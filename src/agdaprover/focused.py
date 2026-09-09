"""Focused, memoized proof synthesis for a certified implicational fragment.

The search constructs beta-normal, eta-long inhabitants of simply typed goals.
It deliberately treats Agda as the authority: this module only proposes a term;
the bridge and fresh-process validator must still accept it.
"""

from __future__ import annotations

import math
import time
from collections.abc import Callable, Generator, Sequence
from dataclasses import dataclass, field
from itertools import product
from typing import Any, Literal, TypeVar

from .contracts import GoalInfo
from .resource_budget import checkpoint
from .terms import Term
from .type_syntax import (
    binder_domains,
    normalize_type_text,
    split_top_level_arrows,
)

FOCUSED_ALGORITHM = "focused-implication-dfs-v1"

_T = TypeVar("_T")


def _drive(work: Generator[Any, Any, _T]) -> _T:
    """Run suspended search frames without consuming the Python call stack.

    Each frame retains its own AND/OR cursor and finally block. Closing the
    stack on interruption unwinds active-sequent bookkeeping in reverse order.
    Scheduling and action charging are otherwise identical to recursive DFS.
    """
    stack = [work]
    answer: Any = None
    try:
        while stack:
            checkpoint()
            try:
                child = stack[-1].send(answer)
            except StopIteration as completed:
                stack.pop()
                answer = completed.value
            else:
                stack.append(child)
                answer = None
        return answer
    finally:
        for frame in reversed(stack):
            frame.close()


@dataclass(frozen=True, eq=False)
class TypeExpr:
    """Small structural type IR used only by the fast search path."""

    tag: Literal["atom", "arrow"]
    atom: str | None = None
    domain: TypeExpr | None = None
    codomain: TypeExpr | None = None
    _hash: int = field(init=False, repr=False)

    def __post_init__(self) -> None:
        if self.tag == "atom":
            if not self.atom or self.domain is not None or self.codomain is not None:
                raise ValueError("malformed atomic type")
        elif self.tag == "arrow":
            if self.atom is not None or self.domain is None or self.codomain is None:
                raise ValueError("malformed arrow type")
        else:
            raise ValueError(f"unsupported type tag: {self.tag!r}")
        object.__setattr__(
            self, "_hash", hash((self.tag, self.atom, self.domain, self.codomain))
        )

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, TypeExpr):
            return NotImplemented
        pending = [(self, other)]
        while pending:
            left, right = pending.pop()
            if left is right:
                continue
            if (
                left._hash != right._hash
                or left.tag != right.tag
                or left.atom != right.atom
            ):
                return False
            if left.tag == "arrow":
                ld, lc = left.arrow_parts()
                rd, rc = right.arrow_parts()
                pending.extend(((ld, rd), (lc, rc)))
        return True

    @staticmethod
    def atomic(text: str) -> TypeExpr:
        normalized = " ".join(text.split())
        if not normalized:
            raise ValueError("empty atomic type")
        return TypeExpr("atom", atom=normalized)

    @staticmethod
    def arrow(domain: TypeExpr, codomain: TypeExpr) -> TypeExpr:
        return TypeExpr("arrow", domain=domain, codomain=codomain)

    @property
    def size(self) -> int:
        total = 0
        pending = [self]
        while pending:
            current = pending.pop()
            total += 1
            if current.tag == "arrow":
                pending.extend(current.arrow_parts())
        return total

    def atom_text(self) -> str:
        if self.tag != "atom" or self.atom is None:
            raise ValueError("expected a well-formed atomic type")
        return self.atom

    def arrow_parts(self) -> tuple[TypeExpr, TypeExpr]:
        if self.tag != "arrow" or self.domain is None or self.codomain is None:
            raise ValueError("expected a well-formed arrow type")
        return self.domain, self.codomain

    def domains_and_result(self) -> tuple[tuple[TypeExpr, ...], TypeExpr]:
        domains: list[TypeExpr] = []
        result = self
        while result.tag == "arrow":
            domain, codomain = result.arrow_parts()
            domains.append(domain)
            result = codomain
        return tuple(domains), result

    def canonical(self) -> str:
        return self._render(" → ", "")

    def shape(self) -> str:
        return self._render("→", "•")

    def _render(self, arrow: str, atom_fallback: str) -> str:
        output: list[str] = []
        pending: list[TypeExpr | str] = [self]
        while pending:
            current = pending.pop()
            if isinstance(current, str):
                output.append(current)
            elif current.tag == "atom":
                output.append(
                    current.atom_text() if not atom_fallback else atom_fallback
                )
            else:
                domain, codomain = current.arrow_parts()
                pending.extend((")", codomain, arrow, domain, "("))
        return "".join(output)


@dataclass(frozen=True)
class Assumption:
    type_expr: TypeExpr
    order: int
    local_name: str | None = None
    binder_level: int | None = None

    def term_at_depth(self, depth: int) -> Term:
        if self.local_name is not None:
            return Term.local(self.local_name)
        if self.binder_level is None or self.binder_level >= depth:
            raise ValueError("introduced assumption escaped its binder")
        return Term.bound(depth - 1 - self.binder_level)

    @property
    def identity(self) -> tuple[object, ...]:
        return (self.type_expr, self.order, self.local_name, self.binder_level)


@dataclass(frozen=True)
class FocusedAction:
    """One non-invertible choice of a hypothesis to focus."""

    assumption: Assumption
    domains: tuple[TypeExpr, ...]
    kernel_observed_eliminator: bool = False

    @property
    def symbolic_key(self) -> tuple[int, int, int]:
        return (
            len(self.domains),
            self.assumption.type_expr.size,
            self.assumption.order,
        )

    def contextual_key(
        self, assumptions: tuple[Assumption, ...]
    ) -> tuple[int, int, int, int, int]:
        """Prefer applications whose arguments are already in the context.

        This is a structural readiness test, not a theorem-specific rule.  It
        prevents a hypothesis such as ``(P → empty) → empty`` from repeatedly
        growing the context when another hypothesis can use the available
        ``P`` and ``Q → empty`` assumptions to close the same goal directly.
        """

        available = {assumption.type_expr for assumption in assumptions}

        def is_ready(domain: TypeExpr) -> bool:
            if domain in available:
                return True
            # Right implication is invertible.  If introducing all of a
            # domain's arguments exposes a result already in the context, the
            # domain has an immediate projection proof as well.
            _domains, result = domain.domains_and_result()
            return result in available

        missing_domains = sum(not is_ready(domain) for domain in self.domains)
        return (
            missing_domains,
            int(self.kernel_observed_eliminator),
            *self.symbolic_key,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "tag": "focus-assumption",
            "assumption_order": self.assumption.order,
            "assumption_type": self.assumption.type_expr.canonical(),
            "domain_types": [domain.canonical() for domain in self.domains],
        }


FocusedBranchScorer = Callable[
    [TypeExpr, tuple[Assumption, ...], Sequence[FocusedAction]], list[float]
]


@dataclass(frozen=True)
class FocusedDecision:
    """A verified-proof training label with only explicitly failed negatives."""

    goal: TypeExpr
    assumptions: tuple[Assumption, ...]
    positive: FocusedAction
    negatives: tuple[FocusedAction, ...]
    candidates: tuple[FocusedAction, ...]
    search_order: tuple[FocusedAction, ...]

    def to_dict(self) -> dict[str, object]:
        return {
            "goal_type": self.goal.canonical(),
            "assumptions": [
                {
                    "order": assumption.order,
                    "type": assumption.type_expr.canonical(),
                }
                for assumption in self.assumptions
            ],
            "positive": self.positive.to_dict(),
            "negatives": [negative.to_dict() for negative in self.negatives],
            "candidate_set": [candidate.to_dict() for candidate in self.candidates],
            "symbolic_order": [
                candidate.assumption.order for candidate in self.candidates
            ],
            "search_order": [
                candidate.assumption.order for candidate in self.search_order
            ],
            "explored_order": [
                candidate.assumption.order
                for candidate in (*self.negatives, self.positive)
            ],
        }


@dataclass
class FocusedStats:
    algorithm: str = FOCUSED_ALGORITHM
    nodes_expanded: int = 0
    actions_considered: int = 0
    actions_generated: int = 0
    cache_hits: int = 0
    cycles_pruned: int = 0
    depth_pruned: int = 0
    depth_limit: int | None = None
    max_depth: int = 0
    memo_entries: int = 0
    proof_size: int | None = None
    policy_nodes: int = 0
    model_calls: int = 0
    model_elapsed_ms: float = 0.0
    symbolic_fallbacks: int = 0
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict[str, object]:
        return {
            "algorithm": self.algorithm,
            "nodes_expanded": self.nodes_expanded,
            "actions_considered": self.actions_considered,
            "actions_generated": self.actions_generated,
            "cache_hits": self.cache_hits,
            "cycles_pruned": self.cycles_pruned,
            "depth_pruned": self.depth_pruned,
            "depth_limit": self.depth_limit,
            "max_depth": self.max_depth,
            "memo_entries": self.memo_entries,
            "proof_size": self.proof_size,
            "policy_nodes": self.policy_nodes,
            "model_calls": self.model_calls,
            "model_elapsed_ms": self.model_elapsed_ms,
            "symbolic_fallbacks": self.symbolic_fallbacks,
            "elapsed_ms": self.elapsed_ms,
        }


@dataclass(frozen=True)
class FocusedResult:
    status: Literal["solved", "no-proof", "resource-exhausted", "unsupported"]
    term: Term | None
    stats: FocusedStats
    diagnostic: str = ""
    decisions: tuple[FocusedDecision, ...] = ()
    exhaustion_kind: Literal["action-budget", "wall-time", "depth"] | None = None


@dataclass(frozen=True)
class FocusedCandidatesResult:
    """Bounded alternative inhabitants for a search controller that backtracks."""

    status: Literal["solved", "no-proof", "resource-exhausted", "unsupported"]
    terms: tuple[Term, ...]
    stats: FocusedStats
    diagnostic: str = ""
    exhaustion_kind: Literal["action-budget", "wall-time", "depth"] | None = None


@dataclass
class _Search:
    action_budget: int
    deadline: float
    eliminators: tuple[tuple[str, tuple[TypeExpr, ...]], ...] = ()
    max_search_depth: int | None = None
    stats: FocusedStats = field(default_factory=FocusedStats)
    branch_scorer: FocusedBranchScorer | None = None
    memo: dict[tuple[object, ...], Term | None] = field(default_factory=dict)
    active: set[tuple[object, ...]] = field(default_factory=set)
    decisions: list[FocusedDecision] = field(default_factory=list)
    hard_exhaustion: Literal["action-budget", "wall-time"] | None = None
    saw_depth_prune: bool = False

    def _charge(self) -> bool:
        if time.monotonic() >= self.deadline:
            self.hard_exhaustion = "wall-time"
            return False
        if self.stats.actions_considered >= self.action_budget:
            self.hard_exhaustion = "action-budget"
            return False
        self.stats.actions_considered += 1
        return True

    def solve(
        self,
        assumptions: tuple[Assumption, ...],
        goal: TypeExpr,
        binder_depth: int,
        search_depth: int,
    ) -> Term | None:
        return _drive(self._solve(assumptions, goal, binder_depth, search_depth))

    def _solve(
        self,
        assumptions: tuple[Assumption, ...],
        goal: TypeExpr,
        binder_depth: int,
        search_depth: int,
    ) -> Generator[Any, Any, Term | None]:
        if self.hard_exhaustion is not None:
            return None
        if time.monotonic() >= self.deadline:
            self.hard_exhaustion = "wall-time"
            return None
        if self.max_search_depth is not None and search_depth > self.max_search_depth:
            self.stats.depth_pruned += 1
            self.saw_depth_prune = True
            return None
        self.stats.max_depth = max(self.stats.max_depth, search_depth)
        sequent_key = (
            tuple(assumption.identity for assumption in assumptions),
            goal,
            binder_depth,
        )
        memo_key = (
            *sequent_key,
            None
            if self.max_search_depth is None
            else self.max_search_depth - search_depth,
        )
        if memo_key in self.memo:
            self.stats.cache_hits += 1
            return self.memo[memo_key]
        if sequent_key in self.active:
            self.stats.cycles_pruned += 1
            return None

        self.stats.nodes_expanded += 1
        depth_prunes_before = self.stats.depth_pruned
        self.active.add(sequent_key)
        try:
            # An exact hypothesis closes immediately and is the cheapest proof.
            for assumption in assumptions:
                if assumption.type_expr == goal:
                    self.stats.actions_generated += 1
                    if not self._charge():
                        return None
                    answer = assumption.term_at_depth(binder_depth)
                    self.memo[memo_key] = answer
                    return answer

            # Right implication is invertible: introduce it before branching.
            if goal.tag == "arrow":
                self.stats.actions_generated += 1
                if not self._charge():
                    return None
                domain, codomain = goal.arrow_parts()
                introduced = Assumption(
                    type_expr=domain,
                    order=len(assumptions),
                    binder_level=binder_depth,
                )
                body = yield self._solve(
                    assumptions + (introduced,),
                    codomain,
                    binder_depth + 1,
                    search_depth + 1,
                )
                if body is not None:
                    answer = Term.lam(body)
                    self.memo[memo_key] = answer
                    return answer
                if self.hard_exhaustion is not None:
                    return None

            # Focus each usable assumption.  An application is an AND edge: all
            # argument goals must be solved before the candidate exists.
            applicable: list[FocusedAction] = []
            for assumption in assumptions:
                domains, result = assumption.type_expr.domains_and_result()
                if domains and result == goal:
                    applicable.append(FocusedAction(assumption, domains))
            for offset, (name, domains) in enumerate(self.eliminators):
                instantiated = goal
                for domain in reversed(domains):
                    instantiated = TypeExpr.arrow(domain, instantiated)
                applicable.append(
                    FocusedAction(
                        Assumption(
                            type_expr=instantiated,
                            order=len(assumptions) + offset,
                            local_name=name,
                        ),
                        domains,
                        True,
                    )
                )
            applicable.sort(key=lambda action: action.contextual_key(assumptions))
            self.stats.actions_generated += len(applicable)
            symbolic_actions = tuple(applicable)

            if self.branch_scorer is not None and len(applicable) > 1:
                policy_started = time.monotonic()
                try:
                    scores = self.branch_scorer(goal, assumptions, applicable)
                    if len(scores) != len(applicable) or not all(
                        isinstance(score, (int, float)) and math.isfinite(float(score))
                        for score in scores
                    ):
                        raise ValueError("focused policy returned malformed scores")
                    scored = list(zip(applicable, scores, strict=True))
                    applicable = [
                        action
                        for action, _score in sorted(
                            scored,
                            key=lambda item: (
                                -float(item[1]),
                                item[0].contextual_key(assumptions),
                            ),
                        )
                    ]
                    self.stats.policy_nodes += 1
                    self.stats.model_calls += len(applicable)
                except (ArithmeticError, ValueError):
                    self.stats.symbolic_fallbacks += 1
                    applicable.sort(
                        key=lambda action: action.contextual_key(assumptions)
                    )
                finally:
                    self.stats.model_elapsed_ms += (
                        time.monotonic() - policy_started
                    ) * 1000.0

            failed_actions: list[FocusedAction] = []
            for action in applicable:
                if not self._charge():
                    return None
                decision_checkpoint = len(self.decisions)
                candidate = action.assumption.term_at_depth(binder_depth)
                viable = True
                for domain in action.domains:
                    argument = yield self._solve(
                        assumptions, domain, binder_depth, search_depth + 1
                    )
                    if argument is None:
                        viable = False
                        break
                    candidate = Term.app(candidate, argument)
                if viable:
                    if failed_actions:
                        self.decisions.append(
                            FocusedDecision(
                                goal=goal,
                                assumptions=assumptions,
                                positive=action,
                                negatives=tuple(failed_actions),
                                candidates=symbolic_actions,
                                search_order=tuple(applicable),
                            )
                        )
                    self.memo[memo_key] = candidate
                    return candidate
                del self.decisions[decision_checkpoint:]
                failed_actions.append(action)
                if self.hard_exhaustion is not None:
                    return None

            # A depth-censored subtree is unknown at this bound, not a proof of
            # failure.  Do not let it poison another path through the memo.
            if self.stats.depth_pruned == depth_prunes_before:
                self.memo[memo_key] = None
            return None
        finally:
            self.active.discard(sequent_key)


@dataclass
class _EnumerationSearch:
    """Enumerate canonical focused proofs for joint source-state search.

    The ordinary fast path deliberately returns the first inhabitant.  A joint
    search cannot make that commitment: a later declaration may reject an
    earlier, locally valid choice.  This controller therefore retains bounded
    OR alternatives and bounded Cartesian products at AND nodes.
    """

    action_budget: int
    solution_limit: int
    deadline: float
    eliminators: tuple[tuple[str, tuple[TypeExpr, ...]], ...] = ()
    max_search_depth: int | None = None
    batch_invertible: bool = False
    stats: FocusedStats = field(default_factory=FocusedStats)
    branch_scorer: FocusedBranchScorer | None = None
    memo: dict[tuple[object, ...], tuple[Term, ...]] = field(default_factory=dict)
    active: set[tuple[object, ...]] = field(default_factory=set)
    hard_exhaustion: Literal["action-budget", "wall-time"] | None = None
    saw_depth_prune: bool = False

    def _charge(self) -> bool:
        if time.monotonic() >= self.deadline:
            self.hard_exhaustion = "wall-time"
            return False
        if self.stats.actions_considered >= self.action_budget:
            self.hard_exhaustion = "action-budget"
            return False
        self.stats.actions_considered += 1
        return True

    def _ordered_actions(
        self,
        goal: TypeExpr,
        assumptions: tuple[Assumption, ...],
        actions: list[FocusedAction],
    ) -> list[FocusedAction]:
        actions.sort(key=lambda action: action.contextual_key(assumptions))
        if self.branch_scorer is None or len(actions) <= 1:
            return actions
        policy_started = time.monotonic()
        try:
            scores = self.branch_scorer(goal, assumptions, actions)
            if len(scores) != len(actions) or not all(
                isinstance(score, (int, float)) and math.isfinite(float(score))
                for score in scores
            ):
                raise ValueError("focused policy returned malformed scores")
            self.stats.policy_nodes += 1
            self.stats.model_calls += len(actions)
            return [
                action
                for action, _score in sorted(
                    zip(actions, scores, strict=True),
                    key=lambda item: (
                        -float(item[1]),
                        item[0].contextual_key(assumptions),
                    ),
                )
            ]
        except (ArithmeticError, ValueError):
            self.stats.symbolic_fallbacks += 1
            return sorted(
                actions, key=lambda action: action.contextual_key(assumptions)
            )
        finally:
            self.stats.model_elapsed_ms += (time.monotonic() - policy_started) * 1000.0

    def solve(
        self,
        assumptions: tuple[Assumption, ...],
        goal: TypeExpr,
        binder_depth: int,
        search_depth: int,
    ) -> tuple[Term, ...]:
        return _drive(self._solve(assumptions, goal, binder_depth, search_depth))

    def _solve(
        self,
        assumptions: tuple[Assumption, ...],
        goal: TypeExpr,
        binder_depth: int,
        search_depth: int,
    ) -> Generator[Any, Any, tuple[Term, ...]]:
        if self.hard_exhaustion is not None:
            return ()
        if time.monotonic() >= self.deadline:
            self.hard_exhaustion = "wall-time"
            return ()
        if self.max_search_depth is not None and search_depth > self.max_search_depth:
            self.stats.depth_pruned += 1
            self.saw_depth_prune = True
            return ()
        self.stats.max_depth = max(self.stats.max_depth, search_depth)
        sequent_key = (
            tuple(assumption.identity for assumption in assumptions),
            goal,
            binder_depth,
        )
        memo_key = (
            *sequent_key,
            None
            if self.max_search_depth is None
            else self.max_search_depth - search_depth,
        )
        if memo_key in self.memo:
            self.stats.cache_hits += 1
            return self.memo[memo_key]
        if sequent_key in self.active:
            self.stats.cycles_pruned += 1
            return ()

        self.stats.nodes_expanded += 1
        self.active.add(sequent_key)
        results: list[Term] = []
        seen: set[Term] = set()

        def retain(candidate: Term) -> None:
            if candidate not in seen and len(results) < self.solution_limit:
                seen.add(candidate)
                results.append(candidate)

        try:
            # Right implication is invertible, so every canonical inhabitant
            # introduces the binder before making an OR choice.
            if goal.tag == "arrow":
                self.stats.actions_generated += 1
                if not self._charge():
                    return ()
                if self.batch_invertible:
                    domains, codomain = goal.domains_and_result()
                else:
                    domain, codomain = goal.arrow_parts()
                    domains = (domain,)
                introduced = tuple(
                    Assumption(
                        type_expr=domain,
                        order=len(assumptions) + offset,
                        binder_level=binder_depth + offset,
                    )
                    for offset, domain in enumerate(domains)
                )
                bodies = yield self._solve(
                    assumptions + introduced,
                    codomain,
                    binder_depth + len(domains),
                    search_depth + 1,
                )
                for body in bodies:
                    candidate = body
                    for _domain in reversed(domains):
                        candidate = Term.lam(candidate)
                    retain(candidate)
                answer = tuple(results)
                if self.hard_exhaustion is None and not self.saw_depth_prune:
                    self.memo[memo_key] = answer
                return answer

            # Exact hypotheses are genuine alternatives in joint mode.  Model
            # them as zero-argument focus actions so the same NNUE head can
            # choose which locally valid definition to explore first.
            exact_actions = [
                FocusedAction(assumption, ())
                for assumption in assumptions
                if assumption.type_expr == goal
            ]
            self.stats.actions_generated += len(exact_actions)
            for action in self._ordered_actions(goal, assumptions, exact_actions):
                if len(results) >= self.solution_limit or not self._charge():
                    break
                retain(action.assumption.term_at_depth(binder_depth))

            applicable: list[FocusedAction] = []
            for assumption in assumptions:
                domains, result = assumption.type_expr.domains_and_result()
                if domains and result == goal:
                    applicable.append(FocusedAction(assumption, domains))
            for offset, (name, domains) in enumerate(self.eliminators):
                instantiated = goal
                for domain in reversed(domains):
                    instantiated = TypeExpr.arrow(domain, instantiated)
                applicable.append(
                    FocusedAction(
                        Assumption(
                            type_expr=instantiated,
                            order=len(assumptions) + offset,
                            local_name=name,
                        ),
                        domains,
                        True,
                    )
                )
            self.stats.actions_generated += len(applicable)
            for action in self._ordered_actions(goal, assumptions, applicable):
                if len(results) >= self.solution_limit or not self._charge():
                    break
                argument_sets: list[tuple[Term, ...]] = []
                for domain in action.domains:
                    arguments = yield self._solve(
                        assumptions, domain, binder_depth, search_depth + 1
                    )
                    if not arguments:
                        argument_sets = []
                        break
                    argument_sets.append(arguments)
                if not argument_sets:
                    continue
                for arguments in product(*argument_sets):
                    if time.monotonic() >= self.deadline:
                        self.hard_exhaustion = "wall-time"
                        break
                    candidate = action.assumption.term_at_depth(binder_depth)
                    for argument in arguments:
                        candidate = Term.app(candidate, argument)
                    retain(candidate)
                    if len(results) >= self.solution_limit:
                        break

            answer = tuple(results)
            if self.hard_exhaustion is None and not self.saw_depth_prune:
                self.memo[memo_key] = answer
            return answer
        finally:
            self.active.discard(sequent_key)


def parse_type(type_text: str) -> TypeExpr:
    """Parse top-level arrows while keeping other Agda syntax opaque.

    A parenthesized named binder such as ``(x : A) → B`` contributes type
    ``A``.  Dependency in ``B`` is not interpreted; unsupported proposals are
    rejected later by Agda, preserving soundness.
    """

    work: list[tuple[str, str | int]] = [("parse", type_text)]
    values: list[TypeExpr] = []
    while work:
        operation, payload = work.pop()
        if operation == "combine":
            count = int(payload)
            components = values[-count:]
            del values[-count:]
            result = components[-1]
            for domain in reversed(components[:-1]):
                result = TypeExpr.arrow(domain, result)
            values.append(result)
            continue
        text = str(payload)
        parts = split_top_level_arrows(text)
        if len(parts) == 1:
            values.append(TypeExpr.atomic(normalize_type_text(parts[0])))
            continue
        parse_parts = [
            *(domain for part in parts[:-1] for domain in binder_domains(part)),
            parts[-1],
        ]
        work.append(("combine", len(parse_parts)))
        for part in reversed(parse_parts):
            work.append(("parse", part))
    if len(values) != 1:
        raise ValueError("malformed type syntax")
    return values[0]


def focused_prove(
    goal: GoalInfo,
    *,
    action_budget: int,
    timeout_seconds: float,
    max_depth: int | None = None,
    branch_scorer: FocusedBranchScorer | None = None,
    eliminators: Sequence[tuple[str, Sequence[str]]] = (),
) -> FocusedResult:
    """Synthesize one focused candidate without invoking Agda per search node."""

    started = time.monotonic()
    stats = FocusedStats(depth_limit=max_depth)
    try:
        target = parse_type(goal.target)
        assumptions = tuple(
            Assumption(
                type_expr=parse_type(entry.type),
                order=order,
                local_name=entry.name,
            )
            for order, entry in enumerate(goal.context)
            if entry.in_scope and entry.name
        )
        parsed_eliminators = tuple(
            (name, tuple(parse_type(domain) for domain in domains))
            for name, domains in eliminators
        )
    except ValueError as error:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return FocusedResult("unsupported", None, stats, str(error))

    search = _Search(
        action_budget=action_budget,
        deadline=started + timeout_seconds,
        eliminators=parsed_eliminators,
        max_search_depth=max_depth,
        stats=stats,
        branch_scorer=branch_scorer,
    )
    term = search.solve(assumptions, target, 0, 0)
    stats.memo_entries = len(search.memo)
    stats.proof_size = term.size if term is not None else None
    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
    if term is not None:
        return FocusedResult("solved", term, stats, decisions=tuple(search.decisions))
    if search.hard_exhaustion is not None:
        return FocusedResult(
            "resource-exhausted",
            None,
            stats,
            f"focused {search.hard_exhaustion} exhausted",
            tuple(search.decisions),
            search.hard_exhaustion,
        )
    if search.saw_depth_prune:
        return FocusedResult(
            "resource-exhausted",
            None,
            stats,
            "focused depth limit censored all remaining proof paths",
            tuple(search.decisions),
            "depth",
        )
    return FocusedResult("no-proof", None, stats, decisions=tuple(search.decisions))


def focused_candidates(
    goal: GoalInfo,
    *,
    action_budget: int,
    solution_limit: int,
    timeout_seconds: float,
    max_depth: int | None = None,
    branch_scorer: FocusedBranchScorer | None = None,
    batch_invertible: bool = False,
    eliminators: Sequence[tuple[str, Sequence[str]]] = (),
) -> FocusedCandidatesResult:
    """Enumerate bounded focused inhabitants for a backtracking controller."""

    started = time.monotonic()
    stats = FocusedStats(depth_limit=max_depth)
    if action_budget <= 0 or solution_limit <= 0 or timeout_seconds <= 0:
        return FocusedCandidatesResult(
            "resource-exhausted",
            (),
            stats,
            "focused alternative budget exhausted",
            "action-budget"
            if action_budget <= 0 or solution_limit <= 0
            else "wall-time",
        )
    try:
        target = parse_type(goal.target)
        assumptions = tuple(
            Assumption(
                type_expr=parse_type(entry.type),
                order=order,
                local_name=entry.name,
            )
            for order, entry in enumerate(goal.context)
            if entry.in_scope and entry.name
        )
        parsed_eliminators = tuple(
            (name, tuple(parse_type(domain) for domain in domains))
            for name, domains in eliminators
        )
    except ValueError as error:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return FocusedCandidatesResult("unsupported", (), stats, str(error))

    search = _EnumerationSearch(
        action_budget=action_budget,
        solution_limit=solution_limit,
        deadline=started + timeout_seconds,
        eliminators=parsed_eliminators,
        max_search_depth=max_depth,
        stats=stats,
        branch_scorer=branch_scorer,
        batch_invertible=batch_invertible,
    )
    terms = search.solve(assumptions, target, 0, 0)
    stats.memo_entries = len(search.memo)
    stats.proof_size = min((term.size for term in terms), default=None)
    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
    if search.hard_exhaustion is not None:
        return FocusedCandidatesResult(
            "resource-exhausted",
            terms,
            stats,
            f"focused {search.hard_exhaustion} exhausted",
            search.hard_exhaustion,
        )
    if search.saw_depth_prune:
        return FocusedCandidatesResult(
            "resource-exhausted",
            terms,
            stats,
            "focused depth limit censored remaining proof paths",
            "depth",
        )
    return FocusedCandidatesResult("solved" if terms else "no-proof", terms, stats)


def focused_state_feature_tokens(
    goal: TypeExpr, assumptions: tuple[Assumption, ...]
) -> tuple[str, ...]:
    """Sparse, mostly alpha-invariant policy features for one OR node."""

    producers = 0
    exact = 0
    for assumption in assumptions:
        domains, result = assumption.type_expr.domains_and_result()
        producers += int(bool(domains) and result == goal)
        exact += int(assumption.type_expr == goal)
    atom = goal.atom if goal.tag == "atom" else "function"
    return (
        "policy:focused-v2",
        f"goal-shape:{goal.shape()}",
        f"goal-symbol:{atom}",
        f"goal-size:{_size_bucket(goal.size)}",
        f"assumptions:{_count_bucket(len(assumptions))}",
        f"exact-assumptions:{_count_bucket(exact)}",
        f"producer-count:{_count_bucket(producers)}",
    )


def focused_action_feature_tokens(
    goal: TypeExpr,
    assumptions: tuple[Assumption, ...],
    action: FocusedAction,
) -> tuple[str, ...]:
    """Features describing estimated cost and connectivity of a focus edge."""

    available = {assumption.type_expr for assumption in assumptions}
    producer_results = [
        assumption.type_expr.domains_and_result()[1] for assumption in assumptions
    ]
    direct = sum(domain in available for domain in action.domains)
    producible = sum(domain in producer_results for domain in action.domains)
    duplicates = len(action.domains) - len(set(action.domains))
    recursive = sum(domain == goal for domain in action.domains)
    domain_shape = ",".join(domain.shape() for domain in action.domains)
    return (
        "action:focus-assumption",
        f"action-arity:{_count_bucket(len(action.domains))}",
        f"action-type-size:{_size_bucket(action.assumption.type_expr.size)}",
        f"action-domain-shapes:{domain_shape}",
        f"action-direct-domains:{_count_bucket(direct)}",
        f"action-producible-domains:{_count_bucket(producible)}",
        f"action-duplicate-domains:{_count_bucket(duplicates)}",
        f"action-recursive-domains:{_count_bucket(recursive)}",
        f"action-order:{_count_bucket(action.assumption.order)}",
        f"joint:goal={goal.shape()}:domains={domain_shape}",
        f"joint:arity={len(action.domains)}:direct={direct}:producible={producible}",
    )


def _count_bucket(value: int) -> str:
    for boundary in (0, 1, 2, 3, 4, 8, 16):
        if value <= boundary:
            return str(boundary)
    return "large"


def _size_bucket(value: int) -> str:
    for boundary in (1, 3, 5, 8, 13, 21, 34):
        if value <= boundary:
            return str(boundary)
    return "large"
