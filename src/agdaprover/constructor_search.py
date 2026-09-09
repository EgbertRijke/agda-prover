"""Transactional, kernel-guided synthesis of structural proof trees.

Agda's intro tactic owns constructor applicability: its coverage checker
filters indexed constructors using the current goal and unification state.
This module orders genuine alternatives and recursively discharges constructor
or visible-premise telescopes, retaining Agda as the authority at every
transition.
"""

from __future__ import annotations

import json
import math
import os
import re
import time
from collections.abc import Iterator
from dataclasses import dataclass, field, replace
from typing import Literal

from .bridge.contracts import StateToken
from .contracts import ContextEntry, GoalInfo
from .dependency_planner import goal_has_concrete_nullary_scrutinee
from .focused import FocusedCandidatesResult, focused_candidates, parse_type
from .kernel.protocol import (
    CommittedProofAction,
    InternalObligationSession,
    PreciseSearchGoalSession,
    ScopeDeclarationSession,
    ScopedRetrievalSession,
    TermInferenceSession,
    TransactionalKernelSession,
)
from .notation import render_application, strip_outer_parentheses
from .or_policy import ORPolicyRouter, policy_candidate
from .premise_search import (
    ScopePremiseAction,
    premise_eliminator_source_domains,
    premise_expected_arguments,
    premise_has_shallow_support,
    premise_independent_result_domains,
    premise_inferred_application,
    premise_result_application,
    premise_result_bindings_consistent,
    premise_result_overlap,
    premise_result_prefix_application,
    premise_result_prefix_priority,
    premise_static_priority,
    premise_structured_result_domains,
    premise_type_pattern_matches,
    rank_scope_premises,
    scoped_premise_actions,
    scoped_premise_admission,
    shallow_composition_actions,
)
from .ranking.protocol import SparsePolicyRanker
from .reasoning.classifications import (
    classify_structural_scheduling,
    has_relational_context_evidence,
    is_reflexive_relation_target,
)
from .recursive_calls import (
    RecursiveCallAction,
    RecursiveCallSpec,
    RecursiveCallStats,
    generate_recursive_call_actions,
    generate_recursive_compositions,
)
from .relation_path import (
    RelationHead,
    explicit_arity,
    parse_relation,
    solve_relation_path,
)
from .retrieval import (
    PROGRESSIVE_POLICY,
    RetrievalResult,
    ScopedPremises,
    SymbolicPremiseIndex,
)
from .retrieval_stats import ScopedRetrievalStats
from .scope_catalog import visible_scope_declarations
from .search_frontier import BatchedFrontier
from .terms import render_term
from .type_syntax import (
    binder_domains,
    normalize_type_text,
    result_head,
    split_adjacent_binders,
    split_top_level_application,
    split_top_level_arrows,
    top_level_arrow_count,
)

CONSTRUCTOR_ALGORITHM = "kernel-guided-structural-tree-v2"
_HOLE = re.compile(r"(?<![\w?])\?(?![\w?])")
_LAMBDA = re.compile(r"^\s*λ\s+(.+?)\s+→\s+\?\s*$")
_ATOMIC_TERM = re.compile(r"[^\s(),{}]+")
_INTERNAL_META = re.compile(r"_[^\s(){}]+_\d+")
_MAX_RECORDED_PREMISE_ATTEMPTS = 64
_MAX_RECORDED_SKELETON_ATTEMPTS = 64
_SCOPE_PREMISE_QUERY_LIMIT = 128
_PREMISE_BRANCH_QUERY_SLICE = 32
_SKELETON_HEAD_LIMIT = 12
_SKELETON_QUERY_LIMIT = 64


@dataclass(frozen=True)
class _ScopedActions:
    ranking: RetrievalResult
    entries: tuple[tuple[int, ScopePremiseAction], ...]
    serialized_bytes: int
    admission_order: tuple[int, ...]

    def through(self, limit: int) -> tuple[ScopePremiseAction, ...]:
        admitted = frozenset(self.admission_order[:limit])
        return tuple(action for rank, action in self.entries if rank in admitted)

    def metadata(
        self, limit: int
    ) -> dict[ScopePremiseAction, tuple[tuple[str, str], ...]]:
        admission_ranks = {
            rank: position for position, rank in enumerate(self.admission_order, 1)
        }
        return {
            action: (
                ("retrieval-policy", PROGRESSIVE_POLICY),
                ("retrieval-limit", str(limit)),
                ("retrieval-rank", str(rank)),
                ("retrieval-admission-rank", str(admission_ranks[rank])),
                ("retrieval-head-match", str(self.ranking.items[rank - 1].head_match)),
                (
                    "retrieval-shallow-support",
                    "yes" if premise_has_shallow_support(action.type_text) else "no",
                ),
                (
                    "retrieval-symbol-overlap",
                    str(self.ranking.items[rank - 1].symbol_overlap),
                ),
                (
                    "retrieval-lexical-overlap",
                    str(self.ranking.items[rank - 1].lexical_overlap),
                ),
                (
                    "retrieval-arity-distance",
                    str(self.ranking.items[rank - 1].arity_distance),
                ),
            )
            + (
                (
                    (
                        "retrieval-dependency-score",
                        str(self.ranking.items[rank - 1].dependency_score),
                    ),
                )
                if self.ranking.dependency_graph_id is not None
                else ()
            )
            + (
                (
                    ("retrieval-ranking-policy", self.ranking.policy),
                    (
                        "retrieval-query-symbol-match",
                        str(self.ranking.items[rank - 1].query_symbol_match),
                    ),
                )
                if self.ranking.query_symbol_lane
                else ()
            )
            for rank, action in self.entries
            if admission_ranks[rank] <= limit
        }


@dataclass
class _SkeletonObservations:
    """Replay observations only for one exact parent and interaction.

    This is local to one widening sequence, never a proof/similarity cache.
    Accepted partial terms still need the ordinary hidden-obligation check.
    """

    state: StateToken
    goal_id: int
    baseline: tuple[int, int] | None = None
    attempts: dict[str, tuple[CommittedProofAction, tuple[int, int] | None]] = field(
        default_factory=dict
    )
    deferred_query_stop: int | None = None


def _canonicalize_internal_metas(text: str) -> str:
    """Erase Agda's allocation-dependent metavariable identifiers.

    Search alternatives that differ only because Agda allocated `_x_251`
    instead of `_x_317` are the same abstract obligation.  Canonicalizing
    them makes cycle detection effective without interpreting any datatype.
    """

    names: dict[str, str] = {}

    def replace(matched: re.Match[str]) -> str:
        name = matched.group(0)
        return names.setdefault(name, f"?m{len(names)}")

    return _INTERNAL_META.sub(replace, " ".join(text.split()))


def _context_type_signature(goal: GoalInfo) -> tuple[str, ...]:
    """Canonical context types for bounded eliminator widening."""

    return tuple(
        sorted(
            {
                _canonicalize_internal_metas(entry.type)
                for entry in goal.context
                if entry.in_scope
            }
        )
    )


@dataclass(frozen=True)
class ProofPlan:
    """A checked introduction template with one plan per explicit hole."""

    template: str
    children: tuple[ProofPlan, ...] = ()
    recursive_call: bool = False

    @property
    def recursive_call_count(self) -> int:
        return int(self.recursive_call) + sum(
            child.recursive_call_count for child in self.children
        )

    def render(self) -> str:
        child_iterator = iter(self.children)

        def replace(_matched: re.Match[str]) -> str:
            try:
                child = next(child_iterator)
            except StopIteration as error:
                raise ValueError("constructor template has too many holes") from error
            rendered_child = child.render()
            return (
                rendered_child
                if _ATOMIC_TERM.fullmatch(rendered_child)
                else f"({rendered_child})"
            )

        rendered = _HOLE.sub(replace, self.template)
        try:
            next(child_iterator)
        except StopIteration:
            return rendered
        raise ValueError("constructor template has too few holes")

    def clause_parts(self) -> tuple[tuple[str, ...], str]:
        """Move only leading checked lambda introductions to the clause head."""

        binders: list[str] = []
        current = self
        while len(current.children) == 1:
            matched = _LAMBDA.fullmatch(current.template)
            if matched is None:
                break
            binders.extend(matched.group(1).split())
            current = current.children[0]
        return tuple(binders), current.render()


@dataclass(frozen=True)
class _PremiseSkeleton:
    """Application tree whose ``None`` leaves are kernel-inferred arguments."""

    head: str
    children: tuple[_PremiseSkeleton | None, ...]

    @property
    def node_count(self) -> int:
        return 1 + sum(child.node_count for child in self.children if child is not None)

    @property
    def hole_count(self) -> int:
        return sum(1 if child is None else child.hole_count for child in self.children)

    @property
    def repetition_count(self) -> int:
        heads = [self.head]

        def collect(node: _PremiseSkeleton) -> None:
            for child in node.children:
                if child is not None:
                    heads.append(child.head)
                    collect(child)

        collect(self)
        return len(heads) - len(set(heads))

    def render(self) -> str:
        return render_application(
            self.head,
            ("_" if child is None else child.render() for child in self.children),
        )

    def fill(
        self, target: tuple[int, ...], replacement: _PremiseSkeleton
    ) -> _PremiseSkeleton:
        if not target:
            raise ValueError("skeleton path cannot replace its root")
        index, *rest = target
        if index < 0 or index >= len(self.children):
            raise ValueError("skeleton path is out of bounds")
        children = list(self.children)
        child = children[index]
        if rest:
            if child is None:
                raise ValueError("skeleton path descends through a hole")
            children[index] = child.fill(tuple(rest), replacement)
        else:
            if child is not None:
                raise ValueError("skeleton path does not select a hole")
            children[index] = replacement
        return _PremiseSkeleton(self.head, tuple(children))

    def hole_paths(self, prefix: tuple[int, ...] = ()) -> tuple[tuple[int, ...], ...]:
        paths: list[tuple[int, ...]] = []
        for index, child in enumerate(self.children):
            path = (*prefix, index)
            if child is None:
                paths.append(path)
            else:
                paths.extend(child.hole_paths(path))
        return tuple(paths)


@dataclass(frozen=True)
class ConstructorSolution:
    state: StateToken
    plan: ProofPlan

    @property
    def proof_text(self) -> str:
        return self.plan.render()


@dataclass
class ConstructorStats(ScopedRetrievalStats):
    algorithm: str = CONSTRUCTOR_ALGORITHM
    states_expanded: int = 0
    goal_inspections: int = 0
    actions_considered: int = 0
    actions_generated: int = 0
    constructor_queries: int = 0
    catalog_queries: int = 0
    premise_catalog_queries: int = 0
    premise_queries: int = 0
    premise_refinement_queries: int = 0
    premise_query_limit: int = _SCOPE_PREMISE_QUERY_LIMIT
    premise_candidates: int = 0
    relation_path: dict[str, object] = field(default_factory=dict)
    premise_attempts: list[dict[str, object]] = field(default_factory=list)
    premise_attempts_omitted: int = 0
    completion_queries: int = 0
    incomplete_solutions_pruned: int = 0
    constructor_branches: int = 0
    deterministic_constructor_introductions: int = 0
    constructor_or_nodes: int = 0
    proof_checks: int = 0
    generated_subgoals: int = 0
    cycles_pruned: int = 0
    depth_pruned: int = 0
    max_depth: int = 0
    skeleton_queries: int = 0
    skeleton_candidates: int = 0
    skeleton_frontier_peak: int = 0
    skeleton_attempts: list[dict[str, object]] = field(default_factory=list)
    skeleton_attempts_omitted: int = 0
    recursive_subject_search_actions: int = 0
    recursive_subject_inference_queries: int = 0
    recursive_subjects_generated: int = 0
    recursive_catalog_queries: int = 0
    recursive_wrappers_generated: int = 0
    recursive_applications_generated: int = 0
    recursive_inference_queries: int = 0
    recursive_applications_inferred: int = 0
    recursive_applications_pruned: int = 0
    recursive_compositions_generated: int = 0
    recursive_composition_inference_queries: int = 0
    recursive_compositions_inferred: int = 0
    recursive_proof_checks: int = 0
    recursive_actions: list[dict[str, object]] = field(default_factory=list)
    local_refinement_candidates: int = 0
    local_refinement_queries: int = 0
    empty_function_queries: int = 0
    empty_function_closures: int = 0
    constructor_orders: list[dict[str, object]] = field(default_factory=list)
    model_calls: int = 0
    model_batches: int = 0
    model_elapsed_ms: float = 0.0
    symbolic_fallbacks: int = 0
    elapsed_ms: float = 0.0
    depth_limit: int | None = None
    focused: dict[str, int | float] = field(default_factory=dict)

    def to_dict(self) -> dict[str, object]:
        return self.stats_dict()


@dataclass(frozen=True)
class ConstructorResult:
    status: Literal["solved", "no-proof", "resource-exhausted", "unsupported"]
    solutions: tuple[ConstructorSolution, ...]
    stats: ConstructorStats
    diagnostic: str = ""


class _ConstructorSearch:
    def __init__(
        self,
        session: TransactionalKernelSession,
        *,
        action_budget: int,
        deadline: float,
        max_depth: int | None,
        solution_limit: int,
        focused_model: SparsePolicyRanker | None,
        refinement_model: SparsePolicyRanker | None,
        policy_router: ORPolicyRouter | None,
        excluded_premises: frozenset[str],
        defer_concrete_premises: bool,
        recursive_call: RecursiveCallSpec | None,
        preferred_constructor_arity: int | None,
        require_recursive_call: bool,
    ) -> None:
        self.session = session
        self.action_budget = action_budget
        self.deadline = deadline
        self.max_depth = max_depth
        self.solution_limit = solution_limit
        self.stats = ConstructorStats(depth_limit=max_depth)
        self.policy_router = policy_router or ORPolicyRouter(
            focused_model=focused_model,
            refinement_model=refinement_model,
        )
        self.focused_policy = self.policy_router.focused_policy
        self.excluded_premises = excluded_premises
        self.defer_concrete_premises = defer_concrete_premises
        self.recursive_call = recursive_call
        self.preferred_constructor_arity = preferred_constructor_arity
        self.require_recursive_call = require_recursive_call
        self._scope_catalog: tuple[tuple[str, str], ...] | None = None
        self._scoped_actions: dict[tuple[StateToken, int], _ScopedActions] = {}
        self._scoped_index_reuse_enabled = (
            os.environ.get("AGDAPROVER_SCOPED_INDEX_REUSE") == "1"
        )
        self._scoped_query_symbol_lane_enabled = (
            os.environ.get("AGDAPROVER_SCOPED_QUERY_SYMBOL_LANE") == "1"
        )
        self._previous_scoped_index: tuple[StateToken, SymbolicPremiseIndex] | None = (
            None
        )
        self._focused_visible_eliminators: tuple[tuple[str, tuple[str, ...]], ...] = ()
        self._has_ready_nonrecursive_eliminators = False
        self._scope_premise_queries = 0
        self._goal_hints: dict[tuple[str, int], str] = {}
        self._recursive_action_cache: dict[
            tuple[str, int], tuple[RecursiveCallAction, ...]
        ] = {}
        self._baseline_internal_obligations = (
            session.internal_obligation_counts(session.current_state())
            if isinstance(session, InternalObligationSession)
            else (0, 0)
        )
        if isinstance(session, InternalObligationSession):
            self.stats.completion_queries += 1
        self.saw_exhaustion = False

    def _record_recursive(self, nested: RecursiveCallStats) -> None:
        self.stats.recursive_subject_search_actions += nested.subject_search_actions
        self.stats.recursive_subject_inference_queries += (
            nested.subject_inference_queries
        )
        self.stats.recursive_subjects_generated += nested.subjects_generated
        self.stats.recursive_catalog_queries += nested.constructor_catalog_queries
        self.stats.recursive_wrappers_generated += nested.constructor_wrappers_generated
        self.stats.recursive_applications_generated += nested.applications_generated
        self.stats.recursive_inference_queries += nested.inference_queries
        self.stats.recursive_applications_inferred += nested.applications_inferred
        self.stats.recursive_applications_pruned += nested.applications_pruned
        self.stats.recursive_compositions_generated += (
            nested.composition_applications_generated
        )
        self.stats.recursive_composition_inference_queries += (
            nested.composition_inference_queries
        )
        self.stats.recursive_compositions_inferred += (
            nested.composition_applications_inferred
        )
        self.stats.actions_considered += (
            nested.subject_search_actions
            + nested.subject_inference_queries
            + nested.inference_queries
            + nested.composition_inference_queries
        )
        self.stats.actions_generated += (
            nested.applications_generated + nested.composition_applications_generated
        )

    def _solve_with_recursive_calls(
        self,
        state: StateToken,
        goal: GoalInfo,
        *,
        deprioritized_terms: frozenset[str] = frozenset(),
    ) -> Iterator[ConstructorSolution]:
        """Try only fully applied, observationally typed recursive calls."""

        if self.recursive_call is None or not isinstance(
            self.session, TermInferenceSession
        ):
            return
        remaining = self.action_budget - self.stats.actions_considered
        if remaining <= 0:
            return
        cache_key = (state.structural_hash, goal.goal_id)
        actions = self._recursive_action_cache.get(cache_key)
        if actions is None:
            actions, recursive_stats = generate_recursive_call_actions(
                self.session,
                state,
                goal,
                self.recursive_call,
                query_budget=remaining,
                deadline=self.deadline,
            )
            self._record_recursive(recursive_stats)
        if (
            cache_key not in self._recursive_action_cache
            and actions
            and isinstance(self.session, ScopeDeclarationSession)
        ):
            if self._scope_catalog is None:
                self._scope_catalog, queries = visible_scope_declarations(
                    self.session, state, goal
                )
                self.stats.premise_catalog_queries += queries
            compositions, composition_stats = generate_recursive_compositions(
                self.session,
                state,
                goal,
                actions,
                self._scope_catalog,
                excluded_names=self.excluded_premises
                | frozenset((self.recursive_call.root_name,)),
                query_budget=max(
                    0,
                    self.action_budget - self.stats.actions_considered,
                ),
                deadline=self.deadline,
            )
            self._record_recursive(composition_stats)
            actions = (*actions, *compositions)
        self._recursive_action_cache[cache_key] = actions

        def sibling_used_subject(action_subject: str) -> bool:
            return any(
                action_subject in expression.replace("(", " ").replace(")", " ").split()
                for expression in deprioritized_terms
            )

        ordered_actions = sorted(
            actions,
            key=lambda action: (
                action.expression in deprioritized_terms
                or sibling_used_subject(action.subject),
                action.subject_origin != "direct-descendant",
                action.expression,
            ),
        )
        actions_by_expression = {
            action.expression: action for action in ordered_actions
        }
        ranked_recursive = self.policy_router.rank(
            goal,
            tuple(
                policy_candidate(
                    family="recursive-call",
                    tag="apply-recursive-definition",
                    expression=action.expression,
                    type_text=action.inferred_type,
                    symbolic_key=(
                        action.expression in deprioritized_terms
                        or sibling_used_subject(action.subject),
                        action.subject_origin != "direct-descendant",
                        action.expression,
                    ),
                    metadata=(("subject-origin", action.subject_origin),),
                )
                for action in ordered_actions
            ),
            classification=classify_structural_scheduling(
                recursive_result_head_matches_goal=any(
                    result_head(action.inferred_type) == result_head(goal.target)
                    for action in ordered_actions
                ),
                structural_descent_available=bool(ordered_actions),
                dependencies_ready=True,
                reflexive_relation_target=is_reflexive_relation_target(goal.target),
                relational_elimination_available=has_relational_context_evidence(
                    goal.target,
                    tuple(
                        entry.type
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    ),
                ),
            ),
        )
        ordered_actions = [
            actions_by_expression[candidate.expression]
            for candidate in ranked_recursive.candidates
        ]
        for action in ordered_actions:
            if len(self.stats.recursive_actions) < 64:
                self.stats.recursive_actions.append(action.to_dict())
            if not self._charge():
                return
            self.policy_router.mark("recursive-call", action.expression)
            checked = self.session.commit_proof_action(
                state,
                kind="give",
                goal_id=goal.goal_id,
                expression=action.expression,
            )
            self.stats.proof_checks += 1
            self.stats.recursive_proof_checks += 1
            if checked.accepted and checked.child_state is not None:
                yield ConstructorSolution(
                    checked.child_state,
                    ProofPlan(action.expression, recursive_call=True),
                )
            else:
                self.policy_router.mark(
                    "recursive-call", action.expression, outcome="invalid"
                )

    def _solve_with_local_refinements(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        *,
        continuation_only: bool | None = None,
        deprioritized_terms: frozenset[str] = frozenset(),
        deprioritized_only: bool | None = None,
    ) -> Iterator[ConstructorSolution]:
        """Refine by a local function so dependent arguments become subgoals."""

        target_head = result_head(goal.target)
        if self._has_ready_nonrecursive_eliminators:
            target_relation = parse_relation(goal.target)

            def continuation_depth(entry: ContextEntry) -> int:
                try:
                    domains = tuple(
                        domain
                        for part in split_top_level_arrows(entry.type)[:-1]
                        for domain in binder_domains(part)
                    )
                except ValueError:
                    return 0
                return sum(top_level_arrow_count(domain) for domain in domains)

            def embedded_function_count(entry: ContextEntry) -> int:
                try:
                    domains = tuple(
                        domain
                        for part in split_top_level_arrows(entry.type)[:-1]
                        for domain in binder_domains(part)
                    )
                except ValueError:
                    return 0
                return sum(domain.count("→") for domain in domains)

            indexed = tuple(
                (index, entry)
                for index, entry in enumerate(goal.context)
                if entry.in_scope
                and entry.name
                and top_level_arrow_count(entry.type)
                and (
                    result_head(entry.type) == target_head
                    or (
                        target_relation is not None
                        and parse_relation(
                            split_top_level_arrows(entry.type)[-1],
                            expected_operator=target_relation.operator,
                        )
                        is not None
                    )
                )
            )
            candidates = tuple(
                entry
                for _index, entry in sorted(
                    (
                        item
                        for item in indexed
                        if continuation_only is None
                        or (continuation_depth(item[1]) > 0) == continuation_only
                    ),
                    key=lambda item: (
                        item[1].name in deprioritized_terms,
                        explicit_arity(item[1].type),
                        -continuation_depth(item[1]),
                        (
                            -embedded_function_count(item[1])
                            if target_relation is None
                            else 0
                        ),
                        -item[0],
                    ),
                )[:16]
            )
            if deprioritized_only is not None:
                candidates = tuple(
                    entry
                    for entry in candidates
                    if (entry.name in deprioritized_terms) == deprioritized_only
                )
        else:
            candidates = tuple(
                sorted(
                    (
                        entry
                        for entry in goal.context
                        if entry.in_scope
                        and entry.name
                        and top_level_arrow_count(entry.type)
                        and result_head(entry.type) == target_head
                    ),
                    key=lambda entry: (explicit_arity(entry.type), entry.name),
                )[:16]
            )
        self.stats.local_refinement_candidates += len(candidates)
        self.stats.actions_generated += len(candidates)
        for entry in candidates:
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=entry.name,
            )
            self.stats.local_refinement_queries += 1
            if checked.accepted:
                yield from self._accepted_introduction(
                    goal,
                    checked,
                    depth,
                    ancestors,
                    premise_query_stop,
                    deprioritized_locals=(
                        deprioritized_terms | frozenset((entry.name,))
                        if self._has_ready_nonrecursive_eliminators
                        else frozenset()
                    ),
                )

    def _solve_with_ready_structured_results(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        deprioritized_locals: frozenset[str] = frozenset(),
        *,
        closure_only: bool = False,
    ) -> Iterator[ConstructorSolution]:
        """Use projections whose structured input is already in context."""

        if closure_only and parse_relation(goal.target) is not None:
            return
        context_heads = {
            result_head(entry.type)
            for entry in goal.context
            if entry.in_scope and entry.name and not top_level_arrow_count(entry.type)
        }
        if not context_heads:
            return
        actions = tuple(
            action
            for action in self._ordered_premise_actions(state, goal)
            if explicit_arity(action.type_text) == 1
            and any(
                result_head(domain) in context_heads
                and "→" not in domain
                and "λ" not in domain
                for domain in premise_structured_result_domains(action.type_text)
            )
        )
        actions = tuple(
            sorted(
                actions,
                key=lambda action: (
                    min(
                        len(normalize_type_text(domain))
                        for domain in premise_structured_result_domains(
                            action.type_text
                        )
                    ),
                    explicit_arity(action.type_text),
                    action.name,
                ),
            )
        )
        distinct_actions: list[ScopePremiseAction] = []
        seen_action_types: set[str] = set()
        for action in actions:
            action_type = normalize_type_text(action.type_text)
            if action_type in seen_action_types:
                continue
            seen_action_types.add(action_type)
            distinct_actions.append(action)
        actions = tuple(distinct_actions)
        self.stats.actions_generated += len(actions)
        self.stats.premise_candidates += len(actions)
        applications_by_action: dict[ScopePremiseAction, tuple[str, ...]] = {}
        bases_by_action: dict[ScopePremiseAction, tuple[str, ...]] = {}
        for action in actions:
            structured_domains = {
                normalize_type_text(domain)
                for domain in premise_structured_result_domains(action.type_text)
            }
            explicit_domains = tuple(
                domain
                for part in split_top_level_arrows(action.type_text)[:-1]
                for group in split_adjacent_binders(part) or (part,)
                if not group.lstrip().startswith(("{", "⦃"))
                for domain in binder_domains(group)
            )
            ready_applications: list[str] = []
            ready_bases: list[str] = []
            for index, domain in enumerate(explicit_domains):
                if normalize_type_text(domain) not in structured_domains:
                    continue
                for entry in goal.context:
                    if not (
                        entry.in_scope
                        and entry.name
                        and not top_level_arrow_count(entry.type)
                        and result_head(entry.type) == result_head(domain)
                    ):
                        continue
                    arguments = ["?"] * len(explicit_domains)
                    arguments[index] = entry.name
                    base = render_application(action.expression, tuple(arguments))
                    ready_bases.append(base)
                    ready_applications.append(base)
                    ready_applications.extend(
                        render_application(argument.name, (base,))
                        for argument in goal.context
                        if argument.in_scope
                        and argument.name
                        and argument.name != entry.name
                        and top_level_arrow_count(argument.type)
                    )
                    ready_applications.extend(
                        render_application(base, (argument.name,))
                        for argument in goal.context
                        if argument.in_scope
                        and argument.name
                        and argument.name != entry.name
                        and top_level_arrow_count(argument.type)
                    )
                    ready_applications.extend(
                        render_application(base, (argument.name,))
                        for argument in goal.context
                        if argument.in_scope
                        and argument.name
                        and argument.name != entry.name
                        and not top_level_arrow_count(argument.type)
                        and not result_head(argument.type).startswith("Set")
                        and result_head(argument.type) != "Level"
                    )
            applications_by_action[action] = tuple(dict.fromkeys(ready_applications))
            bases_by_action[action] = tuple(dict.fromkeys(ready_bases))

        give_attempts: tuple[
            tuple[ScopePremiseAction, Literal["give", "refine"], str], ...
        ] = tuple(
            (action, "give", application)
            for action in actions
            for application in applications_by_action[action]
        )
        refine_attempts: tuple[
            tuple[ScopePremiseAction, Literal["give", "refine"], str], ...
        ] = tuple(
            (action, "refine", base)
            for action in actions
            for base in bases_by_action[action]
        )
        attempts: tuple[tuple[ScopePremiseAction, Literal["give", "refine"], str], ...]
        if closure_only:
            attempts = tuple(
                (action, "refine", base)
                for action in actions
                for base in bases_by_action[action]
            )
        elif self._has_opaque_type_head(goal):
            # On a flexible result, check every concrete leaf before allowing
            # a projection head to invent an underconstrained record input.
            attempts = (*give_attempts, *refine_attempts)
        else:
            # A rigid result constrains projection refinement.  Keep each
            # projection refinement and its shallow leaves adjacent, with the
            # refinement first.  A projection often exposes a continuation;
            # probing every possible composition before that structural fact
            # is known is needlessly quadratic in the local context.
            interleaved_attempts: list[
                tuple[ScopePremiseAction, Literal["give", "refine"], str]
            ] = []
            for action in actions:
                interleaved_attempts.extend(
                    (action, "refine", base) for base in bases_by_action[action]
                )
                interleaved_attempts.extend(
                    (action, "give", application)
                    for application in applications_by_action[action]
                )
            attempts = tuple(interleaved_attempts)

        for _action, kind, expression in attempts:
            if self._scope_premise_queries >= min(
                self.stats.premise_query_limit, premise_query_stop
            ):
                return
            self.stats.actions_generated += 1
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind=kind,
                goal_id=goal.goal_id,
                expression=expression,
            )
            self.stats.premise_queries += 1
            self._scope_premise_queries += 1
            if kind == "refine":
                self.stats.premise_refinement_queries += 1
            if kind == "give":
                self.stats.proof_checks += 1
                if checked.accepted and checked.child_state is not None:
                    yield ConstructorSolution(
                        checked.child_state,
                        ProofPlan(expression),
                    )
            elif checked.accepted:
                if (
                    closure_only
                    and checked.generated_goals
                    and any(
                        not any(
                            entry.in_scope
                            and entry.name
                            and normalize_type_text(strip_outer_parentheses(entry.type))
                            == normalize_type_text(
                                strip_outer_parentheses(child.target)
                            )
                            for entry in goal.context
                        )
                        for child in checked.generated_goals
                    )
                ):
                    continue
                yield from self._accepted_introduction(
                    goal,
                    checked,
                    depth,
                    ancestors,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                )

    def _solve_with_ready_eliminators(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        deprioritized_locals: frozenset[str] = frozenset(),
    ) -> Iterator[ConstructorSolution]:
        """Apply a polymorphic eliminator to an available concrete source."""

        if parse_relation(goal.target) is not None:
            return
        source_entries = tuple(
            entry
            for entry in goal.context
            if entry.in_scope
            and entry.name
            and not top_level_arrow_count(entry.type)
            and not result_head(entry.type).startswith("Set")
            and result_head(entry.type) != "Level"
        )
        if not source_entries:
            return
        attempts: list[tuple[int, str]] = []
        for action in self._ordered_premise_actions(state, goal):
            source_domains = {
                normalize_type_text(domain)
                for domain in premise_eliminator_source_domains(action.type_text)
            }
            if not source_domains or (
                explicit_arity(action.type_text) == 1
                and premise_structured_result_domains(action.type_text)
            ):
                continue
            explicit_domains = tuple(
                domain
                for part in split_top_level_arrows(action.type_text)[:-1]
                for group in split_adjacent_binders(part) or (part,)
                if not group.lstrip().startswith(("{", "⦃"))
                for domain in binder_domains(group)
            )
            for index, domain in enumerate(explicit_domains):
                if normalize_type_text(domain) not in source_domains:
                    continue
                for entry in source_entries:
                    if not premise_type_pattern_matches(
                        action.type_text,
                        domain,
                        entry.type,
                    ):
                        continue
                    # Question-mark arguments become interaction goals in the
                    # committed Agda state.  Underscores would instead create
                    # hidden metas, producing an apparently closed action that
                    # can only be rejected much later by the completion gate.
                    arguments = ["?"] * len(explicit_domains)
                    arguments[index] = entry.name
                    attempts.append(
                        (
                            len(explicit_domains),
                            render_application(action.expression, tuple(arguments)),
                        )
                    )

        # A nondependent recursor and its dependent eliminator can expose the
        # same source type.  The shorter telescope is the strictly smaller
        # search branch, while Agda still decides whether it is applicable.
        attempts = sorted(set(attempts))
        self.stats.actions_generated += len(attempts)
        self.stats.premise_candidates += len(attempts)
        for _arity, expression in attempts:
            if self._scope_premise_queries >= min(
                self.stats.premise_query_limit, premise_query_stop
            ):
                return
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=expression,
            )
            self.stats.premise_queries += 1
            self.stats.premise_refinement_queries += 1
            self._scope_premise_queries += 1
            if checked.accepted:
                yield from self._accepted_introduction(
                    goal,
                    checked,
                    depth,
                    ancestors,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                )

    def _available(self) -> bool:
        if time.monotonic() >= self.deadline:
            self.saw_exhaustion = True
            return False
        if self.stats.actions_considered >= self.action_budget:
            self.saw_exhaustion = True
            return False
        return True

    def _charge(self) -> bool:
        if not self._available():
            return False
        self.stats.actions_considered += 1
        return True

    def _goal(self, state: StateToken, goal_id: int) -> GoalInfo | None:
        self.stats.goal_inspections += 1
        if isinstance(self.session, PreciseSearchGoalSession):
            goal = self.session.inspect_search_goal(state, goal_id=goal_id)
        else:
            goal = next(
                (
                    goal
                    for goal in self.session.inspect_state(state)
                    if goal.goal_id == goal_id
                ),
                None,
            )
        hint = self._goal_hints.get((state.structural_hash, goal_id))
        if (
            goal is not None
            and hint is not None
            and len(_INTERNAL_META.findall(hint))
            < len(_INTERNAL_META.findall(goal.target))
        ):
            return replace(goal, target=hint)
        return goal

    def _record_focused(self, result: FocusedCandidatesResult) -> None:
        focused_stats = result.stats
        self.stats.actions_considered += focused_stats.actions_considered
        self.stats.actions_generated += focused_stats.actions_generated
        self.stats.model_calls += focused_stats.model_calls
        self.stats.model_batches += focused_stats.policy_nodes
        self.stats.model_elapsed_ms += focused_stats.model_elapsed_ms
        self.stats.symbolic_fallbacks += focused_stats.symbolic_fallbacks
        for name in (
            "nodes_expanded",
            "cache_hits",
            "cycles_pruned",
            "depth_pruned",
        ):
            self.stats.focused[name] = int(self.stats.focused.get(name, 0)) + int(
                getattr(focused_stats, name)
            )

    def _ordered_constructors(
        self,
        goal: GoalInfo,
        names: tuple[str, ...],
        constructor_types: dict[str, str],
    ) -> tuple[str, ...]:
        def structural_key(name: str) -> tuple[int, str]:
            if self.preferred_constructor_arity is None:
                return (0, name)
            type_text = constructor_types.get(name)
            if type_text is None:
                return (1_000_000, name)
            return (
                abs(explicit_arity(type_text) - self.preferred_constructor_arity),
                name,
            )

        ordered = tuple(sorted(dict.fromkeys(names), key=structural_key))
        if len(self.stats.constructor_orders) < 64:
            self.stats.constructor_orders.append(
                {
                    "target": goal.target,
                    "preferred_arity": self.preferred_constructor_arity,
                    "constructors": list(ordered),
                }
            )
        candidates = tuple(
            policy_candidate(
                family="constructor-choice",
                tag="select-constructor",
                expression=name,
                type_text=constructor_types.get(name, "unknown"),
                symbolic_key=structural_key(name),
                metadata=(
                    (
                        "explicit-arity",
                        str(explicit_arity(constructor_types.get(name, ""))),
                    ),
                ),
            )
            for name in ordered
        )
        before_items = self.policy_router.model_items_scored
        before_batches = self.policy_router.model_batches
        before_elapsed = self.policy_router.model_elapsed_ms
        before_fallbacks = self.policy_router.symbolic_fallbacks
        constructor_matches_goal = any(
            result_head(constructor_types.get(name, "unknown"))
            == result_head(goal.target)
            for name in ordered
        )
        ranked = self.policy_router.rank(
            goal,
            candidates,
            classification=classify_structural_scheduling(
                construction_result_head_matches_goal=constructor_matches_goal,
                structural_construction_available=bool(ordered),
                structural_descent_available=(
                    self.recursive_call is not None
                    if self.recursive_call is not None
                    else None
                ),
                dependencies_ready=True,
                reflexive_relation_target=is_reflexive_relation_target(goal.target),
                relational_elimination_available=has_relational_context_evidence(
                    goal.target,
                    tuple(
                        entry.type
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    ),
                ),
            ),
        )
        self.stats.model_calls += self.policy_router.model_items_scored - before_items
        self.stats.model_batches += self.policy_router.model_batches - before_batches
        self.stats.model_elapsed_ms += (
            self.policy_router.model_elapsed_ms - before_elapsed
        )
        self.stats.symbolic_fallbacks += (
            self.policy_router.symbolic_fallbacks - before_fallbacks
        )
        return tuple(candidate.expression for candidate in ranked.candidates)

    @staticmethod
    def _introduction_readiness(checked: CommittedProofAction) -> int:
        """Count generated fields not closable after invertible introductions."""

        missing = 0
        for child in checked.generated_goals:
            try:
                _domains, result = parse_type(child.target).domains_and_result()
                available = {
                    parse_type(entry.type)
                    for entry in child.context
                    if entry.in_scope and entry.name
                }
            except ValueError:
                missing += 1
                continue
            missing += int(result not in available)
        return missing

    @staticmethod
    def _constructor_expression(name: str, type_text: str | None) -> str:
        if not type_text:
            return name
        domains = split_top_level_arrows(type_text)[:-1]
        visible_count = sum(
            1 for domain in domains if not domain.lstrip().startswith(("{", "⦃"))
        )
        return name if visible_count <= 10 else name + " ?" * visible_count

    @staticmethod
    def _has_opaque_type_head(goal: GoalInfo) -> bool:
        """Recognize a locally quantified type/family with no visible constructors."""

        try:
            application = split_top_level_application(goal.target)
        except ValueError:
            return False
        if not application:
            return False
        head = application[0]
        for entry in goal.context:
            if not (entry.name == head and result_head(entry.type).startswith("Set")):
                continue
            try:
                telescope = split_top_level_arrows(entry.type)[:-1]
                arity = sum(len(binder_domains(domain)) for domain in telescope)
            except ValueError:
                return False
            # A nullary abstract type is opaque only when it is the entire
            # target. In particular, the first operand of an infix type
            # former (``P + Q``) is not that type expression's head.
            return len(application) == arity + 1
        return False

    @staticmethod
    def _can_use_absurd_function_pattern(goal: GoalInfo) -> bool:
        """Whether Agda could structurally split the first function argument.

        ``λ ()`` can only eliminate a constructor-free datatype argument. It
        cannot eliminate another function, a universe, or an opaque type
        parameter, so probing those shapes only causes a rejected kernel
        transaction. Concrete indexed families remain eligible: Agda still
        decides whether their current index has no constructors.
        """

        parts = split_top_level_arrows(goal.target)
        if len(parts) < 2:
            return False
        try:
            domains = binder_domains(parts[0])
        except ValueError:
            return False
        if not domains:
            return False
        domain = domains[0]
        if top_level_arrow_count(domain):
            return False
        head = result_head(domain)
        if head.startswith("Set"):
            return False
        return not any(
            entry.in_scope
            and entry.name == head
            and result_head(entry.type).startswith("Set")
            for entry in goal.context
        )

    def _premise_actions(
        self, state: StateToken, goal: GoalInfo, *, retrieval_limit: int = 64
    ) -> tuple[ScopePremiseAction, ...]:
        key = (state, goal.goal_id)
        if key in self._scoped_actions:
            return self._scoped_actions[key].through(retrieval_limit)
        scoped = self._read_scoped_premises(state, goal)
        if scoped is not None:
            self._rank_scoped_premises(state, goal, scoped)
            return self._scoped_actions[key].through(retrieval_limit)
        if not isinstance(self.session, ScopeDeclarationSession):
            return ()
        if self._scope_catalog is None:
            self._scope_catalog, queries = visible_scope_declarations(
                self.session, state, goal
            )
            self.stats.premise_catalog_queries += queries
        return rank_scope_premises(
            goal,
            self._scope_catalog,
            excluded_names=self.excluded_premises,
        )

    def _read_scoped_premises(
        self, state: StateToken, goal: GoalInfo
    ) -> ScopedPremises | None:
        if not isinstance(self.session, ScopedRetrievalSession):
            return None
        started = time.monotonic()
        scoped = self.session.scoped_retrieval(
            state, goal_id=goal.goal_id, excluded_names=self.excluded_premises
        )
        if scoped is not None:
            self.stats.scoped_retrieval_elapsed_ms += (
                time.monotonic() - started
            ) * 1000
            self.stats.premise_catalog_queries += 1
            self.stats.scoped_retrieval_queries += 1
            self.stats.scoped_retrieval_nodes += scoped.structure_nodes
        return scoped

    def _rank_scoped_premises(
        self, state: StateToken, goal: GoalInfo, scoped: ScopedPremises
    ) -> tuple[ScopePremiseAction, ...]:
        # The live feed can exceed the legacy 128-premise fragment, but uses
        # the same caller action budget and smaller recursive branch slices.
        self.stats.premise_query_limit = self.action_budget
        started = time.monotonic()
        # Capture policy in the controller, not in an ambient environment read
        # during each query. Never mutate the gateway's source-bound snapshot.
        if scoped.query.query_symbol_lane != self._scoped_query_symbol_lane_enabled:
            scoped = replace(
                scoped,
                query=replace(
                    scoped.query,
                    query_symbol_lane=self._scoped_query_symbol_lane_enabled,
                ),
            )
        previous = self._previous_scoped_index
        if (
            self._scoped_index_reuse_enabled
            and previous is not None
            and previous[0].environment_id == state.environment_id
            and previous[0].module_id == state.module_id
        ):
            index = previous[1].updated(scoped.allowed, scoped.dependencies)
            self.stats.scoped_retrieval_incremental_builds += 1
        else:
            index = scoped.index()
        self.stats.scoped_retrieval_index_builds += 1
        self.stats.scoped_retrieval_index_build_elapsed_ms += (
            time.monotonic() - started
        ) * 1000
        if self._scoped_index_reuse_enabled:
            self._previous_scoped_index = (state, index)
        work = index.build_work
        self.stats.scoped_retrieval_index_feature_rows_reused += sum(
            int(work[name] or 0)
            for name in (
                "symbol_rows_reused",
                "lexical_rows_reused",
                "dependency_rows_reused",
            )
        )
        self.stats.scoped_retrieval_index_posting_updates += sum(
            int(work[name] or 0)
            for name in ("posting_entries_inserted", "posting_entries_removed")
        )
        ranked = index.retrieve(scoped.query, limit=512)
        self.stats.scoped_retrieval_candidates += ranked.candidate_count
        self.stats.scoped_retrieval_postings += ranked.postings_visited
        actions = scoped_premise_actions(scoped, ranked)
        record: dict[str, object] = {
            "schema_version": "agdaprover.scoped-retrieval-decision.v3"
            if ranked.dependency_graph_id is not None
            else "agdaprover.scoped-retrieval-decision.v2",
            "search_policy": PROGRESSIVE_POLICY,
            "retrieval_limit": 512,
            "index_id": ranked.index_id,
            "query_id": ranked.query_id,
            "scope_id": ranked.scope_id,
            "candidate_count": ranked.candidate_count,
            "postings_visited": ranked.postings_visited,
            "actions": [a.to_dict() for a in actions],
            "components": [
                {
                    "declaration_id": item.premise.declaration_id,
                    "head_match": item.head_match,
                    "symbol_overlap": item.symbol_overlap,
                    "lexical_overlap": item.lexical_overlap,
                    "arity_distance": item.arity_distance,
                    **(
                        {"dependency_score": item.dependency_score}
                        if ranked.dependency_graph_id is not None
                        else {}
                    ),
                    **(
                        {"query_symbol_match": item.query_symbol_match}
                        if ranked.query_symbol_lane
                        else {}
                    ),
                }
                for item in ranked.items
            ],
        }
        if ranked.dependency_graph_id is not None:
            record.update(
                dependency_graph_id=ranked.dependency_graph_id,
                dependency_postings_visited=ranked.dependency_postings_visited,
                ranking_policy=ranked.policy,
            )
        if self._scoped_index_reuse_enabled:
            record["schema_version"] = "agdaprover.scoped-retrieval-decision.v4"
            record["index_build_work"] = dict(work)
        if ranked.query_symbol_lane:
            record["schema_version"] = "agdaprover.scoped-retrieval-decision.v5"
            record["ranking_policy"] = ranked.policy
        self.stats.record_retrieval("decisions", record)
        # Exact state/interaction reuse only; no root/child type substitution
        # or similarity cache. Eviction cannot broaden scope.
        size = sum(
            len(action.name.encode())
            + len(action.type_text.encode())
            + len(action.expression.encode())
            for action in actions
        ) + len(json.dumps(ranked.to_dict(), ensure_ascii=False).encode())
        while self._scoped_actions and (
            len(self._scoped_actions) >= 64
            or sum(pool.serialized_bytes for pool in self._scoped_actions.values())
            + size
            > 32 * 1024**2
        ):
            oldest = next(iter(self._scoped_actions))
            self._scoped_actions.pop(oldest)
        types = dict(scoped.type_views)
        by_alias_type: dict[tuple[str, str], int] = {}
        for i, item in enumerate(ranked.items, 1):
            view = normalize_type_text(types[item.premise.declaration_id])
            for alias in item.premise.aliases:
                by_alias_type.setdefault((alias, view), i)
        entries = tuple(
            (by_alias_type[(action.name, action.type_text)], action)
            for action in actions
        )
        admission_order = scoped_premise_admission(goal, ranked, entries)
        admission_ranks = {rank: i for i, rank in enumerate(admission_order)}
        self._scoped_actions[(state, goal.goal_id)] = _ScopedActions(
            ranked,
            tuple(sorted(entries, key=lambda entry: admission_ranks[entry[0]])),
            size,
            admission_order,
        )
        self.stats.scoped_retrieval_elapsed_ms += (time.monotonic() - started) * 1000
        return actions

    def _ordered_premise_actions(
        self, state: StateToken, goal: GoalInfo, *, retrieval_limit: int = 64
    ) -> tuple[ScopePremiseAction, ...]:
        """Return the bounded symbolic tier order, optionally NNUE-tiebroken."""

        actions = self._premise_actions(state, goal, retrieval_limit=retrieval_limit)
        scoped = self._scoped_actions.get((state, goal.goal_id))
        retrieval_metadata = (
            scoped.metadata(retrieval_limit) if scoped is not None else {}
        )
        recursive_evidence = bool(
            self._recursive_action_cache.get((state.structural_hash, goal.goal_id))
        )
        priorities = {}
        for action in actions:
            base = premise_static_priority(goal, action)
            if recursive_evidence:
                prefix_priority = premise_result_prefix_priority(goal, action)
                priorities[action] = (
                    prefix_priority,
                    -int(premise_result_bindings_consistent(goal, action)),
                    (
                        -self._premise_explicit_arity(action)
                        if prefix_priority == 1
                        else 0
                    ),
                    *base,
                )
            else:
                priorities[action] = (3, 0, 0, *base)
        ordered = tuple(sorted(actions, key=priorities.__getitem__))
        grouped: dict[str, list[ScopePremiseAction]] = {}
        if scoped is not None:
            # Rank spellings through the existing unique-expression OR API.
            # Keep every distinct type view: result-directed applications
            # inferred from different overloads need not be the same request.
            for action in ordered:
                views = grouped.setdefault(action.expression, [])
                if action not in views:
                    views.append(action)
            ordered = tuple(views[0] for views in grouped.values())
        by_expression = {action.expression: action for action in ordered}
        candidates = tuple(
            policy_candidate(
                family="visible-premise",
                tag="refine-visible-premise",
                expression=action.expression,
                type_text=action.type_text,
                symbolic_key=priorities[action],
                metadata=(
                    ("explicit-arity", str(self._premise_explicit_arity(action))),
                    ("result-overlap", str(premise_result_overlap(goal, action))),
                )
                + retrieval_metadata.get(action, ()),
            )
            for action in ordered
        )
        before_items = self.policy_router.model_items_scored
        before_batches = self.policy_router.model_batches
        before_elapsed = self.policy_router.model_elapsed_ms
        before_fallbacks = self.policy_router.symbolic_fallbacks
        ranked = self.policy_router.rank(
            goal,
            candidates,
            classification=classify_structural_scheduling(
                recursive_result_head_matches_goal=(
                    any(
                        result_head(action.inferred_type) == result_head(goal.target)
                        for action in self._recursive_action_cache.get(
                            (state.structural_hash, goal.goal_id), ()
                        )
                    )
                    if recursive_evidence
                    else False
                ),
                structural_descent_available=recursive_evidence,
                reflexive_relation_target=is_reflexive_relation_target(goal.target),
                relational_elimination_available=has_relational_context_evidence(
                    goal.target,
                    tuple(
                        entry.type
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    ),
                ),
            ),
        )
        self.stats.model_calls += self.policy_router.model_items_scored - before_items
        self.stats.model_batches += self.policy_router.model_batches - before_batches
        self.stats.model_elapsed_ms += (
            self.policy_router.model_elapsed_ms - before_elapsed
        )
        self.stats.symbolic_fallbacks += (
            self.policy_router.symbolic_fallbacks - before_fallbacks
        )
        return tuple(
            action
            for candidate in ranked.candidates
            for action in grouped.get(
                candidate.expression, [by_expression[candidate.expression]]
            )
        )

    def _progressive_eliminators(
        self,
        goal: GoalInfo,
        ancestors: frozenset[tuple[object, ...]],
    ) -> tuple[tuple[str, tuple[str, ...]], ...]:
        """Filter generic eliminators whose premises revisit this branch."""

        visible_context = _context_type_signature(goal)
        return tuple(
            (expression, domains)
            for expression, domains in self._focused_visible_eliminators
            if all(
                (
                    _canonicalize_internal_metas(domain),
                    visible_context,
                )
                not in ancestors
                and normalize_type_text(strip_outer_parentheses(domain))
                != normalize_type_text(strip_outer_parentheses(goal.target))
                for domain in domains
            )
        )

    def _solve_with_visible_eliminators(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
    ) -> Iterator[ConstructorSolution]:
        """Refine a rigid goal by a kernel-observed polymorphic eliminator."""

        if any(
            entry.in_scope
            and entry.name
            and normalize_type_text(strip_outer_parentheses(entry.type))
            == normalize_type_text(strip_outer_parentheses(goal.target))
            for entry in goal.context
        ):
            return
        progressive_eliminators = self._progressive_eliminators(goal, ancestors)
        self.stats.actions_generated += len(progressive_eliminators)
        self.stats.premise_candidates += len(progressive_eliminators)
        for expression, _domains in progressive_eliminators:
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=expression,
            )
            self.stats.premise_queries += 1
            self.stats.premise_refinement_queries += 1
            if checked.accepted:
                yield from self._accepted_introduction(
                    goal,
                    checked,
                    depth,
                    ancestors,
                    premise_query_stop,
                )

    def _solve_with_relation_path(
        self,
        state: StateToken,
        goal: GoalInfo,
    ) -> tuple[ConstructorSolution, ...]:
        """Close one typed relation path discovered from the live signature."""

        if not (
            isinstance(self.session, TermInferenceSession)
            and isinstance(self.session, ScopeDeclarationSession)
        ):
            return ()
        target_relation = parse_relation(goal.target)
        referenced_relation_locals = tuple(
            entry
            for entry in goal.context
            if entry.in_scope
            and entry.name
            and re.search(rf"(?<!\w){re.escape(entry.name)}(?!\w)", goal.target)
            and target_relation is not None
            and parse_relation(
                entry.type,
                expected_operator=target_relation.operator,
            )
            is not None
        )
        cached_recursive_actions = self._recursive_action_cache.get(
            (state.structural_hash, goal.goal_id), ()
        )
        recursive_relation_seeds = tuple(
            action
            for action in cached_recursive_actions
            if target_relation is not None
            and parse_relation(
                action.inferred_type,
                expected_operator=target_relation.operator,
            )
            is not None
        )
        if self.defer_concrete_premises or (
            len(referenced_relation_locals) + len(recursive_relation_seeds) < 2
        ):
            return ()
        remaining = self.action_budget - self.stats.actions_considered
        if remaining <= 1:
            return ()
        actions = self._ordered_premise_actions(state, goal)
        heads = tuple(
            RelationHead(action.expression, action.type_text, order)
            for order, action in enumerate(actions)
        )
        recursive_seeds = tuple(
            (action.expression, action.inferred_type)
            for action in recursive_relation_seeds
        )
        result = solve_relation_path(
            self.session,
            state,
            goal,
            heads,
            query_budget=min(192, remaining - 1),
            deadline=self.deadline,
            seed_terms=recursive_seeds,
        )
        self.stats.relation_path = result.stats.to_dict()
        self.stats.actions_considered += result.stats.inference_queries
        self.stats.actions_generated += result.stats.applications_generated
        if result.expression is None:
            return ()
        if not self._charge():
            return ()
        checked = self.session.commit_proof_action(
            state,
            kind="give",
            goal_id=goal.goal_id,
            expression=result.expression,
        )
        self.stats.proof_checks += 1
        if checked.accepted and checked.child_state is not None:
            return (
                ConstructorSolution(
                    checked.child_state,
                    ProofPlan(result.expression),
                ),
            )
        return ()

    def _solve_with_scope_premises(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        *,
        selected_actions: tuple[ScopePremiseAction, ...] | None = None,
        observations: _SkeletonObservations | None = None,
    ) -> Iterator[ConstructorSolution]:
        if self.defer_concrete_premises:
            return
        if observations is not None and (
            observations.state != state or observations.goal_id != goal.goal_id
        ):
            raise ValueError("premise observations belong to a different state/goal")
        actions = tuple(
            action
            for action in (
                self._ordered_premise_actions(state, goal)
                if selected_actions is None
                else selected_actions
            )
            if not (
                explicit_arity(action.type_text) == 1
                and premise_structured_result_domains(action.type_text)
            )
        )
        self.stats.actions_generated += len(actions)
        self.stats.premise_candidates += len(actions)
        for action in actions:
            if self._scope_premise_queries >= min(
                self.stats.premise_query_limit, premise_query_stop
            ):
                return
            if not self._charge():
                return
            self.policy_router.mark("visible-premise", action.expression)
            # A visible declaration whose complete type is the current goal
            # is already a closed inhabitant.  Refining it would eta-expand
            # the declaration and manufacture one subgoal per argument (for
            # example turning a binary constructor used as a function into
            # two pointless element goals).  Prefer the exact checked give;
            # this is both complete for this case and substantially cheaper.
            if normalize_type_text(action.type_text) == normalize_type_text(
                goal.target
            ):
                direct_head = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression=action.expression,
                )
                self.stats.premise_queries += 1
                self._scope_premise_queries += 1
                self.stats.proof_checks += 1
                if direct_head.accepted and direct_head.child_state is not None:
                    yield ConstructorSolution(
                        direct_head.child_state,
                        ProofPlan(action.expression),
                    )
                    return
                if self._scope_premise_queries >= min(
                    self.stats.premise_query_limit, premise_query_stop
                ):
                    return
                if not self._charge():
                    return
            application = premise_result_application(goal, action)
            if application is None:
                application = premise_inferred_application(goal, action)
            if application is not None:
                direct = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression=application,
                )
                self.stats.premise_queries += 1
                self._scope_premise_queries += 1
                self.stats.proof_checks += 1
                if direct.accepted and direct.child_state is not None:
                    yield ConstructorSolution(
                        direct.child_state,
                        ProofPlan(application),
                    )
                    return
                if self._scope_premise_queries >= min(
                    self.stats.premise_query_limit, premise_query_stop
                ):
                    return
                if not self._charge():
                    return
            recursive_evidence = bool(
                self._recursive_action_cache.get((state.structural_hash, goal.goal_id))
            )
            prefix_application = (
                premise_result_prefix_application(goal, action)
                if recursive_evidence
                else None
            )
            refinement_expression = prefix_application or action.expression
            if observations is not None:
                previous = observations.attempts.get(refinement_expression)
                if previous is not None and not previous[0].accepted:
                    self.stats.scoped_retrieval_refinement_reuses += 1
                    continue
            checked = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=refinement_expression,
            )
            self.stats.premise_queries += 1
            self.stats.premise_refinement_queries += 1
            self._scope_premise_queries += 1
            attempt = {
                **action.to_dict(),
                "applied_expression": refinement_expression,
                "goal_target": goal.target,
                "accepted": checked.accepted,
                "generated_subgoals": len(checked.generated_goals),
                "rejection_code": checked.rejection_code,
            }
            if len(self.stats.premise_attempts) < _MAX_RECORDED_PREMISE_ATTEMPTS:
                self.stats.premise_attempts.append(attempt)
            else:
                self.stats.premise_attempts_omitted += 1
            if not checked.accepted:
                if observations is not None:
                    observations.attempts[refinement_expression] = (checked, None)
                continue
            expected = premise_expected_arguments(goal, action)
            # Reversible premises are sometimes essential: a useful chain may
            # begin by reorienting an obligation before another declaration
            # applies.  `_solve_goal` compares the exact canonical child with
            # all ancestors, so the inverse transition is pruned when it would
            # actually close a cycle without conflating different orientations.
            branch_query_stop = min(
                premise_query_stop,
                self._scope_premise_queries + _PREMISE_BRANCH_QUERY_SLICE,
            )
            if checked.child_state is not None and len(expected) == len(
                checked.generated_goals
            ):
                self._goal_hints.update(
                    ((checked.child_state.structural_hash, child.goal_id), target)
                    for child, target in zip(
                        checked.generated_goals, expected, strict=True
                    )
                )
            yield from self._accepted_introduction(
                goal,
                checked,
                depth,
                ancestors,
                branch_query_stop,
            )

    def _solve_children(
        self,
        state: StateToken,
        children: tuple[GoalInfo, ...],
        index: int,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        plans: tuple[ProofPlan, ...] = (),
        deprioritized_locals: frozenset[str] = frozenset(),
    ) -> Iterator[tuple[StateToken, tuple[ProofPlan, ...]]]:
        if index >= len(children):
            yield state, plans
            return
        child_id = children[index].goal_id
        if self._goal(state, child_id) is None:
            return
        used_atomic_siblings = frozenset(
            plan.render() for plan in plans if not plan.children
        )
        if self._has_ready_nonrecursive_eliminators:
            used_atomic_siblings |= deprioritized_locals
        for solution in self._solve_goal(
            state,
            child_id,
            depth,
            ancestors,
            deprioritized_locals=used_atomic_siblings,
            premise_query_stop=premise_query_stop,
        ):
            yield from self._solve_children(
                solution.state,
                children,
                index + 1,
                depth,
                ancestors,
                premise_query_stop,
                (*plans, solution.plan),
                deprioritized_locals,
            )

    def _accepted_introduction(
        self,
        _goal: GoalInfo,
        checked: CommittedProofAction,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        *,
        deprioritized_locals: frozenset[str] = frozenset(),
    ) -> Iterator[ConstructorSolution]:
        child_state = checked.child_state
        preview = checked.preview
        children = checked.generated_goals
        if child_state is None or preview is None:
            return
        hole_count = len(_HOLE.findall(preview))
        if hole_count != len(children):
            return
        self.stats.generated_subgoals += len(children)
        if not children:
            yield ConstructorSolution(child_state, ProofPlan(preview))
            return
        for final_state, child_plans in self._solve_children(
            child_state,
            children,
            0,
            depth + 1,
            ancestors,
            premise_query_stop,
            deprioritized_locals=deprioritized_locals,
        ):
            yield ConstructorSolution(final_state, ProofPlan(preview, child_plans))

    def _solve_goal(
        self,
        state: StateToken,
        goal_id: int,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        *,
        deprioritized_locals: frozenset[str] = frozenset(),
        premise_query_stop: int | None = None,
    ) -> Iterator[ConstructorSolution]:
        if not self._available():
            return
        if self.max_depth is not None and depth > self.max_depth:
            self.stats.depth_pruned += 1
            self.saw_exhaustion = True
            return
        goal = self._goal(state, goal_id)
        if goal is None:
            return
        self.stats.states_expanded += 1
        self.stats.max_depth = max(self.stats.max_depth, depth)
        key = (
            _canonicalize_internal_metas(goal.target),
            _context_type_signature(goal),
        )
        if key in ancestors:
            # A repeated sequent is a cycle only after checking the exact
            # inhabitants already present in the live context.  Constructor
            # wrapping commonly recreates its parent's target for a field
            # (for example the tail of a cons-like constructor), while a
            # parent argument is the intended finite field value.  Pruning
            # before this checked reuse made such ordinary wrappers look
            # recursively infinite.  This rule is type-directed and applies
            # equally to recursive datatype fields, records, and indexed
            # families; it assigns no meaning to any constructor.
            exact_local_solved = False
            exact_locals = sorted(
                (
                    entry.name
                    for entry in goal.context
                    if entry.in_scope
                    and entry.name
                    and normalize_type_text(strip_outer_parentheses(entry.type))
                    == normalize_type_text(strip_outer_parentheses(goal.target))
                ),
                key=lambda name: (name in deprioritized_locals, name),
            )
            self.stats.actions_generated += len(exact_locals)
            for name in exact_locals:
                if not self._charge():
                    return
                checked_local = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression=name,
                )
                self.stats.proof_checks += 1
                if checked_local.accepted and checked_local.child_state is not None:
                    exact_local_solved = True
                    yield ConstructorSolution(
                        checked_local.child_state,
                        ProofPlan(name),
                    )
            exact_premises = tuple(
                action
                for action in self._ordered_premise_actions(state, goal)
                if normalize_type_text(strip_outer_parentheses(action.type_text))
                == normalize_type_text(strip_outer_parentheses(goal.target))
            )
            self.stats.actions_generated += len(exact_premises)
            self.stats.premise_candidates += len(exact_premises)
            for action in exact_premises:
                if not self._charge():
                    return
                checked_premise = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression=action.expression,
                )
                self.stats.premise_queries += 1
                self.stats.proof_checks += 1
                if checked_premise.accepted and checked_premise.child_state is not None:
                    exact_local_solved = True
                    yield ConstructorSolution(
                        checked_premise.child_state,
                        ProofPlan(action.expression),
                    )
            recursive_solved = False
            for solution in self._solve_with_recursive_calls(
                state,
                goal,
                deprioritized_terms=deprioritized_locals,
            ):
                recursive_solved = True
                yield solution
            if exact_local_solved or recursive_solved:
                return
            self.stats.cycles_pruned += 1
            return
        descendants = ancestors | {key}
        if premise_query_stop is None:
            premise_query_stop = self.stats.premise_query_limit

        # Function introduction is invertible.  Asking Agda once introduces
        # the complete visible telescope, rather than one binder per search
        # state or one whole-file reload per binder.
        if top_level_arrow_count(goal.target):
            # A function out of a constructor-free domain has a canonical
            # absurd-pattern clause.  This proposal is deliberately blind to
            # the domain's name and representation: Agda accepts ``λ ()``
            # exactly when its coverage checker can eliminate the argument.
            # Trying it before ordinary introduction prevents goals such as a
            # W-node's ``B a → W A B`` field from recursively rebuilding an
            # infinite tree when the selected shape actually has no children.
            if self._can_use_absurd_function_pattern(goal):
                self.stats.actions_generated += 1
                if not self._charge():
                    return
                empty_function = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression="λ ()",
                )
                self.stats.empty_function_queries += 1
                self.stats.proof_checks += 1
                if empty_function.accepted and empty_function.child_state is not None:
                    self.stats.empty_function_closures += 1
                    yield ConstructorSolution(
                        empty_function.child_state,
                        ProofPlan("λ ()"),
                    )
                    # Interaction refinement can provisionally accept an
                    # absurd lambda whose coverage obligation is incomplete.
                    # The outer solution filter rejects that proposal; keep
                    # ordinary function introduction available on resume.
            self.stats.actions_generated += 1
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression="",
            )
            self.stats.constructor_queries += 1
            if checked.accepted:
                yield from self._accepted_introduction(
                    goal,
                    checked,
                    depth,
                    descendants,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                )
            return

        remaining = self.action_budget - self.stats.actions_considered
        if remaining <= 0:
            self.saw_exhaustion = True
            return

        # A local inhabitant or one shallow local application is cheaper and
        # more informative than rebuilding a value through its sole
        # constructor.  This matters for destructor branches (``children i``)
        # and prevents a one-constructor fast path from replacing a projection
        # with an unrelated recursively nested value.
        target_head = result_head(goal.target)
        shallow_local_possible = (
            self.recursive_call is not None
            and parse_relation(goal.target) is None
            and any(
                entry.in_scope and entry.name and result_head(entry.type) == target_head
                for entry in goal.context
            )
        )
        if shallow_local_possible and not (self.require_recursive_call and depth == 0):
            shallow = focused_candidates(
                goal,
                action_budget=min(16, remaining),
                solution_limit=min(8, remaining),
                timeout_seconds=max(0.0, self.deadline - time.monotonic()),
                max_depth=2,
                branch_scorer=(
                    self.policy_router.score_focused
                    if self.focused_policy is not None
                    else None
                ),
            )
            self._record_focused(shallow)
            shallow_solved = False
            for term in shallow.terms:
                rendered = render_term(term)
                if not self._available():
                    return
                checked_local = self.session.commit_proof_action(
                    state,
                    kind="give",
                    goal_id=goal.goal_id,
                    expression=rendered,
                )
                self.stats.proof_checks += 1
                if checked_local.accepted and checked_local.child_state is not None:
                    shallow_solved = True
                    yield ConstructorSolution(
                        checked_local.child_state,
                        ProofPlan(rendered),
                    )
            if shallow_solved and not self.require_recursive_call:
                return

        # Concrete one-constructor data/record goals have an invertible
        # introduction just like function goals.  Query it before unrestricted
        # focused composition: higher-order branch functions can otherwise
        # induce a very large space of irrelevant applications even though
        # the target has exactly one structural shape.  Agda signals
        # ambiguity through alternatives, so only an accepted action with no
        # alternatives is committed as the deterministic fast path.
        opaque_type_head = self._has_opaque_type_head(goal)
        recursive_codomain_head = (
            result_head(split_top_level_arrows(self.recursive_call.root_type)[-1])
            if self.recursive_call is not None
            else ""
        )
        prefer_recursive_call = (
            self.recursive_call is not None
            and depth > 0
            and result_head(goal.target) == recursive_codomain_head
        )
        intro_check: CommittedProofAction | None = None
        if (
            self.recursive_call is not None
            and not opaque_type_head
            and not prefer_recursive_call
        ):
            self.stats.actions_generated += 1
            if not self._charge():
                return
            intro_check = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression="",
            )
            self.stats.constructor_queries += 1
            if intro_check.accepted and not intro_check.alternatives:
                self.stats.deterministic_constructor_introductions += 1
                deterministic_solved = False
                for solution in self._accepted_introduction(
                    goal,
                    intro_check,
                    depth,
                    descendants,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                ):
                    deterministic_solved = True
                    yield solution
                if deterministic_solved:
                    return
            elif len(intro_check.alternatives) == 1:
                self.stats.actions_generated += 1
                if not self._charge():
                    return
                selected = self.session.commit_proof_action(
                    state,
                    kind="refine",
                    goal_id=goal.goal_id,
                    expression=intro_check.alternatives[0],
                )
                self.stats.constructor_queries += 1
                if selected.accepted:
                    self.stats.deterministic_constructor_introductions += 1
                    deterministic_solved = False
                    for solution in self._accepted_introduction(
                        goal,
                        selected,
                        depth,
                        descendants,
                        premise_query_stop,
                        deprioritized_locals=deprioritized_locals,
                    ):
                        deterministic_solved = True
                        yield solution
                    if deterministic_solved:
                        return
            elif intro_check.alternatives and self.require_recursive_call:
                # In a constructor-wrapped recursive plan, Agda's reported
                # introduction alternatives are the complete structural OR
                # node.  Enumerate them directly instead of falling through
                # to unrestricted premise search merely to rediscover the
                # same constructors.  Plans without a recursive descendant
                # are filtered at the root, so another constructor remains
                # available without any datatype-specific ordering rule.
                for alternative in intro_check.alternatives:
                    self.stats.actions_generated += 1
                    if not self._charge():
                        return
                    selected = self.session.commit_proof_action(
                        state,
                        kind="refine",
                        goal_id=goal.goal_id,
                        expression=alternative,
                    )
                    self.stats.constructor_queries += 1
                    if not selected.accepted:
                        continue
                    yield from self._accepted_introduction(
                        goal,
                        selected,
                        depth,
                        descendants,
                        premise_query_stop,
                        deprioritized_locals=deprioritized_locals,
                    )
                return

        # A recursive call is a narrow, kernel-inferred action and should be
        # attempted before unrestricted focused composition.  Higher-order
        # W-algebra contexts can otherwise generate an infinite family of
        # logically valid but irrelevant function compositions.
        recursive_solved = False
        delay_recursive_for_constructor_shape = (
            self.preferred_constructor_arity is not None
            and not self._has_opaque_type_head(goal)
            and (depth == 0 or result_head(goal.target) != recursive_codomain_head)
        )
        for solution in (
            self._solve_with_recursive_calls(
                state,
                goal,
                deprioritized_terms=deprioritized_locals,
            )
            if not delay_recursive_for_constructor_shape
            else ()
        ):
            recursive_solved = True
            yield solution
        if recursive_solved:
            return

        if self._has_ready_nonrecursive_eliminators:
            continuation_solved = False
            for solution in self._solve_with_local_refinements(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                continuation_only=True,
                deprioritized_terms=deprioritized_locals,
                deprioritized_only=False,
            ):
                continuation_solved = True
                yield solution
            if continuation_solved:
                return

            shares_structured_head = any(
                entry.in_scope
                and entry.name
                and not top_level_arrow_count(entry.type)
                and result_head(entry.type) == result_head(goal.target)
                for entry in goal.context
            )
            if not opaque_type_head and intro_check is None and shares_structured_head:
                self.stats.actions_generated += 1
                if not self._charge():
                    return
                intro_check = self.session.commit_proof_action(
                    state,
                    kind="refine",
                    goal_id=goal.goal_id,
                    expression="",
                )
                self.stats.constructor_queries += 1
                if (
                    intro_check.accepted
                    and not intro_check.alternatives
                    and self.preferred_constructor_arity is None
                ):
                    solved = False
                    for solution in self._accepted_introduction(
                        goal,
                        intro_check,
                        depth,
                        descendants,
                        premise_query_stop,
                        deprioritized_locals=deprioritized_locals,
                    ):
                        solved = True
                        yield solution
                    if solved:
                        return

            projection_closure_solved = False
            for solution in self._solve_with_ready_structured_results(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                deprioritized_locals,
                closure_only=True,
            ):
                projection_closure_solved = True
                yield solution
            if projection_closure_solved:
                return

        # Consume a concrete source through a nonrecursive, result-polymorphic
        # eliminator before unrestricted term composition.  Telescope shape
        # supplies this action; Agda remains the applicability authority.
        if self.recursive_call is None:
            ready_eliminator_solved = False
            for solution in self._solve_with_ready_eliminators(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                deprioritized_locals,
            ):
                ready_eliminator_solved = True
                yield solution
            if ready_eliminator_solved:
                return

            if self._has_ready_nonrecursive_eliminators:
                ready_structured_solved = False
                for solution in self._solve_with_ready_structured_results(
                    state,
                    goal,
                    depth,
                    descendants,
                    premise_query_stop,
                    deprioritized_locals,
                ):
                    ready_structured_solved = True
                    yield solution
                if ready_structured_solved:
                    return

        local_refinement_solved = False
        if self.recursive_call is not None or self._has_ready_nonrecursive_eliminators:
            for solution in self._solve_with_local_refinements(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                continuation_only=(
                    False if self._has_ready_nonrecursive_eliminators else None
                ),
                deprioritized_terms=deprioritized_locals,
                deprioritized_only=(
                    False if self._has_ready_nonrecursive_eliminators else None
                ),
            ):
                local_refinement_solved = True
                yield solution
        if local_refinement_solved:
            return

        if self._has_ready_nonrecursive_eliminators:
            deferred_local_solved = False
            for solution in self._solve_with_local_refinements(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                deprioritized_terms=deprioritized_locals,
                deprioritized_only=True,
            ):
                deferred_local_solved = True
                yield solution
            if deferred_local_solved:
                return

        eliminator_solved = False
        if opaque_type_head:
            for solution in self._solve_with_visible_eliminators(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
            ):
                eliminator_solved = True
                yield solution
        if eliminator_solved:
            return

        remaining = self.action_budget - self.stats.actions_considered
        if remaining <= 0:
            self.saw_exhaustion = True
            return
        focused_eliminators = (
            self._progressive_eliminators(goal, descendants) if opaque_type_head else ()
        )
        focused_action_budget = min(64, remaining)
        focused = focused_candidates(
            goal,
            action_budget=focused_action_budget,
            # A symbolic type match can still be rejected by dependent
            # constraints known only to Agda.  Preserve a bounded kernel
            # candidate batch independently of the requested final-proof
            # count, so a rejected first local does not hide the valid one.
            solution_limit=min(focused_action_budget, 1 if focused_eliminators else 64),
            timeout_seconds=max(0.0, self.deadline - time.monotonic()),
            max_depth=(None if self.max_depth is None else self.max_depth - depth),
            branch_scorer=(
                self.policy_router.score_focused
                if self.focused_policy is not None
                else None
            ),
            eliminators=focused_eliminators,
        )
        self._record_focused(focused)
        if focused.status == "resource-exhausted":
            self.saw_exhaustion = True
        attempted_local_terms: set[str] = set()
        for term in focused.terms:
            if time.monotonic() >= self.deadline:
                self.saw_exhaustion = True
                return
            rendered = render_term(term)
            attempted_local_terms.add(rendered)
            checked = self.session.commit_proof_action(
                state,
                kind="give",
                goal_id=goal.goal_id,
                expression=rendered,
            )
            self.stats.proof_checks += 1
            if checked.accepted and checked.child_state is not None:
                yield ConstructorSolution(checked.child_state, ProofPlan(rendered))

        # A target containing Agda metavariables may not textually match a
        # local type even though unification makes that local the unique valid
        # choice. Probe each remaining in-scope local once; the kernel rejects
        # wrong dependency levels and indices.
        local_probes = (
            tuple(
                entry.name
                for entry in goal.context
                if entry.in_scope
                and entry.name
                and entry.name not in attempted_local_terms
            )
            if _INTERNAL_META.search(goal.target)
            else ()
        )
        local_probes = tuple(
            sorted(
                local_probes,
                key=lambda name: (name in deprioritized_locals, name),
            )
        )
        self.stats.actions_generated += len(local_probes)
        for name in local_probes:
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="give",
                goal_id=goal.goal_id,
                expression=name,
            )
            self.stats.proof_checks += 1
            if checked.accepted and checked.child_state is not None:
                yield ConstructorSolution(checked.child_state, ProofPlan(name))

        # Agda may display an implicit context value in the target while
        # marking its printed name out of scope in the generated clause.  The
        # expected type can nevertheless determine that value uniquely.  An
        # anonymous placeholder is a safe proposal only when such an exact
        # hidden-context type exists and the kernel confirms that committing it
        # creates no additional internal obligation.
        anonymous_exact_local = any(
            not entry.in_scope
            and entry.name
            and normalize_type_text(entry.type) == normalize_type_text(goal.target)
            for entry in goal.context
        )
        if anonymous_exact_local and isinstance(
            self.session, InternalObligationSession
        ):
            before = self.session.internal_obligation_counts(state)
            self.stats.completion_queries += 1
            self.stats.actions_generated += 1
            if not self._charge():
                return
            checked = self.session.commit_proof_action(
                state,
                kind="give",
                goal_id=goal.goal_id,
                expression="_",
            )
            self.stats.proof_checks += 1
            if checked.accepted and checked.child_state is not None:
                after = self.session.internal_obligation_counts(checked.child_state)
                self.stats.completion_queries += 1
                if all(
                    current <= previous
                    for current, previous in zip(after, before, strict=True)
                ):
                    yield ConstructorSolution(checked.child_state, ProofPlan("_"))

        if opaque_type_head:
            # A locally quantified carrier/family has no constructor catalogue
            # of its own. Kernel-observed polymorphic eliminators were already
            # tried above; unrestricted global-premise expansion here merely
            # invents recursively nested inhabitants of the abstract head.
            return

        # A failed empty intro is still valuable: Agda either reports no
        # constructor, or enumerates every constructor compatible with the
        # current indices.  Only the latter creates an OR-node.
        if not opaque_type_head and intro_check is None:
            self.stats.actions_generated += 1
            if not self._charge():
                return
            intro_check = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression="",
            )
            self.stats.constructor_queries += 1
            if intro_check.accepted and self.preferred_constructor_arity is None:
                self.stats.deterministic_constructor_introductions += 1
                yield from self._accepted_introduction(
                    goal,
                    intro_check,
                    depth,
                    descendants,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                )
        catalog: tuple[tuple[str, str], ...] = ()
        if intro_check is not None and (
            intro_check.alternatives
            or intro_check.rejection_code
            in {"agda-interaction-cannot-refine", "agda-intro-not-found"}
            or self.preferred_constructor_arity is not None
        ):
            catalog = self.session.constructor_candidates(
                state,
                goal_id=goal.goal_id,
                type_head=result_head(goal.target),
            )
            self.stats.catalog_queries += 1
        target_head = result_head(goal.target)
        constructor_catalog = tuple(
            (name, type_text)
            for name, type_text in catalog
            if result_head(type_text) == target_head
        )
        if (
            intro_check is not None
            and intro_check.accepted
            and self.preferred_constructor_arity is not None
            and not constructor_catalog
        ):
            self.stats.deterministic_constructor_introductions += 1
            yield from self._accepted_introduction(
                goal,
                intro_check,
                depth,
                descendants,
                premise_query_stop,
                deprioritized_locals=deprioritized_locals,
            )
        if (
            intro_check is not None
            and not intro_check.alternatives
            and catalog
            and not constructor_catalog
        ):
            # A datatype module exports constructors, while a record module
            # exports its fields.  A record literal bypasses the named-record
            # constructor's ten-appended-meta limit and lets Agda elaborate
            # dependent fields in declaration order.
            record_literal = (
                "record { "
                + " ; ".join(f"{name} = ?" for name, _type in catalog)
                + " }"
            )
            self.stats.actions_generated += 1
            self.stats.constructor_branches += 1
            if not self._charge():
                return
            selected = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=record_literal,
            )
            self.stats.constructor_queries += 1
            if selected.accepted:
                yield from self._accepted_introduction(
                    goal,
                    selected,
                    depth,
                    descendants,
                    premise_query_stop,
                    deprioritized_locals=deprioritized_locals,
                )
            yield from self._solve_with_progressive_premises(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
                allow_skeletons=False,
            )
            return
        constructor_types = dict(constructor_catalog)
        names = (intro_check.alternatives if intro_check is not None else ()) or tuple(
            name for name, _type in constructor_catalog
        )
        constructors = self._ordered_constructors(goal, names, constructor_types)
        if len(constructors) == 1:
            self.stats.deterministic_constructor_introductions += 1
        elif len(constructors) > 1:
            self.stats.constructor_or_nodes += 1
        self.stats.actions_generated += len(constructors)
        self.stats.constructor_branches += len(constructors)
        selected_constructors: list[tuple[int, int, str, CommittedProofAction]] = []
        for constructor_order, constructor in enumerate(constructors):
            if not self._charge():
                return
            self.policy_router.mark("constructor-choice", constructor)
            selected = self.session.commit_proof_action(
                state,
                kind="refine",
                goal_id=goal.goal_id,
                expression=self._constructor_expression(
                    constructor, constructor_types.get(constructor)
                ),
            )
            self.stats.constructor_queries += 1
            if selected.accepted:
                selected_constructors.append(
                    (
                        self._introduction_readiness(selected),
                        constructor_order,
                        constructor,
                        selected,
                    )
                )
            else:
                self.policy_router.mark(
                    "constructor-choice", constructor, outcome="invalid"
                )
        for _readiness, _order, _constructor, selected in sorted(
            selected_constructors,
            key=lambda item: (item[0], item[1]),
        ):
            yield from self._accepted_introduction(
                goal,
                selected,
                depth,
                descendants,
                premise_query_stop,
                deprioritized_locals=deprioritized_locals,
            )
        if not opaque_type_head:
            eliminator_solved = False
            for solution in self._solve_with_visible_eliminators(
                state,
                goal,
                depth,
                descendants,
                premise_query_stop,
            ):
                eliminator_solved = True
                yield solution
            if eliminator_solved:
                return
        if delay_recursive_for_constructor_shape:
            for solution in self._solve_with_recursive_calls(
                state,
                goal,
                deprioritized_terms=deprioritized_locals,
            ):
                yield solution
        if self.defer_concrete_premises and goal_has_concrete_nullary_scrutinee(goal):
            return
        relation_solutions = self._solve_with_relation_path(state, goal)
        if relation_solutions:
            yield from relation_solutions
            return
        yield from self._solve_with_progressive_premises(
            state, goal, depth, descendants, premise_query_stop
        )

    def _solve_with_progressive_premises(
        self,
        state: StateToken,
        goal: GoalInfo,
        depth: int,
        ancestors: frozenset[tuple[object, ...]],
        premise_query_stop: int,
        *,
        allow_skeletons: bool = True,
    ) -> Iterator[ConstructorSolution]:
        # The disabled capability keeps the old ordering, query slices and
        # fallback exactly. Only the checked live-scope feed is widened.
        self._premise_actions(state, goal)
        pool = self._scoped_actions.get((state, goal.goal_id))
        if pool is None:
            solved = False
            for solution in self._solve_with_scope_premises(
                state, goal, depth, ancestors, premise_query_stop
            ):
                solved = True
                yield solution
            if not solved and allow_skeletons:
                yield from self._solve_with_application_skeletons(
                    state, goal, depth=depth
                )
            return
        ranked = pool.ranking
        ranks = {action: rank for rank, action in pool.entries}
        limits = ranked.progressive_limits()
        attempted: set[ScopePremiseAction] = set()
        observations = _SkeletonObservations(state, goal.goal_id)
        for limit in limits:
            if not self._available():
                return
            actions = self._ordered_premise_actions(state, goal, retrieval_limit=limit)
            new_actions = tuple(action for action in actions if action not in attempted)
            attempted.update(new_actions)
            supported_composition = (
                frozenset(shallow_composition_actions(goal, actions))
                if allow_skeletons and self.defer_concrete_premises
                else frozenset(actions)
            )
            record = {
                "schema_version": "agdaprover.retrieval-widening.v3",
                "search_policy": PROGRESSIVE_POLICY,
                "index_id": ranked.index_id,
                "query_id": ranked.query_id,
                "scope_id": ranked.scope_id,
                "width": limit,
                "ordered_expressions": [a.expression for a in actions],
                "new_expressions": [a.expression for a in new_actions],
                "ordered_ranks": [ranks[a] for a in actions],
                "new_ranks": [ranks[a] for a in new_actions],
                "admission_order": list(pool.admission_order),
                "composition_deferred_expressions": [
                    a.expression for a in actions if a not in supported_composition
                ],
            }
            self.stats.record_retrieval("widenings", record)
            solved = False
            for solution in self._solve_with_scope_premises(
                state,
                goal,
                depth,
                ancestors,
                premise_query_stop,
                selected_actions=new_actions,
                observations=observations,
            ):
                solved = True
                yield solution
            if solved:
                return
            if allow_skeletons:
                solutions = self._solve_with_application_skeletons(
                    state,
                    goal,
                    depth=depth,
                    selected_actions=actions,
                    observations=observations,
                    query_slice=16 if limit != limits[-1] else 64,
                )
                if solutions:
                    yield from solutions
                    return

    @staticmethod
    def _premise_explicit_arity(action: ScopePremiseAction) -> int:
        """Count displayed explicit arguments without interpreting their types."""

        return explicit_arity(action.type_text)

    def _solve_with_application_skeletons(
        self,
        state: StateToken,
        goal: GoalInfo,
        *,
        depth: int,
        selected_actions: tuple[ScopePremiseAction, ...] | None = None,
        observations: _SkeletonObservations | None = None,
        query_slice: int = 16,
    ) -> tuple[ConstructorSolution, ...]:
        """Complete a short visible-premise application by kernel feedback.

        Skeleton holes are Agda inference placeholders, not admitted goals.
        A candidate is returned only when the transactional state has no new
        visible or internal obligations. Accepted partial skeletons are
        progressively expanded in increasing unresolved-obligation order.
        """

        if not isinstance(self.session, InternalObligationSession):
            return ()
        if observations is not None and (
            observations.state != state or observations.goal_id != goal.goal_id
        ):
            raise ValueError("skeleton observations belong to a different state/goal")
        ordered_actions = tuple(
            action
            for action in (
                self._ordered_premise_actions(state, goal)
                if selected_actions is None
                else selected_actions
            )
            if not (
                explicit_arity(action.type_text) == 1
                and premise_structured_result_domains(action.type_text)
            )
        )
        if observations is not None and self.defer_concrete_premises:
            supported = shallow_composition_actions(goal, ordered_actions)
            self.stats.scoped_retrieval_composition_head_deferrals += len(
                ordered_actions
            ) - len(supported)
            ordered_actions = supported
        order = {action: index for index, action in enumerate(ordered_actions)}
        actions = tuple(
            sorted(
                ordered_actions,
                key=lambda action: (
                    -premise_result_overlap(goal, action),
                    order[action],
                ),
            )[: _SKELETON_HEAD_LIMIT if observations is None else 512]
        )
        # Recursive calls are proof-relevant inhabitants just like local
        # hypotheses.  Retain their inferred applications as terminal leaves
        # in the same bounded skeleton grammar, so a visible congruence or
        # transitivity principle can consume recursive evidence.  Previously
        # they were tried only as complete solutions, which forced the case
        # engine to keep splitting whenever an induction hypothesis needed
        # one small surrounding proof context.
        recursive_heads = tuple(
            _PremiseSkeleton(action.expression, ())
            for action in self._recursive_action_cache.get(
                (state.structural_hash, goal.goal_id), ()
            )[:12]
        )
        heads = tuple(
            dict.fromkeys(
                (
                    *recursive_heads,
                    *(
                        _PremiseSkeleton(
                            action.expression,
                            (None,) * self._premise_explicit_arity(action),
                        )
                        for action in actions
                    ),
                )
            )
        )
        if not heads:
            return ()
        max_nodes = (
            5 if self.max_depth is None else max(1, min(5, self.max_depth - depth + 1))
        )
        if observations is None or observations.baseline is None:
            baseline = self.session.internal_obligation_counts(state)
            self.stats.completion_queries += 1
            if observations is not None:
                observations.baseline = baseline
        else:
            baseline = observations.baseline
        relational_evidence_available = has_relational_context_evidence(
            goal.target,
            tuple(
                entry.type for entry in goal.context if entry.in_scope and entry.name
            ),
        )
        query_stop = min(
            _SKELETON_QUERY_LIMIT,
            self.stats.skeleton_queries
            + (16 if relational_evidence_available else _SKELETON_QUERY_LIMIT),
        )
        if observations is not None:
            # Leave room for later retrieved families. This slice is still
            # charged to the same total action/deadline budget as all search.
            query_stop = self.stats.skeleton_queries + query_slice
            if self.defer_concrete_premises:
                # This orchestration phase deliberately leaves case search
                # pending. Widening must not reset its composition allowance:
                # otherwise imported declarations multiply a shallow probe
                # into enough work to starve structural elimination. Preserve
                # the legacy 16/64 bounds across this exact-parent sequence.
                if observations.deferred_query_stop is None:
                    observations.deferred_query_stop = min(
                        _SKELETON_QUERY_LIMIT,
                        self.stats.skeleton_queries
                        + (
                            16
                            if relational_evidence_available
                            else _SKELETON_QUERY_LIMIT
                        ),
                    )
                query_stop = min(query_stop, observations.deferred_query_stop)
        queue = BatchedFrontier[
            tuple[tuple[int, int, int], _PremiseSkeleton, int, int]
        ]()
        queued: dict[str, tuple[int, int, int]] = {}
        head_outcomes: dict[str, int | None] = {}
        deferred_heads: list[tuple[_PremiseSkeleton, int, int]] = []
        head_order = {head.render(): index for index, head in enumerate(heads)}
        sequence = 0

        def expansion_heads() -> tuple[_PremiseSkeleton, ...]:
            accepted = tuple(
                unresolved
                for unresolved in head_outcomes.values()
                if unresolved is not None
            )
            threshold = min(accepted) + 2 if accepted else 0

            def retained_head(head: _PremiseSkeleton) -> bool:
                outcome = head_outcomes.get(head.render())
                return head.render() in head_outcomes and (
                    outcome is None or outcome <= threshold
                )

            retained = tuple(head for head in heads if retained_head(head))
            return tuple(
                sorted(
                    retained,
                    key=lambda head: (
                        head_outcomes[head.render()] is None,
                        (
                            head_outcomes[head.render()]
                            if head_outcomes[head.render()] is not None
                            else math.inf
                        ),
                        head_order[head.render()],
                    ),
                )
            )

        def enqueue(
            skeleton: _PremiseSkeleton,
            *,
            unresolved: int = 0,
            progress_credit: int = 0,
        ) -> None:
            nonlocal sequence
            rendered = skeleton.render()
            priority = (
                unresolved - progress_credit + 2 * skeleton.repetition_count,
                skeleton.node_count,
                -skeleton.hole_count,
            )
            previous = queued.get(rendered)
            if (
                (previous is not None and previous <= priority)
                or skeleton.node_count > max_nodes
                or len(rendered.encode("utf-8")) > 4096
            ):
                return
            if observations is not None and len(queue) >= 2048:
                self.stats.scoped_retrieval_frontier_pruned += 1
                return
            queued[rendered] = priority
            sequence += 1
            queue.push(
                priority,
                sequence,
                (priority, skeleton, unresolved, progress_credit),
            )
            self.stats.skeleton_candidates += 1
            self.stats.skeleton_frontier_peak = max(
                self.stats.skeleton_frontier_peak, len(queue)
            )

        for head in heads:
            enqueue(head)

        def expand(
            skeleton: _PremiseSkeleton,
            unresolved: int,
            progress_credit: int,
        ) -> None:
            if skeleton.node_count >= max_nodes:
                return
            for path in skeleton.hole_paths():
                for head in expansion_heads():
                    enqueue(
                        skeleton.fill(path, head),
                        unresolved=unresolved,
                        progress_credit=progress_credit,
                    )

        def release_deferred_heads() -> None:
            if len(head_outcomes) != len(heads):
                return
            while deferred_heads:
                skeleton, unresolved, progress_credit = deferred_heads.pop(0)
                expand(skeleton, unresolved, progress_credit)

        seen: set[str] = set()
        while queue and self.stats.skeleton_queries < query_stop and self._available():
            (
                _priority,
                skeleton,
                estimated_unresolved,
                progress_credit,
            ) = queue.pop()
            rendered = skeleton.render()
            if queued.get(rendered) != _priority:
                continue
            queued.pop(rendered, None)
            if rendered in seen:
                continue
            seen.add(rendered)
            cached = (
                observations.attempts.get(rendered)
                if observations is not None
                else None
            )
            obligations = None
            if cached is not None:
                checked, obligations = cached
                self.stats.scoped_retrieval_refinement_reuses += 1
            else:
                if not self._charge():
                    break
                checked = self.session.commit_proof_action(
                    state,
                    kind="refine",
                    goal_id=goal.goal_id,
                    expression=rendered,
                )
                self.stats.skeleton_queries += 1
                self.stats.premise_queries += 1
                self.stats.premise_refinement_queries += 1
            is_head = skeleton.node_count == 1
            recorded_attempt: dict[str, object] | None = None
            if cached is not None:
                pass
            elif len(self.stats.skeleton_attempts) < _MAX_RECORDED_SKELETON_ATTEMPTS:
                recorded_attempt = {
                    "goal_target": goal.target,
                    "expression": rendered,
                    "accepted": checked.accepted,
                    "generated_subgoals": len(checked.generated_goals),
                }
                self.stats.skeleton_attempts.append(recorded_attempt)
            else:
                self.stats.skeleton_attempts_omitted += 1
            if (
                not checked.accepted
                or checked.child_state is None
                or checked.generated_goals
            ):
                if observations is not None and cached is None:
                    observations.attempts[rendered] = (checked, None)
                if is_head:
                    head_outcomes[rendered] = None
                    release_deferred_heads()
                continue
            if obligations is None:
                obligations = self.session.internal_obligation_counts(
                    checked.child_state
                )
                self.stats.completion_queries += 1
            if observations is not None and cached is None:
                observations.attempts[rendered] = (checked, obligations)
            if recorded_attempt is not None:
                recorded_attempt["internal_obligations"] = list(obligations)
            if all(
                current <= previous
                for current, previous in zip(obligations, baseline, strict=True)
            ):
                return (
                    ConstructorSolution(
                        checked.child_state,
                        ProofPlan(rendered),
                    ),
                )
            unresolved = sum(
                max(0, current - previous)
                for current, previous in zip(obligations, baseline, strict=True)
            )
            if is_head:
                head_outcomes[rendered] = unresolved
            next_credit = progress_credit + max(0, estimated_unresolved - unresolved)
            if is_head:
                deferred_heads.append((skeleton, unresolved, next_credit))
                release_deferred_heads()
                continue
            expand(skeleton, unresolved, next_credit)
        return ()

    def solve(self, root_goal: GoalInfo) -> tuple[ConstructorSolution, ...]:
        results: list[ConstructorSolution] = []
        seen: set[str] = set()
        state = self.session.current_state()
        scoped = self._read_scoped_premises(state, root_goal)
        if scoped is not None or isinstance(self.session, ScopeDeclarationSession):
            if scoped is not None:
                root_catalog = scoped.declarations()
            else:
                assert isinstance(self.session, ScopeDeclarationSession)
                root_catalog, queries = visible_scope_declarations(
                    self.session, state, root_goal
                )
                self.stats.premise_catalog_queries += queries
            # Child interaction goals do not carry source-level module-scope
            # metadata.  The root catalogue is nevertheless valid throughout
            # this transactional refinement tree, whose actions only add
            # locals.  Reusing it preserves imported projections and other
            # declarations instead of silently shrinking to the current
            # module's textual prefix.
            self._scope_catalog = root_catalog
            self._has_ready_nonrecursive_eliminators = any(
                premise_eliminator_source_domains(type_text)
                for _name, type_text in root_catalog
            )
            if scoped is not None:
                self._rank_scoped_premises(state, root_goal, scoped)
                root_actions = self._scoped_actions[(state, root_goal.goal_id)].through(
                    64
                )
            else:
                root_actions = rank_scope_premises(
                    root_goal, root_catalog, excluded_names=self.excluded_premises
                )
            self._focused_visible_eliminators = tuple(
                (action.expression, domains)
                for action in root_actions
                if (domains := premise_independent_result_domains(action.type_text))
            )[:8]
        for solution in self._solve_goal(state, root_goal.goal_id, 0, frozenset()):
            try:
                rendered = solution.proof_text
            except ValueError:
                continue
            if rendered in seen:
                continue
            if self.require_recursive_call and not solution.plan.recursive_call_count:
                continue
            seen.add(rendered)
            if isinstance(self.session, InternalObligationSession):
                obligations = self.session.internal_obligation_counts(solution.state)
                self.stats.completion_queries += 1
                if any(
                    current > baseline
                    for current, baseline in zip(
                        obligations, self._baseline_internal_obligations, strict=True
                    )
                ):
                    self.stats.incomplete_solutions_pruned += 1
                    continue
            results.append(solution)
            if len(results) >= self.solution_limit:
                break
        return tuple(results)


def constructor_tree_prove(
    session: TransactionalKernelSession,
    root_goal: GoalInfo,
    *,
    action_budget: int,
    timeout_seconds: float,
    max_depth: int | None,
    solution_limit: int = 1,
    focused_model: SparsePolicyRanker | None = None,
    refinement_model: SparsePolicyRanker | None = None,
    policy_router: ORPolicyRouter | None = None,
    excluded_premises: frozenset[str] = frozenset(),
    defer_concrete_premises: bool = False,
    recursive_call: RecursiveCallSpec | None = None,
    preferred_constructor_arity: int | None = None,
    require_recursive_call: bool = False,
) -> ConstructorResult:
    """Enumerate checked structural-tree inhabitants in one Agda session.

    ``defer_concrete_premises`` is an orchestration hint: a concrete nullary
    scrutinee returns control before global-premise expansion so the caller can
    try batched cases first. Calling again with the default restores the full
    premise fallback; the hint never removes a kernel action permanently.
    """

    started = time.monotonic()
    stats = ConstructorStats(depth_limit=max_depth)
    if action_budget <= 0 or timeout_seconds <= 0 or solution_limit <= 0:
        return ConstructorResult(
            "resource-exhausted",
            (),
            stats,
            "constructor search budget exhausted",
        )
    search = _ConstructorSearch(
        session,
        action_budget=action_budget,
        deadline=started + timeout_seconds,
        max_depth=max_depth,
        solution_limit=solution_limit,
        focused_model=focused_model,
        refinement_model=refinement_model,
        policy_router=policy_router,
        excluded_premises=excluded_premises,
        defer_concrete_premises=defer_concrete_premises,
        recursive_call=recursive_call,
        preferred_constructor_arity=preferred_constructor_arity,
        require_recursive_call=require_recursive_call,
    )
    solutions = search.solve(root_goal)
    stats = search.stats
    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
    if search.focused_policy is not None:
        stats.focused["nnue_actions_scored"] = search.focused_policy.actions_scored
    if solutions:
        return ConstructorResult("solved", solutions, stats)
    if search.saw_exhaustion:
        return ConstructorResult(
            "resource-exhausted",
            (),
            stats,
            "constructor action, depth, or wall-time budget exhausted",
        )
    return ConstructorResult("no-proof", (), stats)
