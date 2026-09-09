"""Bounded, datatype-neutral synthesis of structurally recursive calls.

The search layer never exposes a recursive definition as an unrestricted
premise.  Instead it discovers possible smaller inhabitants from the live
case context, fully applies the recursive definition, and asks Agda to infer
the resulting type.  Agda's termination checker remains the authority when
the completed clauses are loaded.
"""

from __future__ import annotations

import itertools
import time
from dataclasses import dataclass

from .bridge.contracts import StateToken
from .contracts import ContextEntry, GoalInfo
from .focused import focused_candidates
from .kernel.protocol import TermInferenceSession, TransactionalKernelSession
from .notation import render_application
from .relation_path import explicit_arity
from .terms import render_term
from .type_syntax import (
    binder_domain,
    normalize_type_text,
    parse_named_binder,
    result_head,
    split_top_level_arrows,
)

RECURSIVE_CALL_SCHEMA_VERSION = "agdaprover.recursive-call.v1"
_MAX_SUBJECT_ACTIONS = 48
_MAX_SUBJECTS = 12
_MAX_ARGUMENTS_PER_POSITION = 12
_MAX_INFERENCE_QUERIES = 64
_MAX_EXPRESSION_BYTES = 4096


@dataclass(frozen=True)
class RecursiveCallSpec:
    """Search provenance for one definition currently being case-split."""

    root_name: str
    root_type: str
    recursive_domain: str
    allow_constructor_wrapping: bool = False
    argument_names: tuple[str, ...] = ()
    recursive_position: int | None = None
    structural_seeds: tuple[str, ...] = ()
    structural_dependencies: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if not self.root_name.strip():
            raise ValueError("recursive definition name cannot be empty")
        if not self.root_type.strip() or not self.recursive_domain.strip():
            raise ValueError("recursive call types cannot be empty")
        if self.recursive_position is not None and (
            self.recursive_position < 0
            or self.recursive_position >= len(self.argument_names)
        ):
            raise ValueError("recursive argument position lies outside its telescope")


@dataclass(frozen=True)
class RecursiveCallAction:
    """One fully applied recursive call accepted by observational inference."""

    expression: str
    inferred_type: str
    subject: str
    subject_origin: str

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": RECURSIVE_CALL_SCHEMA_VERSION,
            "tag": "apply-recursive-definition",
            "expression": self.expression,
            "inferred_type": self.inferred_type,
            "subject": self.subject,
            "subject_origin": self.subject_origin,
        }


@dataclass
class RecursiveCallStats:
    subject_search_actions: int = 0
    subject_inference_queries: int = 0
    subjects_generated: int = 0
    constructor_catalog_queries: int = 0
    constructor_wrappers_generated: int = 0
    applications_generated: int = 0
    inference_queries: int = 0
    applications_inferred: int = 0
    applications_pruned: int = 0
    composition_applications_generated: int = 0
    composition_inference_queries: int = 0
    composition_applications_inferred: int = 0

    def to_dict(self) -> dict[str, int]:
        return dict(self.__dict__)


def _explicit_domains(type_text: str) -> tuple[str, ...]:
    """Return displayed explicit domains, expanding grouped named binders."""

    domains: list[str] = []
    for part in split_top_level_arrows(type_text)[:-1]:
        binder = parse_named_binder(part)
        if binder is not None:
            if binder.visibility == "explicit":
                domains.extend((binder.domain,) * len(binder.names))
            continue
        stripped = part.lstrip()
        if stripped.startswith(("{", "⦃")):
            continue
        domains.append(binder_domain(part))
    return tuple(domains)


def _focused_subjects(
    goal: GoalInfo,
    domain: str,
    *,
    action_budget: int,
    deadline: float,
    extra_context: tuple[ContextEntry, ...] = (),
) -> tuple[tuple[str, ...], int]:
    remaining = deadline - time.monotonic()
    if remaining <= 0 or action_budget <= 0:
        return (), 0
    artificial = GoalInfo(
        goal.goal_id,
        domain,
        (*goal.context, *extra_context),
        goal.source_range,
    )
    result = focused_candidates(
        artificial,
        action_budget=min(action_budget, _MAX_SUBJECT_ACTIONS),
        solution_limit=_MAX_SUBJECTS,
        timeout_seconds=remaining,
        max_depth=4,
    )
    rendered = tuple(dict.fromkeys(render_term(term) for term in result.terms))
    return rendered, result.stats.actions_considered


def _first_explicit_domain(type_text: str) -> str | None:
    """Return the next displayed argument domain of a partial application."""

    try:
        parts = split_top_level_arrows(type_text)
    except ValueError:
        return None
    for part in parts[:-1]:
        try:
            parsed = parse_named_binder(part)
        except ValueError:
            # Agda may print adjacent implicit binders without arrows between
            # them (``{A : Set} {x : A} → ...``).  Such a combined display
            # segment contains no explicit argument, so skip it rather than
            # letting an observational proposal parser reject the live goal.
            if part.lstrip().startswith(("{", "⦃")):
                continue
            return None
        if parsed is not None:
            if parsed.visibility == "explicit":
                return parsed.domain
            continue
        if not part.lstrip().startswith(("{", "⦃")):
            try:
                return binder_domain(part)
            except ValueError:
                return None
    return None


def _observational_subjects(
    session: TermInferenceSession,
    state: StateToken,
    goal: GoalInfo,
    target_type: str,
    *,
    query_budget: int,
    deadline: float,
    structural_seeds: tuple[str, ...] = (),
    extra_terms: tuple[tuple[str, str], ...] = (),
) -> tuple[tuple[str, ...], int]:
    """Build a bounded closure of local applications using Agda's types.

    Dependent applications cannot be planned reliably from the printed
    telescope alone: after applying one argument, the next domain may be a
    substituted family.  This closure applies one local term at a time and
    asks Agda for the new type, so terms such as ``children (index a p)`` are
    discovered without recognizing either the family or its constructor.
    """

    if query_budget <= 0 or time.monotonic() >= deadline:
        return (), 0
    target = normalize_type_text(target_type)
    required_seeds = frozenset(structural_seeds)
    terms: list[tuple[str, str, int, bool]] = [
        (entry.name, entry.type, 0, not required_seeds or entry.name in required_seeds)
        for entry in goal.context
        if entry.in_scope and entry.name
    ]
    terms.extend(
        (expression, type_text, 0, False)
        for expression, type_text in extra_terms
        if expression not in {term[0] for term in terms}
    )
    expressions = {expression for expression, _type, _depth, _structural in terms}
    subjects = [
        expression
        for expression, type_text, _depth, structural in terms
        if structural and normalize_type_text(type_text) == target
    ]
    structural_proposals: list[str] = []

    def retained_subjects() -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                (
                    *subjects,
                    *(structural_proposals if required_seeds else ()),
                )
            )
        )[:_MAX_SUBJECTS]

    queries = 0
    for depth in range(1, 4):
        candidates: list[tuple[tuple[int, int, int, str, str], str, bool]] = []
        snapshot = tuple(terms)
        for head, head_type, head_depth, head_structural in snapshot:
            if head_depth >= depth:
                continue
            domain = _first_explicit_domain(head_type)
            if domain is None:
                continue
            domain_key = normalize_type_text(domain)
            domain_head = result_head(domain)
            for (
                argument,
                argument_type,
                argument_depth,
                argument_structural,
            ) in snapshot:
                if argument_depth >= depth or argument == head:
                    continue
                expression = render_application(head, (argument,))
                if expression in expressions:
                    continue
                candidates.append(
                    (
                        (
                            int(normalize_type_text(argument_type) != domain_key),
                            int(result_head(argument_type) != domain_head),
                            head_depth + argument_depth,
                            head,
                            argument,
                        ),
                        expression,
                        head_structural or argument_structural,
                    )
                )
        added = 0
        for _priority, expression, structural in sorted(candidates):
            if (
                queries >= query_budget
                or time.monotonic() >= deadline
                or len(terms) >= 48
            ):
                return retained_subjects(), queries
            if expression in expressions:
                continue
            expressions.add(expression)
            inferred = session.infer_type(
                state,
                goal_id=goal.goal_id,
                expression=expression,
            )
            queries += 1
            if inferred is None:
                continue
            terms.append((expression, inferred, depth, structural))
            added += 1
            if structural and required_seeds:
                # Pretty types may unfold a recursive-domain alias (for
                # example ``N`` to ``W A B``), so textual equality cannot be
                # the admission criterion for a derived structural subject.
                # Retain the bounded, observationally typed application as a
                # proposal; applying the recursive definition below asks
                # Agda whether it really inhabits the recursive position.
                structural_proposals.append(expression)
            if structural and normalize_type_text(inferred) == target:
                subjects.append(expression)
                if required_seeds:
                    return retained_subjects(), queries
                if len(subjects) >= _MAX_SUBJECTS:
                    return retained_subjects(), queries
        if not added:
            break
    return retained_subjects(), queries


def _contains_context_value(expression: str, goal: GoalInfo) -> bool:
    """Reject nullary/rebuilt constants when deriving a wrapped descendant."""

    return any(
        entry.in_scope
        and entry.name
        and entry.name in expression.replace("(", " ").replace(")", " ").split()
        for entry in goal.context
    )


def _argument_pool(
    goal: GoalInfo,
    expected_domain: str,
) -> tuple[str, ...]:
    """Return one bounded compatibility tier for an explicit argument.

    Once an exact displayed type is available, trying unrelated locals cannot
    improve that position and merely spends inference calls.  If pretty-name
    differences prevent exact matching, retain the result-head tier; only a
    complete absence of structural evidence falls back to the whole context.
    Agda still checks every selected argument.
    """

    expected = normalize_type_text(expected_domain)
    expected_head = result_head(expected_domain)
    locals_ = tuple(entry for entry in goal.context if entry.in_scope and entry.name)
    exact = tuple(
        entry.name for entry in locals_ if normalize_type_text(entry.type) == expected
    )
    same_head = tuple(
        entry.name
        for entry in locals_
        if entry.name not in exact and result_head(entry.type) == expected_head
    )
    fallback = tuple(
        entry.name
        for entry in locals_
        if entry.name not in exact and entry.name not in same_head
    )
    return (exact or same_head or fallback)[:_MAX_ARGUMENTS_PER_POSITION]


def generate_recursive_call_actions(
    session: TransactionalKernelSession,
    state: StateToken,
    goal: GoalInfo,
    spec: RecursiveCallSpec,
    *,
    query_budget: int,
    deadline: float,
    extra_terms: tuple[tuple[str, str], ...] = (),
) -> tuple[tuple[RecursiveCallAction, ...], RecursiveCallStats]:
    """Generate checked recursive applications without exposing ``root_name``.

    Direct descendants (including higher-order applications such as
    ``children index``) are preferred.  If a nested case split has exposed a
    smaller container, a unique constructor may wrap that smaller value; this
    derives the plane-tree ``node tail`` pattern without naming either type.
    """

    stats = RecursiveCallStats()
    if (
        query_budget <= 0
        or time.monotonic() >= deadline
        or not isinstance(session, TermInferenceSession)
    ):
        return (), stats

    recursive_domain = normalize_type_text(spec.recursive_domain)
    structural_seeds = frozenset(spec.structural_seeds)
    direct = tuple(
        entry.name
        for entry in goal.context
        if entry.in_scope
        and entry.name
        and (
            entry.name in structural_seeds
            or (
                not structural_seeds
                and normalize_type_text(entry.type) == recursive_domain
            )
        )
    )
    # Exact live inhabitants need no term search.  Reserving the finite
    # budget for typing their recursive applications is particularly
    # important after a nested split, where both a direct child and a child
    # rebuilt through a one-constructor container may be required.
    if direct or structural_seeds:
        actions = 0
    else:
        direct, actions = _focused_subjects(
            goal,
            spec.recursive_domain,
            action_budget=query_budget,
            deadline=deadline,
        )
    stats.subject_search_actions += actions
    structural_domains = tuple(
        domain
        for entry in goal.context
        if entry.in_scope and entry.name in structural_seeds
        for domain in (_first_explicit_domain(entry.type),)
        if domain is not None
    )
    plausible_structural_argument = any(
        normalize_type_text(entry.type) == normalize_type_text(domain)
        or result_head(entry.type) == result_head(domain)
        or (
            _first_explicit_domain(entry.type) is not None
            and result_head(entry.type) != result_head(domain)
            and result_head(split_top_level_arrows(entry.type)[-1])
            == result_head(domain)
        )
        for domain in structural_domains
        for entry in goal.context
        if entry.in_scope and entry.name not in structural_seeds
    )
    observational, subject_queries = (
        _observational_subjects(
            session,
            state,
            goal,
            spec.recursive_domain,
            query_budget=min(
                8 if structural_seeds else _MAX_INFERENCE_QUERIES,
                max(0, query_budget - stats.subject_search_actions),
            ),
            deadline=deadline,
            structural_seeds=spec.structural_seeds,
            extra_terms=extra_terms,
        )
        if (
            (
                not structural_seeds
                or not structural_domains
                or plausible_structural_argument
                or bool(extra_terms)
            )
            and (structural_seeds or not direct)
        )
        else ((), 0)
    )
    stats.subject_inference_queries += subject_queries
    direct = tuple(dict.fromkeys((*direct, *observational)))
    preferred_subject = (
        spec.argument_names[spec.recursive_position]
        if spec.recursive_position is not None
        and spec.recursive_position < len(spec.argument_names)
        else None
    )
    direct = (
        (
            preferred_subject,
            *(term for term in direct if term != preferred_subject),
        )
        if preferred_subject is not None and preferred_subject in direct
        else tuple(sorted(direct, key=lambda term: (len(term), term)))
    )
    subjects: list[tuple[str, str]] = [(term, "direct-descendant") for term in direct]

    # Rewrapping is useful only after a second, nested elimination.  It may be
    # needed alongside a direct child (for example both ``tree`` and
    # ``node forest`` in the cons branch of a plane tree), so retain both
    # origins and let sibling-aware constructor search distribute them.
    if spec.allow_constructor_wrapping:
        catalog = session.constructor_candidates(
            state,
            goal_id=goal.goal_id,
            type_head=result_head(spec.recursive_domain),
        )
        stats.constructor_catalog_queries += 1
        constructors = tuple(
            (name, type_text)
            for name, type_text in catalog
            if result_head(type_text) == result_head(spec.recursive_domain)
        )
        if len(constructors) == 1 and explicit_arity(constructors[0][1]) > 0:
            constructor_name, constructor_type = constructors[0]
            constructor_domains = _explicit_domains(constructor_type)
            constructor_pools = tuple(
                _argument_pool(goal, domain) for domain in constructor_domains
            )
            wrapped = (
                tuple(
                    render_application(constructor_name, arguments)
                    for arguments in itertools.islice(
                        itertools.product(*constructor_pools),
                        _MAX_SUBJECTS,
                    )
                )
                if constructor_pools and all(constructor_pools)
                else ()
            )
            if not wrapped:
                # Printed constructor domains can be obscured by dependent
                # aliases.  Retain the general symbolic fallback; the exact
                # structural path above handles ordinary records, W-types,
                # and nested one-constructor data without spending its term
                # search budget.
                wrapped, wrapped_actions = _focused_subjects(
                    goal,
                    spec.recursive_domain,
                    action_budget=max(0, query_budget - stats.subject_search_actions),
                    deadline=deadline,
                    extra_context=(
                        ContextEntry(constructor_name, constructor_type, True),
                    ),
                )
                stats.subject_search_actions += wrapped_actions
            for expression in wrapped:
                if expression != constructor_name and _contains_context_value(
                    expression, goal
                ):
                    subjects.append((expression, "one-constructor-wrapper"))
                    stats.constructor_wrappers_generated += 1

    subjects = list(dict.fromkeys(subjects))[:_MAX_SUBJECTS]
    stats.subjects_generated = len(subjects)
    if not subjects:
        return (), stats

    domains = _explicit_domains(spec.root_type)
    if len(domains) != explicit_arity(spec.root_type) or not domains:
        return (), stats
    recursive_head = result_head(spec.recursive_domain)
    recursive_positions = (
        (spec.recursive_position,)
        if spec.recursive_position is not None
        and len(spec.argument_names) == len(domains)
        else tuple(
            index
            for index, domain in enumerate(domains)
            if result_head(domain) == recursive_head
        )
    )
    if not recursive_positions:
        # Textual heads are only an ordering/filtering heuristic.  A dependent
        # alias can obscure the recursive position, so bounded inference may
        # still test every explicit position.
        recursive_positions = tuple(range(len(domains)))

    limit = min(
        max(
            0,
            query_budget
            - stats.subject_search_actions
            - stats.subject_inference_queries,
        ),
        _MAX_INFERENCE_QUERIES,
    )
    attempted: set[str] = set()
    actions_out: list[RecursiveCallAction] = []
    for subject, origin in subjects:
        for recursive_position in recursive_positions:
            pools: list[tuple[str, ...]] = []
            viable = True
            for index, domain in enumerate(domains):
                pool: tuple[str, ...]
                if index == recursive_position:
                    pool = (subject,)
                elif (
                    len(spec.argument_names) == len(domains)
                    and spec.argument_names[index]
                ):
                    # Preserve the arguments of the clause being proved.  A
                    # recursive call varies the structurally smaller
                    # position; permuting every same-typed local through all
                    # other positions is both rarely useful and exponential
                    # for algebraic laws over one carrier.
                    pool = (spec.argument_names[index],)
                else:
                    pool = _argument_pool(goal, domain)
                if not pool:
                    viable = False
                    break
                pools.append(pool)
            if not viable:
                stats.applications_pruned += 1
                continue
            for arguments in itertools.product(*pools):
                if stats.inference_queries >= limit or time.monotonic() >= deadline:
                    return tuple(actions_out), stats
                expression = render_application(spec.root_name, arguments)
                stats.applications_generated += 1
                if (
                    expression in attempted
                    or len(expression.encode("utf-8")) > _MAX_EXPRESSION_BYTES
                ):
                    stats.applications_pruned += 1
                    continue
                attempted.add(expression)
                inferred = session.infer_type(
                    state,
                    goal_id=goal.goal_id,
                    expression=expression,
                )
                stats.inference_queries += 1
                if inferred is None:
                    continue
                stats.applications_inferred += 1
                actions_out.append(
                    RecursiveCallAction(expression, inferred, subject, origin)
                )
    return tuple(actions_out), stats


def generate_recursive_compositions(
    session: TermInferenceSession,
    state: StateToken,
    goal: GoalInfo,
    recursive_actions: tuple[RecursiveCallAction, ...],
    declarations: tuple[tuple[str, str], ...],
    *,
    excluded_names: frozenset[str],
    query_budget: int,
    deadline: float,
) -> tuple[tuple[RecursiveCallAction, ...], RecursiveCallStats]:
    """Apply result-relevant visible functions around recursive results.

    This is the generic operation needed by the reverse rotating map: a
    recursive tree result is passed through the visible tree destructor to
    inhabit a forest field.  No declaration or datatype name is recognized.
    """

    stats = RecursiveCallStats()
    if query_budget <= 0 or time.monotonic() >= deadline:
        return (), stats
    target_head = result_head(goal.target)
    heads_list: list[tuple[str, str, tuple[str, ...]]] = []
    for name, type_text in declarations:
        if name in excluded_names or explicit_arity(type_text) not in {1, 2, 3}:
            continue
        try:
            if result_head(type_text) != target_head:
                continue
            domains = _explicit_domains(type_text)
        except ValueError:
            # Pretty-printed declarations outside the small syntax fragment
            # remain available to the ordinary kernel search path.
            continue
        heads_list.append((name, type_text, domains))
        if len(heads_list) >= 16:
            break
    heads = tuple(heads_list)
    attempted: set[str] = set()
    output: list[RecursiveCallAction] = []
    for recursive in recursive_actions:
        for name, _type_text, domains in heads:
            exact_positions = tuple(
                index
                for index, domain in enumerate(domains)
                if normalize_type_text(domain)
                == normalize_type_text(recursive.inferred_type)
            )
            structural_positions = tuple(
                index
                for index, domain in enumerate(domains)
                if result_head(domain) == result_head(recursive.inferred_type)
            )
            # Composition is an optional accelerator around an already typed
            # recursive result. With no displayed domain evidence, probing
            # every argument of every visible declaration is overwhelmingly
            # noise; ordinary premise refinement remains the bounded fallback
            # for aliases or hidden conversions.
            recursive_positions = exact_positions or structural_positions
            if not recursive_positions:
                continue
            for recursive_position in recursive_positions:
                pools: list[tuple[str, ...]] = []
                viable = True
                for index, domain in enumerate(domains):
                    pool = (
                        (recursive.expression,)
                        if index == recursive_position
                        else _argument_pool(goal, domain)
                    )
                    if not pool:
                        viable = False
                        break
                    pools.append(pool)
                if not viable:
                    continue
                for arguments in itertools.product(*pools):
                    if (
                        stats.composition_inference_queries >= query_budget
                        or time.monotonic() >= deadline
                    ):
                        return tuple(output), stats
                    expression = render_application(name, arguments)
                    stats.composition_applications_generated += 1
                    if (
                        expression in attempted
                        or len(expression.encode("utf-8")) > _MAX_EXPRESSION_BYTES
                    ):
                        stats.applications_pruned += 1
                        continue
                    attempted.add(expression)
                    inferred = session.infer_type(
                        state,
                        goal_id=goal.goal_id,
                        expression=expression,
                    )
                    stats.composition_inference_queries += 1
                    if inferred is None:
                        continue
                    stats.composition_applications_inferred += 1
                    output.append(
                        RecursiveCallAction(
                            expression,
                            inferred,
                            recursive.subject,
                            f"visible-composition:{recursive.subject_origin}",
                        )
                    )
    return tuple(output), stats
