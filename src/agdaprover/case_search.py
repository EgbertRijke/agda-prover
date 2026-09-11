"""Batched case analysis with datatype-neutral recursive result lifting.

The public Agda interaction protocol returns source clauses for case splits.
Applying one clause at a time makes a complete finite case tree pay one module
load per internal node.  This specialist queries every independent leaf in a
level against the same loaded source state, applies the disjoint edits as one
batch, and lets the next Agda load validate the complete level.
"""

from __future__ import annotations

import re
import tempfile
import time
from collections.abc import Callable
from contextlib import ExitStack
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Literal

from .actions import RefinementCandidate
from .bridge.contracts import StateToken
from .constructor_search import (
    ConstructorResult,
    ConstructorStats,
    constructor_tree_prove,
)
from .contracts import GoalInfo
from .dependency_planner import DependencyPlan, build_dependency_plan
from .focused import focused_prove
from .kernel.p0 import AgdaLoadError, AgdaSession, open_kernel_session
from .kernel.protocol import (
    KernelSession,
    KernelSessionFactory,
    ScopeDeclarationSession,
    TermInferenceSession,
    TransactionalKernelSession,
)
from .notation import (
    binary_mixfix_head,
    binary_mixfix_notation,
    render_application,
    strip_outer_parentheses,
)
from .observability.policy_trace import PolicyChoice
from .or_policy import ORPolicyRouter, PolicyCandidate, policy_candidate
from .premise_search import (
    ScopePremiseAction,
    premise_application_context_score,
    premise_independent_result_domains,
    premise_relation_endpoint_applications,
    premise_relation_evidence_applications,
    premise_relation_evidence_arity,
    premise_relation_function_arity,
    premise_relation_ground_applications,
    premise_result_application,
    premise_result_overlap,
    rank_scope_premises,
)
from .presentation import (
    apply_source_edit,
    guided_clause_region,
    reconstruct_case_split,
    reconstruct_guided_completion,
    reconstruct_hole_completion,
    reconstruct_intro_as_clause,
)
from .project import attach_module_scope
from .project_configuration import ProjectConfiguration
from .ranking.protocol import SparsePolicyRanker
from .reasoning.classifications import (
    StructuralClassification,
    classify_structural_scheduling,
    has_relational_context_evidence,
    is_higher_order_structural_field,
    is_reflexive_relation_target,
    reorders_homogeneous_coordinates,
)
from .recursive_calls import (
    RecursiveCallAction,
    RecursiveCallSpec,
    generate_recursive_call_actions,
)
from .recursive_elimination import (
    ContextualRelationEvidence,
    common_outer_relation_context,
    common_unary_relation_context,
    recursive_action_lifting_edit,
    recursive_clause_lhs,
    recursive_relation_closure_edit,
    recursive_result_lifting_edit,
    reflexive_family_constructors,
    unary_recursive_clause,
)
from .relation_path import RelationView, explicit_arity, parse_relation
from .retrieval_stats import ScopedRetrievalStats
from .scope_catalog import visible_scope_declarations
from .terms import render_term
from .type_syntax import (
    binder_domain,
    normalize_type_text,
    parse_named_binder,
    result_head,
    split_adjacent_binders,
    split_top_level_arrows,
    top_level_arrow_count,
)
from .verification import (
    ValidationError,
    prepare_project_overlay,
    validate_reconstruction,
)
from .zero_constructor import generate_zero_constructor_actions

CASE_BATCH_ALGORITHM = "kernel-guided-level-batched-cases-v2"
_HOLE = re.compile(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])")
_INTERNAL_META = re.compile(r"_[^\s(){}]+_\d+")
_MAX_RECORDED_PREMISE_ATTEMPTS = 64
_MAX_RECORDED_SKELETON_ATTEMPTS = 64
_MAX_RECORDED_ELIMINATION_ACTIONS = 64


@dataclass
class CaseBatchStats(ScopedRetrievalStats):
    algorithm: str = CASE_BATCH_ALGORITHM
    states_expanded: int = 0
    levels_completed: int = 0
    goal_inspections: int = 0
    actions_considered: int = 0
    actions_generated: int = 0
    refinement_queries: int = 0
    constructor_queries: int = 0
    case_queries: int = 0
    case_lookahead_queries: int = 0
    case_lookahead_loads: int = 0
    case_lookahead_elapsed_ms: float = 0.0
    proof_checks: int = 0
    constructor_catalog_queries: int = 0
    premise_catalog_queries: int = 0
    premise_queries: int = 0
    premise_refinement_queries: int = 0
    premise_candidates: int = 0
    premise_attempts: list[dict[str, object]] = field(default_factory=list)
    premise_attempts_omitted: int = 0
    completion_queries: int = 0
    incomplete_solutions_pruned: int = 0
    structural_leaf_attempts: int = 0
    structural_leaf_closures: int = 0
    generated_subgoals: int = 0
    deterministic_refinements: int = 0
    local_closures: int = 0
    result_determined_premise_queries: int = 0
    result_determined_premise_closures: int = 0
    relation_saturation_queries: int = 0
    relation_saturation_edges: int = 0
    relation_saturation_actions: list[dict[str, object]] = field(default_factory=list)
    zero_constructor_candidates: int = 0
    zero_constructor_closures: int = 0
    zero_candidate_validation_checks: int = 0
    # Compatibility counter retained for the P0 editor/result schema.
    induction_proposals: int = 0
    recursive_lift_proposals: int = 0
    recursive_lift_clauses: int = 0
    recursive_lift_inference_queries: int = 0
    recursive_lift_inference_failures: int = 0
    recursive_lift_family_candidates: int = 0
    recursive_function_abstractions: int = 0
    recursive_function_lift_queries: int = 0
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
    local_refinement_candidates: int = 0
    local_refinement_queries: int = 0
    evidence_inference_queries: int = 0
    evidence_terms: int = 0
    evidence_path_queries: int = 0
    skeleton_queries: int = 0
    skeleton_candidates: int = 0
    skeleton_frontier_peak: int = 0
    skeleton_attempts: list[dict[str, object]] = field(default_factory=list)
    skeleton_attempts_omitted: int = 0
    constructor_orders: list[dict[str, object]] = field(default_factory=list)
    recursive_actions: list[dict[str, object]] = field(default_factory=list)
    dependency_towers_built: int = 0
    dependency_planning_fallbacks: int = 0
    dependency_guided_splits: int = 0
    max_dependency_depth: int = 0
    proof_relevant_nodes_observed: int = 0
    parallel_inhabitants_observed: int = 0
    elimination_actions: list[dict[str, object]] = field(default_factory=list)
    elimination_actions_omitted: int = 0
    kernel_loads: int = 0
    kernel_load_elapsed_ms: float = 0.0
    model_calls: int = 0
    model_batches: int = 0
    model_elapsed_ms: float = 0.0
    focused: dict[str, int | float] = field(default_factory=dict)
    source_bytes_materialized: int = 0
    source_bytes_written: int = 0
    max_depth: int = 0
    depth_limit: int | None = None
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict[str, object]:
        return self.stats_dict()


@dataclass(frozen=True)
class CaseBatchResult:
    status: Literal["solved", "no-proof", "resource-exhausted"]
    patch: dict[str, object] | None
    proof_text: str | None
    stats: CaseBatchStats
    diagnostic: str = ""
    policy_choices: tuple[PolicyChoice, ...] = ()


def _safe_arrow_count(target: str) -> int:
    try:
        return top_level_arrow_count(target)
    except ValueError:
        return 0


def _safe_result_head(target: str) -> str:
    try:
        return result_head(target)
    except ValueError:
        return ""


def _first_explicit_domain(type_text: str) -> str | None:
    """Return the first displayed explicit domain of a live Agda type."""

    try:
        parts = split_top_level_arrows(type_text)
    except ValueError:
        return None
    for part in parts[:-1]:
        try:
            parsed = parse_named_binder(part)
        except ValueError:
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


def _surface_head(expression: str) -> str:
    """Return the outer prefix head of one displayed term, if present."""

    terms = _top_level_terms(strip_outer_parentheses(expression))
    return strip_outer_parentheses(terms[0]) if terms else ""


def _root_name(source: str, root_goal: GoalInfo) -> str | None:
    region_start, _region_end = guided_clause_region(source, root_goal)
    hole_start = root_goal.source_range[0] - 1
    prefix = source[region_start:hole_start]
    equals = prefix.rfind("=")
    if equals < 0:
        return None
    lhs = prefix[:equals].strip()
    return lhs.split()[0] if lhs else None


def _top_level_terms(text: str) -> tuple[str, ...]:
    """Split an Agda clause application at top-level whitespace."""

    terms: list[str] = []
    start: int | None = None
    stack: list[str] = []
    pairs = {")": "(", "}": "{", "]": "[", "⟩": "⟨"}
    for index, character in enumerate(text):
        if character in "({[⟨":
            stack.append(character)
        elif character in pairs:
            if not stack or stack[-1] != pairs[character]:
                return ()
            stack.pop()
        if character.isspace() and not stack:
            if start is not None:
                terms.append(text[start:index])
                start = None
        elif start is None:
            start = index
    if stack:
        return ()
    if start is not None:
        terms.append(text[start:])
    return tuple(terms)


def _application_subterms(text: str, *, limit: int = 48) -> tuple[str, ...]:
    """Return a bounded preorder of displayed application subterms.

    The terms are only an observational proposal pool.  In particular, this
    parser does not decide whether a token is a function, constructor, or
    inhabitant; subsequent Agda inference supplies that authority.
    """

    found: list[str] = []

    def visit(expression: str) -> None:
        if len(found) >= limit:
            return
        stripped = strip_outer_parentheses(expression.strip())
        if not stripped or stripped in found:
            return
        found.append(stripped)
        parts = _top_level_terms(stripped)
        if len(parts) <= 1:
            return
        operator_positions = tuple(
            index
            for index, part in enumerate(parts)
            if not any(
                character.isspace() for character in strip_outer_parentheses(part)
            )
            and any(
                not (character.isalnum() or character in "_′₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹.-")
                for character in strip_outer_parentheses(part)
            )
        )
        if operator_positions:
            start = 0
            for position in operator_positions:
                if start < position:
                    visit(" ".join(parts[start:position]))
                visit(parts[position])
                start = position + 1
            if start < len(parts):
                visit(" ".join(parts[start:]))
            return
        for part in parts:
            visit(part)

    visit(text)
    return tuple(found)


def _outer_argument_context(left: str, right: str, variable: str) -> str | None:
    """Recover a shared outer application with one differing final argument."""

    left_terms = _top_level_terms(strip_outer_parentheses(left))
    right_terms = _top_level_terms(strip_outer_parentheses(right))
    if (
        len(left_terms) < 2
        or len(left_terms) != len(right_terms)
        or left_terms[:-1] != right_terms[:-1]
        or left_terms[-1] == right_terms[-1]
    ):
        return None
    return " ".join((*left_terms[:-1], variable))


def _lambda_body(expression: str) -> str | None:
    """Return the body of one displayed lambda, preserving surface syntax."""

    stripped = strip_outer_parentheses(expression)
    if not stripped.startswith("λ ") or "→" not in stripped:
        return None
    _binders, body = stripped.split("→", 1)
    return body.strip() or None


def _nested_outer_contexts(
    left: str,
    right: str,
    variable: str,
    *,
    max_depth: int = 3,
) -> tuple[str, ...]:
    """Peel shared applications separated by function-valued arguments."""

    contexts: list[str] = []
    current_left = left
    current_right = right
    for _depth in range(max_depth):
        context = _outer_argument_context(current_left, current_right, variable)
        if context is None:
            break
        left_terms = _top_level_terms(strip_outer_parentheses(current_left))
        right_terms = _top_level_terms(strip_outer_parentheses(current_right))
        left_body = _lambda_body(left_terms[-1]) if left_terms else None
        right_body = _lambda_body(right_terms[-1]) if right_terms else None
        if left_body is None or right_body is None:
            break
        contexts.append(f"(λ {variable} → {context})")
        current_left = left_body
        current_right = right_body
    return tuple(contexts)


def _clause_arguments(lhs: str, root_name: str) -> tuple[str, ...]:
    """Recover explicit argument expressions from Agda's generated LHS."""

    stripped = lhs.strip()
    if stripped == root_name:
        return ()
    if stripped.startswith(root_name) and (
        len(stripped) == len(root_name) or stripped[len(root_name)].isspace()
    ):
        return _top_level_terms(stripped[len(root_name) :].strip())
    notation = binary_mixfix_notation(root_name)
    terms = _top_level_terms(stripped)
    if notation is not None:
        positions = tuple(
            index
            for index, term in enumerate(terms)
            if term == notation.surface_operator
        )
        if len(positions) == 1 and 0 < positions[0] < len(terms) - 1:
            operator = positions[0]
            return (
                " ".join(terms[:operator]),
                " ".join(terms[operator + 1 :]),
            )
    return ()


def _clause_recursive_specs(
    source: str,
    goal: GoalInfo,
    *,
    root_name: str,
    root_type: str,
) -> tuple[RecursiveCallSpec, ...]:
    """Derive structurally smaller calls from constructor patterns in a LHS.

    There may be several nested induction coordinates.  They are alternatives
    for this leaf, not one global choice for the whole case tree: a proof of a
    binary law can reduce either argument in different branches.
    """

    lhs = recursive_clause_lhs(source, goal)
    if lhs is None:
        return ()
    arguments = _clause_arguments(lhs, root_name)
    if not arguments or len(arguments) != explicit_arity(root_type):
        return ()
    try:
        root_parts = split_top_level_arrows(root_type)
    except ValueError:
        return ()
    root_domains: list[str] = []
    for part in root_parts[:-1]:
        try:
            parsed = parse_named_binder(part)
        except ValueError:
            parsed = None
        if parsed is not None:
            if parsed.visibility == "explicit":
                root_domains.extend(parsed.domain for _name in parsed.names)
            continue
        if part.lstrip().startswith(("{", "⦃")):
            continue
        try:
            root_domains.append(binder_domain(part))
        except ValueError:
            return ()
    if len(root_domains) != len(arguments):
        return ()

    context_types = {
        entry.name: entry.type
        for entry in goal.context
        if entry.in_scope and entry.name
    }
    descendants_by_position: dict[int, tuple[tuple[str, str], ...]] = {}
    for index, argument in enumerate(arguments):
        descendants = [
            (name, domain)
            for name, domain in context_types.items()
            if strip_outer_parentheses(argument) != name
            and re.search(rf"(?<![\w'-]){re.escape(name)}(?![\w'-])", argument)
        ]
        if descendants:
            descendants_by_position[index] = tuple(dict.fromkeys(descendants))
    all_position_descendants = tuple(
        descendant
        for position_descendants in descendants_by_position.values()
        for descendant in position_descendants
    )
    specs: list[RecursiveCallSpec] = []
    for index, position_descendants in descendants_by_position.items():
        root_domain = root_domains[index]
        recursive_domain = normalize_type_text(root_domain)
        structurally_recursive = tuple(
            (name, domain)
            for name, domain in position_descendants
            if recursive_domain in normalize_type_text(domain)
        )
        if structurally_recursive:
            position_descendants = structurally_recursive
        for primary_descendant, field_domain in position_descendants:
            higher_order = normalize_type_text(field_domain) != recursive_domain
            function_structural_field = bool(
                higher_order
                and is_higher_order_structural_field(root_domain, field_domain)
            )
            proposal_domain = field_domain if function_structural_field else root_domain
            proposal_seeds = () if function_structural_field else (primary_descendant,)
            structural_dependencies = tuple(
                name
                for name, _domain in all_position_descendants
                if higher_order
                and name != primary_descendant
                and re.search(
                    rf"(?<![\w'-]){re.escape(name)}(?![\w'-])",
                    field_domain,
                )
            )
            for replace_all in (False, True):
                recursive_arguments = list(arguments)
                recursive_arguments[index] = primary_descendant
                if replace_all:
                    for other, other_descendants in descendants_by_position.items():
                        if other != index:
                            recursive_arguments[other] = other_descendants[0][0]
                specs.append(
                    RecursiveCallSpec(
                        root_name=root_name,
                        root_type=root_type,
                        recursive_domain=(
                            proposal_domain if higher_order else field_domain
                        ),
                        argument_names=tuple(recursive_arguments),
                        recursive_position=index,
                        structural_seeds=proposal_seeds if higher_order else (),
                        structural_dependencies=(
                            () if function_structural_field else structural_dependencies
                        ),
                    )
                )
                # A size-decreasing call over homogeneous coordinates may
                # transpose the smaller inhabitant with one clause argument.
                # This bounded O(n²) family covers structural symmetries
                # without permuting every local through every position.  It
                # is only proposal generation: Agda's termination checker is
                # the authority on whether the resulting call graph descends.
                if reorders_homogeneous_coordinates(root_type) and len(
                    root_domains
                ) == len(recursive_arguments):
                    for other_index, other_domain in enumerate(root_domains):
                        if other_index == index or normalize_type_text(
                            other_domain
                        ) != normalize_type_text(root_domains[index]):
                            continue
                        transposed = list(recursive_arguments)
                        transposed[index], transposed[other_index] = (
                            transposed[other_index],
                            transposed[index],
                        )
                        specs.append(
                            RecursiveCallSpec(
                                root_name=root_name,
                                root_type=root_type,
                                recursive_domain=(
                                    proposal_domain if higher_order else field_domain
                                ),
                                argument_names=tuple(transposed),
                                recursive_position=other_index,
                                structural_seeds=(
                                    proposal_seeds if higher_order else ()
                                ),
                                structural_dependencies=(
                                    ()
                                    if function_structural_field
                                    else structural_dependencies
                                ),
                            )
                        )
    return tuple(dict.fromkeys(specs))


def _apply_disjoint_edits(
    source: str, edits: list[dict[str, object]]
) -> tuple[str, int]:
    def edit_start(edit: dict[str, object]) -> int:
        source_range = edit["source_range"]
        if not isinstance(source_range, list) or not source_range:
            raise TypeError("case edit has no source range")
        start = source_range[0]
        if not isinstance(start, int):
            raise TypeError("case edit range start is not an integer")
        return start

    ordered = sorted(edits, key=edit_start)
    previous_end = 0
    delta = 0
    for edit in ordered:
        source_range = edit.get("source_range")
        if (
            not isinstance(source_range, list)
            or len(source_range) != 2
            or not all(isinstance(value, int) for value in source_range)
        ):
            raise TypeError("case edit source range must contain two integers")
        start, end = source_range
        if start <= 0 or end <= start or end - 1 > len(source):
            raise ValueError("case edit source range lies outside the source")
        if start < previous_end:
            raise ValueError("batched case edits overlap")
        previous_end = end
        original = edit.get("original")
        replacement = edit.get("replacement")
        if not isinstance(original, str) or not isinstance(replacement, str):
            raise TypeError("case edit text fields must be strings")
        if source[start - 1 : end - 1] != original:
            raise ValueError("case edit original does not match the source range")
        delta += len(replacement) - len(original)
    result = source
    for edit in reversed(ordered):
        result = apply_source_edit(result, edit)
    return result, delta


def batched_case_prove(
    source_file: Path,
    root_goal: GoalInfo,
    *,
    action_budget: int,
    timeout_seconds: float,
    max_depth: int | None,
    focused_model: SparsePolicyRanker | None,
    refinement_model: SparsePolicyRanker | None,
    policy_router: ORPolicyRouter | None = None,
    session_factory: KernelSessionFactory = AgdaSession,
    project_configuration: ProjectConfiguration | None = None,
    session: KernelSession | None = None,
    initial_goals: tuple[GoalInfo, ...] | None = None,
    allow_exact_local: bool = True,
    preferred_root_position: int | None = None,
    recursive_program_profile: Literal["unary-recursive", "binary-recursive"]
    | None = None,
    recursive_composition_local_first: bool = False,
    on_statistics: Callable[[CaseBatchStats], None] | None = None,
) -> CaseBatchResult:
    """Solve a finite case tree one complete coverage level at a time.

    Publish completed-work statistics once on every exit, including exceptions.
    As for constructor search, the observer only aggregates in-memory counters;
    it must not perform budgeted work or change exception handling.
    """

    started = time.monotonic()
    stats = CaseBatchStats(depth_limit=max_depth)
    try:
        return _batched_case_prove(
            source_file,
            root_goal,
            action_budget=action_budget,
            timeout_seconds=timeout_seconds,
            max_depth=max_depth,
            focused_model=focused_model,
            refinement_model=refinement_model,
            policy_router=policy_router,
            session_factory=session_factory,
            project_configuration=project_configuration,
            session=session,
            initial_goals=initial_goals,
            allow_exact_local=allow_exact_local,
            preferred_root_position=preferred_root_position,
            recursive_program_profile=recursive_program_profile,
            recursive_composition_local_first=recursive_composition_local_first,
            started=started,
            stats=stats,
        )
    finally:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        if on_statistics is not None:
            on_statistics(stats)


def _batched_case_prove(
    source_file: Path,
    root_goal: GoalInfo,
    *,
    action_budget: int,
    timeout_seconds: float,
    max_depth: int | None,
    focused_model: SparsePolicyRanker | None,
    refinement_model: SparsePolicyRanker | None,
    policy_router: ORPolicyRouter | None,
    session_factory: KernelSessionFactory,
    project_configuration: ProjectConfiguration | None,
    session: KernelSession | None,
    initial_goals: tuple[GoalInfo, ...] | None,
    allow_exact_local: bool,
    preferred_root_position: int | None,
    recursive_program_profile: Literal["unary-recursive", "binary-recursive"] | None,
    recursive_composition_local_first: bool,
    started: float,
    stats: CaseBatchStats,
) -> CaseBatchResult:
    deadline = started + timeout_seconds
    original_source = source_file.read_text()
    active_policy = policy_router or ORPolicyRouter(
        focused_model=focused_model,
        refinement_model=refinement_model,
        budget_envelope={
            "max_actions": action_budget,
            "max_depth": max_depth,
            "timeout_seconds": timeout_seconds,
        },
    )

    def rank_policy(
        goal: GoalInfo,
        candidates: tuple[PolicyCandidate, ...],
        *,
        classification: StructuralClassification | None = None,
    ) -> tuple[PolicyCandidate, ...]:
        before_items = active_policy.model_items_scored
        before_batches = active_policy.model_batches
        before_elapsed = active_policy.model_elapsed_ms
        ranked = active_policy.rank(goal, candidates, classification=classification)
        stats.model_calls += active_policy.model_items_scored - before_items
        stats.model_batches += active_policy.model_batches - before_batches
        stats.model_elapsed_ms += active_policy.model_elapsed_ms - before_elapsed
        return ranked.candidates

    def rank_recursive_actions(
        goal: GoalInfo,
        actions: tuple[RecursiveCallAction, ...],
        *,
        classification: StructuralClassification | None = None,
    ) -> tuple[RecursiveCallAction, ...]:
        symbolic = tuple(dict.fromkeys(actions))
        by_expression = {action.expression: action for action in symbolic}
        ranked = rank_policy(
            goal,
            tuple(
                policy_candidate(
                    family="recursive-call",
                    tag="apply-recursive-definition",
                    expression=action.expression,
                    type_text=action.inferred_type,
                    symbolic_key=(
                        action.subject_origin != "direct-descendant",
                        action.expression,
                    ),
                    metadata=(("subject-origin", action.subject_origin),),
                )
                for action in symbolic
            ),
            classification=classification,
        )
        return tuple(by_expression[candidate.expression] for candidate in ranked)

    def no_proof(diagnostic: str) -> CaseBatchResult:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return CaseBatchResult("no-proof", None, None, stats, diagnostic)

    try:
        region_start, initial_end = guided_clause_region(original_source, root_goal)
    except ValueError as error:
        return no_proof(str(error))
    root_name = _root_name(original_source, root_goal)
    try:
        root_parts = split_top_level_arrows(root_goal.target)
    except ValueError:
        root_parts = (root_goal.target,)
    root_domain: str | None = None
    if len(root_parts) == 2 and _safe_arrow_count(root_goal.target) == 1:
        try:
            root_domain = binder_domain(root_parts[0])
        except ValueError:
            pass

    def available(count: int = 1) -> bool:
        return (
            count > 0
            and stats.actions_considered + count <= action_budget
            and time.monotonic() < deadline
        )

    current_source = original_source
    committed_choices: list[PolicyChoice] = []
    current_end = initial_end
    depth = 0
    case_split_seen = False
    recursive_call: RecursiveCallSpec | None = None
    recursive_split_depth: int | None = None
    recursive_baseline_context_size: int | None = None
    scope_catalog: tuple[tuple[str, str], ...] | None = None
    constructor_catalogs: dict[str, tuple[tuple[str, str], ...]] = {}

    def record_structural_stats(nested: ConstructorStats) -> None:
        stats.merge_retrieval(nested)
        stats.actions_considered += nested.actions_considered
        stats.actions_generated += nested.actions_generated
        stats.refinement_queries += (
            nested.constructor_queries + nested.premise_refinement_queries
        )
        stats.constructor_queries += nested.constructor_queries
        stats.constructor_catalog_queries += nested.catalog_queries
        stats.premise_catalog_queries += nested.premise_catalog_queries
        stats.premise_queries += nested.premise_queries
        stats.premise_refinement_queries += nested.premise_refinement_queries
        stats.premise_candidates += nested.premise_candidates
        stats.evidence_inference_queries += nested.evidence_inference_queries
        stats.evidence_terms += nested.evidence_terms
        stats.evidence_path_queries += nested.evidence_path_queries
        remaining_premise_slots = max(
            0, _MAX_RECORDED_PREMISE_ATTEMPTS - len(stats.premise_attempts)
        )
        retained_premise_attempts = nested.premise_attempts[:remaining_premise_slots]
        stats.premise_attempts.extend(retained_premise_attempts)
        stats.premise_attempts_omitted += (
            nested.premise_attempts_omitted
            + len(nested.premise_attempts)
            - len(retained_premise_attempts)
        )
        stats.completion_queries += nested.completion_queries
        stats.incomplete_solutions_pruned += nested.incomplete_solutions_pruned
        stats.recursive_subject_search_actions += (
            nested.recursive_subject_search_actions
        )
        stats.recursive_subject_inference_queries += (
            nested.recursive_subject_inference_queries
        )
        stats.recursive_subjects_generated += nested.recursive_subjects_generated
        stats.recursive_catalog_queries += nested.recursive_catalog_queries
        stats.recursive_wrappers_generated += nested.recursive_wrappers_generated
        stats.recursive_applications_generated += (
            nested.recursive_applications_generated
        )
        stats.recursive_inference_queries += nested.recursive_inference_queries
        stats.recursive_applications_inferred += nested.recursive_applications_inferred
        stats.recursive_applications_pruned += nested.recursive_applications_pruned
        stats.recursive_compositions_generated += (
            nested.recursive_compositions_generated
        )
        stats.recursive_composition_inference_queries += (
            nested.recursive_composition_inference_queries
        )
        stats.recursive_compositions_inferred += nested.recursive_compositions_inferred
        stats.recursive_proof_checks += nested.recursive_proof_checks
        stats.local_refinement_candidates += nested.local_refinement_candidates
        stats.local_refinement_queries += nested.local_refinement_queries
        stats.refinement_queries += nested.local_refinement_queries
        stats.skeleton_queries += nested.skeleton_queries
        stats.skeleton_candidates += nested.skeleton_candidates
        stats.skeleton_frontier_peak = max(
            stats.skeleton_frontier_peak, nested.skeleton_frontier_peak
        )
        remaining_skeleton_slots = max(
            0, _MAX_RECORDED_SKELETON_ATTEMPTS - len(stats.skeleton_attempts)
        )
        retained_skeleton_attempts = nested.skeleton_attempts[:remaining_skeleton_slots]
        stats.skeleton_attempts.extend(retained_skeleton_attempts)
        stats.skeleton_attempts_omitted += (
            nested.skeleton_attempts_omitted
            + len(nested.skeleton_attempts)
            - len(retained_skeleton_attempts)
        )
        remaining_order_slots = max(0, 64 - len(stats.constructor_orders))
        stats.constructor_orders.extend(
            nested.constructor_orders[:remaining_order_slots]
        )
        remaining_recursive_slots = max(0, 64 - len(stats.recursive_actions))
        stats.recursive_actions.extend(
            nested.recursive_actions[:remaining_recursive_slots]
        )
        stats.proof_checks += nested.proof_checks
        stats.generated_subgoals += nested.generated_subgoals
        stats.goal_inspections += nested.goal_inspections
        stats.model_calls += nested.model_calls
        stats.model_batches += nested.model_batches
        stats.model_elapsed_ms += nested.model_elapsed_ms
        for name, value in nested.focused.items():
            stats.focused[name] = stats.focused.get(name, 0) + value

    def record_elimination_action(action: dict[str, object]) -> None:
        if len(stats.elimination_actions) < _MAX_RECORDED_ELIMINATION_ACTIONS:
            stats.elimination_actions.append(action)
        else:
            stats.elimination_actions_omitted += 1

    def construct_leaf(
        leaf_session: TransactionalKernelSession,
        leaf: GoalInfo,
        *,
        leaf_depth: int,
        recursive_spec: RecursiveCallSpec | None,
        allow_wrapping: bool,
        preferred_arity: int | None,
        case_alternatives_remain: bool,
    ) -> ConstructorResult:
        """Share one construction boundary before or after case probing."""
        stats.structural_leaf_attempts += 1
        structural_budget = action_budget - stats.actions_considered
        if case_alternatives_remain:
            # Construction must leave room for another informative split.
            # If Agda has rejected every split, the leaf instead owns the
            # remaining allowance; refusing to split is not refusing to prove.
            recursive_codomain_head = (
                _safe_result_head(split_top_level_arrows(recursive_spec.root_type)[-1])
                if recursive_spec is not None
                else ""
            )
            structural_slice = (
                64
                if recursive_spec is not None
                and _safe_result_head(leaf.target) == recursive_codomain_head
                else 32
            )
            structural_budget = min(structural_slice, structural_budget)
        return constructor_tree_prove(
            leaf_session,
            leaf,
            action_budget=structural_budget,
            timeout_seconds=max(0.001, deadline - time.monotonic()),
            max_depth=None if max_depth is None else max_depth - leaf_depth,
            solution_limit=1,
            focused_model=focused_model,
            refinement_model=refinement_model,
            policy_router=active_policy,
            excluded_premises=(
                frozenset((root_name,)) if root_name is not None else frozenset()
            ),
            recursive_call=(
                replace(recursive_spec, allow_constructor_wrapping=allow_wrapping)
                if recursive_spec is not None
                else None
            ),
            preferred_constructor_arity=preferred_arity,
            on_statistics=record_structural_stats,
        )

    def case_successor_score(edit: dict[str, object]) -> tuple[int, int, int, int]:
        """Classify one singleton case successor with bounded kernel evidence.

        Local reuse preserves more computation than a constructor-normal leaf;
        both are preferable to a successor requiring another elimination.  A
        fresh throwaway session makes this observational and branch-safe.
        """

        lookahead_started = time.monotonic()
        stats.case_lookahead_queries += 1
        try:
            successor_source = apply_source_edit(current_source, edit)
            source_range = edit["source_range"]
            replacement = edit["replacement"]
            if not isinstance(source_range, list) or len(source_range) != 2:
                return (4, 4, 0, 0)
            if not isinstance(replacement, str):
                return (4, 4, 0, 0)
            successor_start = int(source_range[0]) - 1
            successor_end = successor_start + len(replacement)
            with tempfile.TemporaryDirectory(
                prefix="agdaprover-case-lookahead-"
            ) as lookahead_directory:
                lookahead_workspace = prepare_project_overlay(
                    source_file,
                    successor_source,
                    Path(lookahead_directory),
                    project_configuration=project_configuration,
                    timeout_seconds=deadline - time.monotonic(),
                )
                lookahead_path = lookahead_workspace.source_file
                materialized = lookahead_workspace.total_bytes
                stats.source_bytes_materialized += materialized
                stats.source_bytes_written += materialized
                with open_kernel_session(
                    session_factory,
                    project_configuration=lookahead_workspace.configuration,
                    timeout_seconds=max(0.001, deadline - time.monotonic()),
                    deadline=deadline,
                ) as lookahead_session:
                    load_started = time.monotonic()
                    loaded = lookahead_session.load_module(lookahead_path)
                    stats.kernel_loads += 1
                    stats.case_lookahead_loads += 1
                    stats.kernel_load_elapsed_ms += (
                        time.monotonic() - load_started
                    ) * 1000.0
                    successors = tuple(
                        goal
                        for goal in loaded
                        if successor_start <= goal.source_range[0] - 1
                        and goal.source_range[1] - 1 <= successor_end
                    )
                    if not successors:
                        return (0, 0, 0, 0)

                    # Score a whole constructor fan-out, rather than giving
                    # up as soon as a split has two branches.  The best
                    # induction variable is often exactly the one for which
                    # a nullary branch computes to normal form while a
                    # recursive branch remains.  This observation is fully
                    # datatype-neutral and comes from fresh Agda goals.
                    hard = 0
                    constructor_normal = 0
                    complexity = 0
                    for shallow_successor in successors:
                        successor = lookahead_session.inspect_goal(shallow_successor)
                        stats.goal_inspections += 1
                        if any(
                            entry.in_scope
                            and entry.name
                            and normalize_type_text(entry.type)
                            == normalize_type_text(successor.target)
                            for entry in successor.context
                        ):
                            continue
                        stats.refinement_queries += 1
                        refined = lookahead_session.check_refinement(
                            successor.goal_id, ""
                        )
                        if (
                            refined.accepted
                            and refined.preview is not None
                            and _HOLE.search(refined.preview) is None
                        ):
                            constructor_normal += 1
                            continue
                        hard += 1
                        complexity += len(normalize_type_text(successor.target))
                    return (
                        hard,
                        constructor_normal,
                        complexity,
                        len(successors),
                    )
        except (AgdaLoadError, OSError, TypeError, ValueError):
            return (4, 4, 0, 0)
        finally:
            stats.case_lookahead_elapsed_ms += (
                time.monotonic() - lookahead_started
            ) * 1000.0

    def candidate_closes_leaf(edit: dict[str, object]) -> bool:
        """Confirm a tentative closed term with independent batch validation."""

        try:
            stats.proof_checks += 1
            stats.zero_candidate_validation_checks += 1
            with tempfile.TemporaryDirectory(
                prefix="agdaprover-zero-candidate-"
            ) as validation_directory:
                validation_workspace = prepare_project_overlay(
                    source_file,
                    current_source,
                    Path(validation_directory),
                    project_configuration=project_configuration,
                    timeout_seconds=deadline - time.monotonic(),
                )
                validation_path = validation_workspace.source_file
                materialized = validation_workspace.total_bytes
                stats.source_bytes_materialized += materialized
                stats.source_bytes_written += materialized
                validation, _trust = validate_reconstruction(
                    validation_path,
                    edit,
                    agda_executable=active_session.executable,
                    agda_version=active_session.version,
                    project_configuration=validation_workspace.configuration,
                    timeout_seconds=max(0.001, deadline - time.monotonic()),
                )
            return bool(validation.get("checked") and not validation.get("timed_out"))
        except (AgdaLoadError, OSError, TypeError, ValidationError, ValueError):
            return False

    def candidate_closes_interaction_leaf(edit: dict[str, object]) -> bool:
        """Check one speculative clause without requiring every later hole.

        Loading the edited overlay asks Agda to elaborate the complete module,
        while inspecting only the edited source interval permits unrelated
        benchmark goals to remain open.  This is the appropriate validation
        boundary for a surface-ambiguous context proposal.
        """

        try:
            successor_source = apply_source_edit(current_source, edit)
            source_range = edit["source_range"]
            replacement = edit["replacement"]
            if not isinstance(source_range, list) or len(source_range) != 2:
                return False
            if not isinstance(replacement, str):
                return False
            successor_start = int(source_range[0]) - 1
            successor_end = successor_start + len(replacement)
            stats.proof_checks += 1
            with tempfile.TemporaryDirectory(
                prefix="agdaprover-context-candidate-"
            ) as validation_directory:
                validation_workspace = prepare_project_overlay(
                    source_file,
                    successor_source,
                    Path(validation_directory),
                    project_configuration=project_configuration,
                    timeout_seconds=deadline - time.monotonic(),
                )
                validation_path = validation_workspace.source_file
                materialized = validation_workspace.total_bytes
                stats.source_bytes_materialized += materialized
                stats.source_bytes_written += materialized
                with open_kernel_session(
                    session_factory,
                    project_configuration=validation_workspace.configuration,
                    timeout_seconds=max(0.001, deadline - time.monotonic()),
                    deadline=deadline,
                ) as validation_session:
                    load_started = time.monotonic()
                    try:
                        loaded = validation_session.load_module(validation_path)
                    finally:
                        stats.kernel_loads += 1
                        stats.kernel_load_elapsed_ms += (
                            time.monotonic() - load_started
                        ) * 1000.0
            return not any(
                successor_start <= successor.source_range[0] - 1
                and successor.source_range[1] - 1 <= successor_end
                for successor in loaded
            )
        except (AgdaLoadError, OSError, TypeError, ValueError):
            return False

    with ExitStack() as resources:
        if session is None:
            temporary = resources.enter_context(
                tempfile.TemporaryDirectory(prefix="agdaprover-case-batch-")
            )
            workspace = prepare_project_overlay(
                source_file,
                original_source,
                Path(temporary),
                project_configuration=project_configuration,
                timeout_seconds=deadline - time.monotonic(),
            )
            candidate_path, _overlay_files = workspace.source_file, workspace.files
            active_session = resources.enter_context(
                open_kernel_session(
                    session_factory,
                    project_configuration=workspace.configuration,
                    timeout_seconds=max(0.001, deadline - time.monotonic()),
                    deadline=deadline,
                )
            )
        else:
            if initial_goals is None:
                raise ValueError("a reused case session requires its loaded goals")
            candidate_path = source_file
            active_session = session

        def constructor_catalog(
            goal: GoalInfo,
            state: StateToken,
            type_head: str,
        ) -> tuple[tuple[str, str], ...]:
            """Read an immutable constructor family once per case batch."""

            cached = constructor_catalogs.get(type_head)
            if cached is not None:
                return cached
            if not isinstance(active_session, TransactionalKernelSession):
                return ()
            candidates = active_session.constructor_candidates(
                state,
                goal_id=goal.goal_id,
                type_head=type_head,
            )
            stats.constructor_catalog_queries += 1
            constructor_catalogs[type_head] = candidates
            return candidates

        def scope_declarations(
            current_goal: GoalInfo,
            state: StateToken,
        ) -> tuple[tuple[str, str], ...]:
            if not isinstance(active_session, ScopeDeclarationSession):
                return ()
            declarations, queries = visible_scope_declarations(
                active_session, state, current_goal
            )
            stats.premise_catalog_queries += queries
            return declarations

        try:
            while True:
                if time.monotonic() >= deadline:
                    raise TimeoutError("batched case search exhausted wall time")
                if max_depth is not None and depth > max_depth:
                    raise TimeoutError("batched case search exhausted depth")
                if depth == 0 and initial_goals is not None:
                    loaded = initial_goals
                else:
                    candidate_path.write_text(current_source)
                    encoded_size = len(current_source.encode("utf-8"))
                    stats.source_bytes_materialized += encoded_size
                    stats.source_bytes_written += encoded_size
                    load_started = time.monotonic()
                    try:
                        loaded = active_session.load_module(candidate_path)
                    except AgdaLoadError as error:
                        return no_proof(str(error))
                    finally:
                        stats.kernel_loads += 1
                        stats.kernel_load_elapsed_ms += (
                            time.monotonic() - load_started
                        ) * 1000.0
                stats.states_expanded += 1
                target_goals = tuple(
                    goal
                    for goal in loaded
                    if region_start <= goal.source_range[0] - 1
                    and goal.source_range[1] - 1 <= current_end
                )
                if not target_goals:
                    replacement = current_source[region_start:current_end]
                    patch = reconstruct_guided_completion(
                        original_source, root_goal, replacement
                    )
                    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                    return CaseBatchResult(
                        "solved",
                        patch,
                        replacement,
                        stats,
                        policy_choices=tuple(committed_choices),
                    )

                edits: list[dict[str, object]] = []
                level_choices: list[PolicyChoice] = []
                for shallow in sorted(target_goals, key=lambda goal: goal.source_range):
                    if not available():
                        raise TimeoutError(
                            "batched case search exhausted its action budget"
                        )
                    goal = attach_module_scope(
                        active_session.inspect_goal(shallow),
                        current_source,
                        source_file,
                    )
                    stats.goal_inspections += 1
                    scheduling_lhs = (
                        recursive_clause_lhs(current_source, goal)
                        if root_name is not None
                        else None
                    )
                    scheduling_arguments = (
                        _clause_arguments(scheduling_lhs, root_name)
                        if scheduling_lhs is not None and root_name is not None
                        else ()
                    )
                    unchanged_root_arguments = {
                        strip_outer_parentheses(argument)
                        for argument in scheduling_arguments
                        if len(_top_level_terms(strip_outer_parentheses(argument))) == 1
                    }
                    root_domain_heads: set[str] = set()
                    for part in root_parts[:-1]:
                        for group in split_adjacent_binders(part) or (part,):
                            if group.lstrip().startswith(("{", "⦃")):
                                continue
                            try:
                                root_domain_heads.add(
                                    _safe_result_head(binder_domain(group))
                                )
                            except ValueError:
                                continue
                    has_productive_elimination_candidate = any(
                        entry.in_scope
                        and entry.name
                        and (
                            entry.name in unchanged_root_arguments
                            or _safe_result_head(entry.type) not in root_domain_heads
                        )
                        for entry in goal.context
                    )
                    has_cross_carrier_elimination_candidate = any(
                        entry.in_scope
                        and entry.name
                        and _safe_result_head(entry.type) not in root_domain_heads
                        for entry in goal.context
                    )
                    prefer_productive_elimination = False
                    # Direct recursive closure is attempted before the wider
                    # relation graph below.  An unchanged theorem coordinate
                    # or exposed field from another carrier can still reveal
                    # genuine computation, so broad saturation is deferred.
                    # The case selector below always prefers fresh coordinates
                    # over constructor descendants; this gives a finite
                    # product-induction layer without following one tail
                    # indefinitely.

                    # A live one-constructor reflexive family cannot connect
                    # two visibly distinct constructors of the same carrier.
                    # Derive that conflict from both constructor catalogues;
                    # no relation or datatype name is privileged.  This turns
                    # an impossible branch into a dead state before global
                    # premise search recursively invents intermediates.
                    rigid_relation = parse_relation(goal.target)
                    if rigid_relation is not None and isinstance(
                        active_session, TransactionalKernelSession
                    ):
                        state = active_session.current_state()
                        rigid_relation_catalog = constructor_catalog(
                            goal,
                            state,
                            binary_mixfix_head(rigid_relation.operator),
                        )
                        relation_families = reflexive_family_constructors(
                            rigid_relation_catalog
                        )
                        if (
                            len(rigid_relation_catalog) == 1
                            and len(relation_families) == 1
                        ):
                            left_head = _surface_head(rigid_relation.left)
                            right_head = _surface_head(rigid_relation.right)
                            if left_head and right_head and left_head != right_head:
                                carrier_heads = tuple(
                                    dict.fromkeys(
                                        _safe_result_head(entry.type)
                                        for entry in goal.context
                                        if entry.in_scope
                                        and entry.name
                                        and _safe_result_head(entry.type)
                                    )
                                )
                                for carrier_head in carrier_heads[:8]:
                                    carrier_catalog = constructor_catalog(
                                        goal,
                                        state,
                                        carrier_head,
                                    )
                                    constructor_names = {
                                        name for name, _type in carrier_catalog
                                    }
                                    if {
                                        left_head,
                                        right_head,
                                    } <= constructor_names:
                                        return no_proof(
                                            "one-constructor relation has "
                                            "incompatible rigid indices"
                                        )

                    # Primitive-recursive program synthesis is a finite set of
                    # datatype-neutral schemas.  Constructors, recursion
                    # positions, and compositional operators all come from the
                    # current Agda interaction; the profile only chooses which
                    # structural schema this joint-search alternative explores.
                    program_edit: dict[str, object] | None = None
                    program_choices: tuple[PolicyChoice, ...] = ()
                    recursive_program_actions: list[RecursiveCallAction] = []
                    program_specs = (
                        _clause_recursive_specs(
                            current_source,
                            goal,
                            root_name=root_name,
                            root_type=root_goal.target,
                        )
                        if recursive_program_profile is not None
                        and case_split_seen
                        and root_name is not None
                        else ()
                    )
                    live_context_names = {
                        entry.name
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    }
                    unresolved_program_dependencies = bool(
                        recursive_program_profile is not None
                        and any(
                            dependency not in live_context_names
                            for program_spec in program_specs
                            for dependency in program_spec.structural_dependencies
                        )
                    )
                    if (
                        recursive_program_profile is not None
                        and case_split_seen
                        and isinstance(active_session, TransactionalKernelSession)
                    ):
                        state = active_session.current_state()
                        if (
                            not program_specs
                            and recursive_program_profile == "unary-recursive"
                            and root_name is not None
                            and preferred_root_position is not None
                        ):
                            current_lhs = recursive_clause_lhs(current_source, goal)
                            current_arguments = (
                                _clause_arguments(current_lhs, root_name)
                                if current_lhs is not None
                                else ()
                            )
                            for index, argument in enumerate(current_arguments):
                                if index == preferred_root_position or not available():
                                    continue
                                candidate = strip_outer_parentheses(argument)
                                stats.actions_considered += 1
                                stats.actions_generated += 1
                                stats.proof_checks += 1
                                checked_parameter = active_session.check_candidate(
                                    goal.goal_id, candidate
                                )
                                if checked_parameter.accepted:
                                    program_edit = reconstruct_hole_completion(
                                        current_source, goal, candidate
                                    )
                                    break
                        if (
                            program_edit is None
                            and program_specs
                            and isinstance(active_session, TermInferenceSession)
                        ):
                            for program_spec in program_specs:
                                generated, generated_stats = (
                                    generate_recursive_call_actions(
                                        active_session,
                                        state,
                                        goal,
                                        program_spec,
                                        query_budget=min(
                                            8,
                                            action_budget - stats.actions_considered,
                                        ),
                                        deadline=deadline,
                                    )
                                )
                                stats.recursive_subject_search_actions += (
                                    generated_stats.subject_search_actions
                                )
                                stats.recursive_subject_inference_queries += (
                                    generated_stats.subject_inference_queries
                                )
                                stats.recursive_subjects_generated += (
                                    generated_stats.subjects_generated
                                )
                                stats.recursive_catalog_queries += (
                                    generated_stats.constructor_catalog_queries
                                )
                                stats.recursive_applications_generated += (
                                    generated_stats.applications_generated
                                )
                                stats.recursive_inference_queries += (
                                    generated_stats.inference_queries
                                )
                                stats.recursive_applications_inferred += (
                                    generated_stats.applications_inferred
                                )
                                stats.recursive_applications_pruned += (
                                    generated_stats.applications_pruned
                                )
                                stats.actions_considered += (
                                    generated_stats.subject_search_actions
                                    + generated_stats.subject_inference_queries
                                    + generated_stats.inference_queries
                                )
                                stats.actions_generated += (
                                    generated_stats.applications_generated
                                )
                                recursive_program_actions.extend(
                                    rank_recursive_actions(
                                        goal,
                                        generated,
                                        classification=(
                                            classify_structural_scheduling(
                                                recursive_result_head_matches_goal=any(
                                                    _safe_result_head(
                                                        action.inferred_type
                                                    )
                                                    == _safe_result_head(goal.target)
                                                    for action in generated
                                                ),
                                                structural_descent_available=bool(
                                                    generated
                                                ),
                                                dependencies_ready=(
                                                    not unresolved_program_dependencies
                                                ),
                                                reflexive_relation_target=(
                                                    is_reflexive_relation_target(
                                                        goal.target
                                                    )
                                                ),
                                                relational_elimination_available=(
                                                    has_relational_context_evidence(
                                                        goal.target,
                                                        tuple(
                                                            entry.type
                                                            for entry in goal.context
                                                            if entry.in_scope
                                                            and entry.name
                                                        ),
                                                    )
                                                ),
                                            )
                                        ),
                                    )
                                )
                            for recursive_action in recursive_program_actions:
                                active_policy.mark(
                                    "recursive-call", recursive_action.expression
                                )
                            wrappers: list[str] = []
                            if recursive_program_profile == "unary-recursive":
                                catalog = constructor_catalog(
                                    goal,
                                    state,
                                    _safe_result_head(goal.target),
                                )
                                unary = tuple(
                                    name
                                    for name, type_text in catalog
                                    if _safe_result_head(type_text)
                                    == _safe_result_head(goal.target)
                                    and explicit_arity(type_text) == 1
                                )
                                wrappers.extend(
                                    render_application(
                                        constructor,
                                        (recursive_action.expression,),
                                    )
                                    for recursive_action in recursive_program_actions
                                    for constructor in unary
                                )
                            else:
                                if isinstance(active_session, ScopeDeclarationSession):
                                    if scope_catalog is None:
                                        scope_catalog = scope_declarations(goal, state)
                                    actions = rank_scope_premises(
                                        goal,
                                        scope_catalog,
                                        excluded_names=(
                                            frozenset((root_name,))
                                            if root_name is not None
                                            else frozenset()
                                        ),
                                    )
                                    binary_heads = tuple(
                                        action
                                        for action in actions
                                        if explicit_arity(action.type_text) == 2
                                        and _safe_result_head(action.type_text)
                                        == _safe_result_head(goal.target)
                                    )
                                    carrier_locals = tuple(
                                        entry.name
                                        for entry in goal.context
                                        if entry.in_scope
                                        and entry.name
                                        and normalize_type_text(entry.type)
                                        == normalize_type_text(goal.target)
                                    )
                                    preferred_locals = tuple(
                                        strip_outer_parentheses(argument)
                                        for spec in program_specs
                                        for index, argument in enumerate(
                                            spec.argument_names
                                        )
                                        if index != spec.recursive_position
                                        and strip_outer_parentheses(argument)
                                        in carrier_locals
                                    )
                                    carrier_locals = tuple(
                                        dict.fromkeys(
                                            (*preferred_locals, *carrier_locals)
                                        )
                                    )
                                    wrappers.extend(
                                        expression
                                        for recursive_action in recursive_program_actions
                                        for action in binary_heads[:8]
                                        for local in carrier_locals
                                        for expression in (
                                            (
                                                render_application(
                                                    action.expression,
                                                    (
                                                        local,
                                                        recursive_action.expression,
                                                    ),
                                                ),
                                                render_application(
                                                    action.expression,
                                                    (
                                                        recursive_action.expression,
                                                        local,
                                                    ),
                                                ),
                                            )
                                            if recursive_composition_local_first
                                            else (
                                                render_application(
                                                    action.expression,
                                                    (
                                                        recursive_action.expression,
                                                        local,
                                                    ),
                                                ),
                                                render_application(
                                                    action.expression,
                                                    (
                                                        local,
                                                        recursive_action.expression,
                                                    ),
                                                ),
                                            )
                                        )
                                    )
                            for expression in tuple(dict.fromkeys(wrappers))[:16]:
                                if not available():
                                    break
                                stats.actions_considered += 1
                                stats.actions_generated += 1
                                stats.proof_checks += 1
                                checked_program = active_session.check_candidate(
                                    goal.goal_id, expression
                                )
                                if checked_program.accepted:
                                    program_edit = reconstruct_hole_completion(
                                        current_source, goal, expression
                                    )
                                    break
                            # A recursive result can occur under an arbitrary
                            # constructor telescope, including a dependent
                            # function field such as the children of a W-node.
                            # Let the ordinary structural engine assemble that
                            # telescope, but accept only a plan whose provenance
                            # contains a kernel-inferred recursive call.  This
                            # generalizes unary constructor wrapping without
                            # recognizing any datatype or field name.
                            if (
                                program_edit is None
                                and program_specs
                                and not unresolved_program_dependencies
                                and not any(
                                    entry.in_scope
                                    and entry.name
                                    and _safe_arrow_count(entry.type)
                                    and _safe_result_head(entry.type)
                                    == _safe_result_head(goal.target)
                                    for entry in goal.context
                                )
                            ):
                                structural_program_specs = tuple(
                                    dict.fromkeys(
                                        (
                                            *(
                                                (recursive_call,)
                                                if recursive_call
                                                else ()
                                            ),
                                            *program_specs,
                                        )
                                    )
                                )
                                for program_spec in structural_program_specs:
                                    if not available():
                                        break
                                    structural_program = constructor_tree_prove(
                                        active_session,
                                        goal,
                                        action_budget=min(
                                            32,
                                            action_budget - stats.actions_considered,
                                        ),
                                        timeout_seconds=max(
                                            0.001, deadline - time.monotonic()
                                        ),
                                        max_depth=(
                                            None
                                            if max_depth is None
                                            else max_depth - depth
                                        ),
                                        solution_limit=1,
                                        focused_model=focused_model,
                                        refinement_model=refinement_model,
                                        policy_router=active_policy,
                                        excluded_premises=(
                                            frozenset((root_name,))
                                            if root_name is not None
                                            else frozenset()
                                        ),
                                        recursive_call=program_spec,
                                        require_recursive_call=True,
                                        on_statistics=record_structural_stats,
                                    )
                                    if structural_program.solutions:
                                        program_edit = reconstruct_hole_completion(
                                            current_source,
                                            goal,
                                            structural_program.solutions[0].proof_text,
                                        )
                                        program_choices = structural_program.solutions[
                                            0
                                        ].plan.choices_on_proof()
                                        break
                        elif recursive_program_profile == "binary-recursive":
                            # A nullary result constructor is a base-case
                            # completion only after every exposed constructor
                            # field has been consumed.  Closing earlier loses
                            # the shape of nested inductive fields (for
                            # example, a one-constructor tree whose field is a
                            # list) and commits the whole definition to a
                            # constant program.  This criterion is entirely
                            # structural: records, W-types, and arbitrary
                            # nested inductive families receive the same
                            # treatment.
                            current_lhs = (
                                recursive_clause_lhs(current_source, goal)
                                if root_name is not None
                                else None
                            )
                            current_arguments = (
                                _clause_arguments(current_lhs, root_name)
                                if current_lhs is not None and root_name is not None
                                else ()
                            )
                            unchanged_parameters = {
                                strip_outer_parentheses(argument)
                                for argument in current_arguments
                                if len(
                                    _top_level_terms(strip_outer_parentheses(argument))
                                )
                                == 1
                            }
                            exposed_fields = tuple(
                                entry.name
                                for entry in goal.context
                                if entry.in_scope
                                and entry.name
                                and entry.name not in unchanged_parameters
                            )
                            if exposed_fields:
                                catalog = ()
                            else:
                                catalog = constructor_catalog(
                                    goal,
                                    state,
                                    _safe_result_head(goal.target),
                                )
                            for constructor, type_text in catalog:
                                if (
                                    _safe_result_head(type_text)
                                    != _safe_result_head(goal.target)
                                    or explicit_arity(type_text) != 0
                                    or not available()
                                ):
                                    continue
                                stats.actions_considered += 1
                                stats.actions_generated += 1
                                stats.proof_checks += 1
                                checked_program = active_session.check_candidate(
                                    goal.goal_id, constructor
                                )
                                if checked_program.accepted:
                                    program_edit = reconstruct_hole_completion(
                                        current_source, goal, constructor
                                    )
                                    break
                    if program_edit is not None:
                        edits.append(program_edit)
                        level_choices.extend(program_choices)
                        continue

                    exact_local = next(
                        (
                            entry.name
                            for entry in reversed(goal.context)
                            if entry.in_scope
                            and entry.name
                            and normalize_type_text(entry.type)
                            == normalize_type_text(goal.target)
                        ),
                        None,
                    )
                    # ``allow_exact_local=False`` is used only to force an
                    # observed definition past its initial projection.  Once
                    # a genuine case split has happened, a local may be the
                    # structurally correct base/leaf result; continuing to
                    # suppress it makes ordinary recursive programs
                    # impossible to synthesize and sends the leaf into much
                    # more expensive global-premise search.
                    if (
                        exact_local is not None
                        and (allow_exact_local or case_split_seen)
                        and not unresolved_program_dependencies
                    ):
                        stats.actions_considered += 1
                        stats.actions_generated += 1
                        stats.local_closures += 1
                        edits.append(
                            reconstruct_hole_completion(
                                current_source, goal, exact_local
                            )
                        )
                        continue

                    arrow_goal = bool(_safe_arrow_count(goal.target))
                    if arrow_goal:
                        stats.actions_considered += 1
                        stats.actions_generated += 1
                        stats.refinement_queries += 1
                        checked = active_session.check_refinement(goal.goal_id, "")
                        if checked.accepted and checked.preview is not None:
                            stats.generated_subgoals += max(
                                1, checked.preview.count("?")
                            )
                            edits.append(
                                reconstruct_intro_as_clause(
                                    current_source, goal, checked.preview
                                )
                            )
                            continue

                    # A case split often leaves a purely implicational leaf.
                    # Close that fragment in memory before asking Agda for
                    # another structural split.  Generic eliminators (for
                    # example a declaration from an empty source into an
                    # arbitrary result) are discovered from the live scope;
                    # neither the source datatype nor the declaration name is
                    # built into this rule.
                    if case_split_seen and available():
                        if scope_catalog is None:
                            scope_catalog = (
                                scope_declarations(goal, active_session.current_state())
                                if isinstance(
                                    active_session, TransactionalKernelSession
                                )
                                else ()
                            )
                        leaf_actions = rank_scope_premises(
                            goal,
                            scope_catalog,
                            excluded_names=(
                                frozenset((root_name,))
                                if root_name is not None
                                else frozenset()
                            ),
                        )
                        eliminators = tuple(
                            (action.expression, domains)
                            for action in leaf_actions
                            if (
                                domains := premise_independent_result_domains(
                                    action.type_text
                                )
                            )
                        )[:8]
                        leaf_focused = focused_prove(
                            goal,
                            action_budget=min(
                                32, action_budget - stats.actions_considered
                            ),
                            timeout_seconds=max(0.001, deadline - time.monotonic()),
                            max_depth=(
                                None if max_depth is None else max_depth - depth
                            ),
                            branch_scorer=(
                                active_policy.score_focused
                                if active_policy.focused_policy is not None
                                else None
                            ),
                            eliminators=eliminators,
                        )
                        stats.actions_considered += (
                            leaf_focused.stats.actions_considered
                        )
                        stats.actions_generated += leaf_focused.stats.actions_generated
                        for name in (
                            "nodes_expanded",
                            "cache_hits",
                            "cycles_pruned",
                            "depth_pruned",
                        ):
                            stats.focused[name] = int(stats.focused.get(name, 0)) + int(
                                getattr(leaf_focused.stats, name)
                            )
                        if leaf_focused.term is not None and available():
                            expression = render_term(leaf_focused.term)
                            stats.actions_considered += 1
                            stats.actions_generated += 1
                            stats.proof_checks += 1
                            checked_leaf = active_session.check_candidate(
                                goal.goal_id, expression
                            )
                            if checked_leaf.accepted:
                                stats.local_closures += 1
                                edits.append(
                                    reconstruct_hole_completion(
                                        current_source, goal, expression
                                    )
                                )
                                continue

                    if (
                        not arrow_goal
                        and not unresolved_program_dependencies
                        and available()
                    ):
                        stats.actions_considered += 1
                        stats.actions_generated += 1
                        stats.refinement_queries += 1
                        checked = active_session.check_refinement(goal.goal_id, "")
                        if (
                            checked.accepted
                            and checked.preview is not None
                            and _HOLE.search(checked.preview) is None
                        ):
                            stats.deterministic_refinements += 1
                            stats.generated_subgoals += checked.preview.count("?")
                            edits.append(
                                reconstruct_hole_completion(
                                    current_source, goal, checked.preview
                                )
                            )
                            continue

                    zero_actions = generate_zero_constructor_actions(
                        goal,
                        max_actions=min(16, action_budget - stats.actions_considered),
                    )
                    stats.actions_generated += len(zero_actions)
                    stats.zero_constructor_candidates += len(zero_actions)
                    zero_edit: dict[str, object] | None = None
                    module_parameter_names = {
                        name
                        for parameter in (
                            goal.module_scope.parameters
                            if goal.module_scope is not None
                            else ()
                        )
                        for name in parameter.names
                    }
                    for zero_action in zero_actions:
                        if not available():
                            break
                        if (
                            zero_action.application_count == 0
                            and zero_action.scrutinee.tag == "local"
                            and zero_action.scrutinee.name not in module_parameter_names
                        ):
                            # Ordinary locals are handled by the complete case
                            # action set below. The let/absurd fallback exists
                            # only because Agda refuses interactive splitting
                            # on parameters lifted from a module telescope.
                            continue
                        stats.actions_considered += 1
                        stats.proof_checks += 1
                        checked_zero = active_session.check_candidate(
                            goal.goal_id, zero_action.expression
                        )
                        if not checked_zero.accepted:
                            continue
                        proposed_zero_edit = reconstruct_hole_completion(
                            current_source, goal, zero_action.expression
                        )
                        if not candidate_closes_leaf(proposed_zero_edit):
                            continue
                        zero_edit = proposed_zero_edit
                        stats.zero_constructor_closures += 1
                        record_elimination_action(zero_action.to_dict())
                        break
                    if zero_edit is not None:
                        edits.append(zero_edit)
                        continue

                    recursive_clause = unary_recursive_clause(
                        current_source,
                        goal,
                        root_name=root_name,
                        root_domain=root_domain,
                    )
                    if recursive_clause is not None:
                        stats.recursive_lift_clauses += 1

                    # General recursive lifting is driven by the current
                    # clause and inferred recursive-call type.  Unlike the
                    # original unary shortcut, it works for a theorem with
                    # any number of fixed parameters: only the argument that
                    # Agda just structurally reduced is changed.
                    recursive_specs = (
                        _clause_recursive_specs(
                            current_source,
                            goal,
                            root_name=root_name,
                            root_type=root_goal.target,
                        )
                        if root_name is not None
                        else ()
                    )
                    if not recursive_specs and recursive_call is not None:
                        # A root coordinate that has already become a
                        # nullary constructor is a genuine base branch.  It
                        # has no structurally smaller call, so reusing the
                        # pre-split specification here would manufacture
                        # non-decreasing recursive applications and send the
                        # relation engine through an irrelevant saturation
                        # graph.  Preserve the fallback only while the
                        # anchored coordinate is still the original term
                        # (for example while eliminating a dependent field).
                        current_lhs = (
                            recursive_clause_lhs(current_source, goal)
                            if root_name is not None
                            else None
                        )
                        current_arguments = (
                            _clause_arguments(current_lhs, root_name)
                            if current_lhs is not None and root_name is not None
                            else ()
                        )
                        recursive_position = recursive_call.recursive_position
                        root_constructor_exposed = bool(
                            recursive_position is not None
                            and recursive_position < len(current_arguments)
                            and recursive_position < len(recursive_call.argument_names)
                            and normalize_type_text(
                                strip_outer_parentheses(
                                    current_arguments[recursive_position]
                                )
                            )
                            != normalize_type_text(
                                strip_outer_parentheses(
                                    recursive_call.argument_names[recursive_position]
                                )
                            )
                        )
                        if not root_constructor_exposed:
                            recursive_specs = (recursive_call,)
                    if recursive_specs and recursive_call is not None:
                        recursive_carrier = normalize_type_text(
                            recursive_call.recursive_domain
                        )
                        has_higher_order_descendant = any(
                            _first_explicit_domain(spec.recursive_domain) is not None
                            and normalize_type_text(
                                split_top_level_arrows(spec.recursive_domain)[-1]
                            )
                            == recursive_carrier
                            for spec in recursive_specs
                        )
                        if has_higher_order_descendant:
                            # A constructor field ``I → Carrier`` becomes a
                            # genuine smaller carrier only after structural
                            # search introduces ``I``.  Retain the original
                            # carrier-shaped recursion schema alongside the
                            # field-shaped observations so that this lambda
                            # introduction can expose the recursive call.  A
                            # nullary/base constructor has no such field and
                            # therefore does not regain a non-decreasing call.
                            recursive_specs = tuple(
                                dict.fromkeys((recursive_call, *recursive_specs))
                            )
                        # Several root coordinates may now expose smaller
                        # inhabitants.  The most recently selected structural
                        # coordinate is the active induction descent; try its
                        # recursive call before older coordinates.  Otherwise
                        # a locally valid but non-closing congruence proposal
                        # from the first telescope argument can pre-empt the
                        # call that actually computes in this branch.
                        active_recursive_position = recursive_call.recursive_position
                        recursive_specs = tuple(
                            sorted(
                                recursive_specs,
                                key=lambda spec: (
                                    spec.recursive_position
                                    != active_recursive_position,
                                    normalize_type_text(spec.recursive_domain)
                                    != recursive_carrier,
                                    spec.recursive_position
                                    if spec.recursive_position is not None
                                    else len(root_parts),
                                ),
                            )
                        )
                    if recursive_specs:
                        recursive_specs = tuple(
                            replace(
                                spec,
                                allow_constructor_wrapping=(
                                    spec.allow_constructor_wrapping
                                    or (
                                        recursive_split_depth is not None
                                        and depth >= recursive_split_depth + 2
                                    )
                                ),
                            )
                            for spec in recursive_specs
                        )
                    if (
                        recursive_specs
                        and isinstance(active_session, TermInferenceSession)
                        and isinstance(active_session, TransactionalKernelSession)
                        and available()
                    ):
                        state = active_session.current_state()
                        target_relation = parse_relation(goal.target)
                        clause_lhs = recursive_clause_lhs(current_source, goal)
                        lifted_edit: dict[str, object] | None = None
                        recursive_results: list[tuple[str, str]] = []
                        contextual_relation_evidence: tuple[
                            ContextualRelationEvidence, ...
                        ] = ()
                        recursive_subject_terms: list[str] = []
                        rewrite_declarations: tuple[tuple[str, str], ...] = ()
                        closure_carrier_constructors: list[str] = []
                        closure_carrier_type: str | None = None
                        family_candidates: tuple[tuple[str, str], ...] = ()
                        if target_relation is not None:
                            relation_views = tuple(
                                dict.fromkeys(
                                    (
                                        target_relation,
                                        *(
                                            candidate
                                            for token in _top_level_terms(goal.target)[
                                                1:-1
                                            ]
                                            for candidate in (
                                                parse_relation(
                                                    goal.target,
                                                    expected_operator=token,
                                                ),
                                            )
                                            if candidate is not None
                                        ),
                                    )
                                )
                            )
                            for relation_view in relation_views:
                                try:
                                    relation_head = binary_mixfix_head(
                                        relation_view.operator
                                    )
                                except ValueError:
                                    continue
                                candidate_catalog = constructor_catalog(
                                    goal,
                                    state,
                                    relation_head,
                                )
                                candidate_families = reflexive_family_constructors(
                                    candidate_catalog
                                )
                                if candidate_families:
                                    target_relation = relation_view
                                    family_candidates = candidate_families
                                    break
                            stats.recursive_lift_family_candidates += len(
                                family_candidates
                            )
                        context_type_by_name = {
                            entry.name: entry.type
                            for entry in goal.context
                            if entry.in_scope and entry.name
                        }
                        has_function_structural_seed = any(
                            _first_explicit_domain(context_type_by_name.get(seed, ""))
                            is not None
                            for recursive_spec in recursive_specs
                            for seed in recursive_spec.structural_seeds
                        )
                        recursive_index_terms: tuple[tuple[str, str], ...] = ()
                        if has_function_structural_seed:
                            if scope_catalog is None:
                                scope_catalog = scope_declarations(goal, state)
                            recursive_index_terms = tuple(
                                (name, type_text)
                                for name, type_text in scope_catalog
                                if explicit_arity(type_text) == 0
                            )[:12]
                        for recursive_spec in recursive_specs:
                            if lifted_edit is not None or not available():
                                break
                            recursive_actions, recursive_stats = (
                                generate_recursive_call_actions(
                                    active_session,
                                    state,
                                    goal,
                                    recursive_spec,
                                    query_budget=min(
                                        8,
                                        action_budget - stats.actions_considered,
                                    ),
                                    deadline=deadline,
                                    extra_terms=recursive_index_terms,
                                )
                            )
                            recursive_actions = rank_recursive_actions(
                                goal,
                                recursive_actions,
                                classification=classify_structural_scheduling(
                                    recursive_result_head_matches_goal=any(
                                        _safe_result_head(action.inferred_type)
                                        == _safe_result_head(goal.target)
                                        for action in recursive_actions
                                    ),
                                    structural_descent_available=bool(
                                        recursive_actions
                                    ),
                                    dependencies_ready=(
                                        not unresolved_program_dependencies
                                    ),
                                    reflexive_relation_target=(
                                        is_reflexive_relation_target(goal.target)
                                    ),
                                    relational_elimination_available=(
                                        has_relational_context_evidence(
                                            goal.target,
                                            tuple(
                                                entry.type
                                                for entry in goal.context
                                                if entry.in_scope and entry.name
                                            ),
                                        )
                                    ),
                                ),
                            )
                            stats.recursive_subject_search_actions += (
                                recursive_stats.subject_search_actions
                            )
                            stats.recursive_subject_inference_queries += (
                                recursive_stats.subject_inference_queries
                            )
                            stats.recursive_subjects_generated += (
                                recursive_stats.subjects_generated
                            )
                            stats.recursive_catalog_queries += (
                                recursive_stats.constructor_catalog_queries
                            )
                            stats.recursive_wrappers_generated += (
                                recursive_stats.constructor_wrappers_generated
                            )
                            stats.recursive_applications_generated += (
                                recursive_stats.applications_generated
                            )
                            stats.recursive_inference_queries += (
                                recursive_stats.inference_queries
                            )
                            stats.recursive_applications_inferred += (
                                recursive_stats.applications_inferred
                            )
                            stats.recursive_applications_pruned += (
                                recursive_stats.applications_pruned
                            )
                            stats.actions_considered += (
                                recursive_stats.subject_search_actions
                                + recursive_stats.subject_inference_queries
                                + recursive_stats.inference_queries
                            )
                            stats.actions_generated += (
                                recursive_stats.applications_generated
                            )
                            carrier_catalog = (
                                constructor_catalog(
                                    goal,
                                    state,
                                    _safe_result_head(recursive_spec.recursive_domain),
                                )
                                if target_relation is not None
                                and clause_lhs is not None
                                else ()
                            )
                            carrier_constructors = tuple(
                                name
                                for name, type_text in carrier_catalog
                                if _safe_result_head(type_text)
                                == _safe_result_head(recursive_spec.recursive_domain)
                                and explicit_arity(type_text) == 1
                            )
                            closure_carrier_type = (
                                closure_carrier_type or recursive_spec.recursive_domain
                            )
                            closure_carrier_constructors.extend(carrier_constructors)
                            for recursive_action in recursive_actions:
                                active_policy.mark(
                                    "recursive-call", recursive_action.expression
                                )
                                recursive_subject_terms.append(recursive_action.subject)
                                recursive_results.append(
                                    (
                                        recursive_action.expression,
                                        recursive_action.inferred_type,
                                    )
                                )
                                if len(stats.recursive_actions) < 64:
                                    stats.recursive_actions.append(
                                        {
                                            **recursive_action.to_dict(),
                                            "clause_arguments": list(
                                                recursive_spec.argument_names
                                            ),
                                            "recursive_position": (
                                                recursive_spec.recursive_position
                                            ),
                                        }
                                    )
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    for carrier_constructor in carrier_constructors:
                                        lifted_edit = recursive_action_lifting_edit(
                                            current_source,
                                            goal,
                                            clause_lhs=clause_lhs or "",
                                            carrier_type=(
                                                recursive_spec.recursive_domain
                                            ),
                                            recursive_expression=(
                                                recursive_action.expression
                                            ),
                                            recursive_result_type=(
                                                recursive_action.inferred_type
                                            ),
                                            relation_constructor=(relation_constructor),
                                            relation_operator=relation_operator,
                                            carrier_constructor=(carrier_constructor),
                                        )
                                        if lifted_edit is not None:
                                            break
                                    if lifted_edit is not None:
                                        break
                                if lifted_edit is not None:
                                    break
                        if (
                            lifted_edit is None
                            and target_relation is not None
                            and clause_lhs is not None
                            and _outer_argument_context(
                                target_relation.left,
                                target_relation.right,
                                "agdaprover-value",
                            )
                            is not None
                            and available()
                        ):
                            active_target_relation: RelationView = target_relation
                            # A recursive child can occur behind a function
                            # field (W-types are the canonical example).  Form
                            # the pointwise recursive call directly from the
                            # live structural seed, then offer it to any scoped
                            # one-argument principle whose domain is itself a
                            # function type.  This discovers extensionality-like
                            # rules from their telescope rather than their
                            # names.  A second generic evidence application
                            # lifts the resulting function relation into the
                            # target constructor/record context.
                            if scope_catalog is None:
                                scope_catalog = scope_declarations(goal, state)
                            higher_order_declarations = tuple(
                                dict.fromkeys(
                                    (
                                        *scope_catalog,
                                        *(
                                            (entry.name, entry.type)
                                            for entry in goal.context
                                            if entry.in_scope and entry.name
                                        ),
                                    )
                                )
                            )
                            scoped_actions = rank_scope_premises(
                                goal,
                                higher_order_declarations,
                                excluded_names=(
                                    frozenset((root_name,))
                                    if root_name is not None
                                    else frozenset()
                                ),
                            )
                            context_types = {
                                entry.name: entry.type
                                for entry in goal.context
                                if entry.in_scope and entry.name
                            }
                            function_evidence: list[tuple[str, str, int | None]] = []
                            grounded_function_evidence: tuple[
                                tuple[str, str, int | None], ...
                            ] = ()
                            attempted_abstractions: set[str] = set()
                            for recursive_spec in recursive_specs:
                                position = recursive_spec.recursive_position
                                if position is None or position >= len(
                                    recursive_spec.argument_names
                                ):
                                    continue
                                for seed in recursive_spec.structural_seeds:
                                    seed_type = context_types.get(seed)
                                    if seed_type is None:
                                        continue
                                    index_domain = _first_explicit_domain(seed_type)
                                    try:
                                        seed_codomain = split_top_level_arrows(
                                            seed_type
                                        )[-1]
                                    except ValueError:
                                        continue
                                    if index_domain is None or _safe_result_head(
                                        seed_codomain
                                    ) != _safe_result_head(
                                        recursive_spec.recursive_domain
                                    ):
                                        continue
                                    index_name = "agdaprover-index"
                                    suffix = 0
                                    while index_name in context_types or re.search(
                                        rf"(?<![\w-]){re.escape(index_name)}(?![\w-])",
                                        current_source,
                                    ):
                                        suffix += 1
                                        index_name = f"agdaprover-index-{suffix}"
                                    arguments = list(recursive_spec.argument_names)
                                    arguments[position] = render_application(
                                        seed, (index_name,)
                                    )
                                    recursive_expression = render_application(
                                        recursive_spec.root_name, arguments
                                    )
                                    abstraction = (
                                        f"(λ {index_name} → {recursive_expression})"
                                    )
                                    if abstraction in attempted_abstractions:
                                        continue
                                    attempted_abstractions.add(abstraction)
                                    for action in scoped_actions:
                                        if (
                                            explicit_arity(action.type_text) != 1
                                            or _safe_arrow_count(
                                                _first_explicit_domain(action.type_text)
                                                or ""
                                            )
                                            == 0
                                            or target_relation.operator
                                            not in action.type_text
                                        ):
                                            continue
                                        if not available():
                                            break
                                        expression = render_application(
                                            action.expression, (abstraction,)
                                        )
                                        stats.actions_generated += 1
                                        stats.actions_considered += 1
                                        stats.recursive_function_abstractions += 1
                                        stats.recursive_function_lift_queries += 1
                                        inferred = active_session.infer_type(
                                            state,
                                            goal_id=goal.goal_id,
                                            expression=expression,
                                        )
                                        if (
                                            parse_relation(
                                                inferred or "",
                                                expected_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            is not None
                                        ):
                                            function_evidence.append(
                                                (expression, inferred or "", position)
                                            )
                                            break
                                    if len(function_evidence) >= 4:
                                        break
                                if len(function_evidence) >= 4:
                                    break
                            # The same telescope-shaped principle may close a
                            # function relation over an empty index without an
                            # induction hypothesis.  ``λ ()`` is Agda's
                            # datatype-generic absurd pattern; trying it here
                            # derives empty-branch extensionality from the live
                            # zero-constructor metadata and remains entirely
                            # kernel checked.
                            if len(function_evidence) < 5:
                                empty_abstraction = "(λ ())"
                                for action in scoped_actions:
                                    if (
                                        explicit_arity(action.type_text) != 1
                                        or _safe_arrow_count(
                                            _first_explicit_domain(action.type_text)
                                            or ""
                                        )
                                        == 0
                                        or target_relation.operator
                                        not in action.type_text
                                    ):
                                        continue
                                    if not available():
                                        break
                                    expression = render_application(
                                        action.expression, (empty_abstraction,)
                                    )
                                    stats.actions_generated += 1
                                    stats.actions_considered += 1
                                    stats.recursive_function_abstractions += 1
                                    stats.recursive_function_lift_queries += 1
                                    inferred = active_session.infer_type(
                                        state,
                                        goal_id=goal.goal_id,
                                        expression=expression,
                                    )
                                    if (
                                        parse_relation(
                                            inferred or "",
                                            expected_operator=target_relation.operator,
                                        )
                                        is not None
                                    ):
                                        function_evidence.append(
                                            (expression, inferred or "", None)
                                        )
                                        break
                            if function_evidence:
                                grounded_function_evidence = tuple(
                                    evidence
                                    for evidence in function_evidence
                                    if _INTERNAL_META.search(evidence[1]) is None
                                )
                                context_functions: list[str] = []
                                context_variable = "agdaprover-value"
                                outer_argument_context = _outer_argument_context(
                                    target_relation.left,
                                    target_relation.right,
                                    context_variable,
                                )
                                if outer_argument_context is not None:
                                    context_function = (
                                        f"(λ {context_variable} → "
                                        f"{outer_argument_context})"
                                    )
                                    context_functions.append(context_function)
                                for (
                                    _expression,
                                    type_text,
                                    _position,
                                ) in grounded_function_evidence:
                                    edge = parse_relation(
                                        type_text,
                                        expected_operator=(target_relation.operator),
                                    )
                                    if edge is None:
                                        continue
                                    context_body = common_unary_relation_context(
                                        edge.left,
                                        edge.right,
                                        target_relation.left,
                                        target_relation.right,
                                        context_variable,
                                    )
                                    if context_body is not None:
                                        context_function = (
                                            f"(λ {context_variable} → {context_body})"
                                        )
                                        context_functions.append(context_function)
                                context_functions = list(
                                    dict.fromkeys(context_functions)
                                )
                                term_arguments = tuple(
                                    dict.fromkeys(
                                        (
                                            *context_functions,
                                            *_application_subterms(
                                                target_relation.left
                                            ),
                                            *_application_subterms(
                                                target_relation.right
                                            ),
                                        )
                                    )
                                )
                                attempted_lifts: set[str] = set()
                                anchored_lifts: list[tuple[int, str, str, str]] = []
                                lift_actions = tuple(
                                    action
                                    for action in scoped_actions
                                    if (
                                        premise_relation_evidence_arity(
                                            action,
                                            relation_operator=(
                                                target_relation.operator
                                            ),
                                        )
                                        or 0
                                    )
                                    > 0
                                )
                                lift_actions = tuple(
                                    sorted(
                                        lift_actions,
                                        key=lambda action: (
                                            int(
                                                (
                                                    premise_relation_function_arity(
                                                        action,
                                                        relation_operator=(
                                                            active_target_relation.operator
                                                        ),
                                                    )
                                                    or 0
                                                )
                                                == 0
                                            ),
                                            -premise_result_overlap(goal, action),
                                            explicit_arity(action.type_text),
                                            action.expression,
                                        ),
                                    )[:6]
                                )
                                for action in lift_actions:
                                    function_arity = (
                                        premise_relation_function_arity(
                                            action,
                                            relation_operator=(
                                                target_relation.operator
                                            ),
                                        )
                                        or 0
                                    )
                                    if function_arity > 0:
                                        for context_function in context_functions:
                                            for (
                                                evidence_expression,
                                                _evidence_type,
                                                evidence_position,
                                            ) in function_evidence:
                                                expression = render_application(
                                                    action.expression,
                                                    (
                                                        context_function,
                                                        evidence_expression,
                                                    ),
                                                )
                                                if expression in attempted_lifts:
                                                    continue
                                                attempted_lifts.add(expression)
                                                if not available():
                                                    break
                                                stats.actions_generated += 1
                                                stats.actions_considered += 1
                                                stats.recursive_function_lift_queries += 1
                                                inferred_lift = (
                                                    active_session.infer_type(
                                                        state,
                                                        goal_id=goal.goal_id,
                                                        expression=expression,
                                                    )
                                                )
                                                lifted_relation = parse_relation(
                                                    inferred_lift or "",
                                                    expected_operator=(
                                                        target_relation.operator
                                                    ),
                                                )
                                                if (
                                                    lifted_relation is not None
                                                    and inferred_lift is not None
                                                    and _INTERNAL_META.search(
                                                        inferred_lift
                                                    )
                                                    is None
                                                ):
                                                    recursive_results.append(
                                                        (
                                                            expression,
                                                            inferred_lift or "",
                                                        )
                                                    )
                                                    if evidence_position is not None:
                                                        anchored_lifts.append(
                                                            (
                                                                evidence_position,
                                                                expression,
                                                                lifted_relation.left,
                                                                lifted_relation.right,
                                                            )
                                                        )
                                                if (
                                                    lifted_relation is not None
                                                    and normalize_type_text(
                                                        lifted_relation.left
                                                    )
                                                    == normalize_type_text(
                                                        target_relation.left
                                                    )
                                                    and normalize_type_text(
                                                        lifted_relation.right
                                                    )
                                                    == normalize_type_text(
                                                        target_relation.right
                                                    )
                                                ):
                                                    lifted_edit = (
                                                        reconstruct_case_split(
                                                            current_source,
                                                            goal,
                                                            (
                                                                f"{clause_lhs} = "
                                                                f"{expression}",
                                                            ),
                                                        )
                                                    )
                                                    break
                                                if (
                                                    lifted_relation is not None
                                                    and inferred_lift is not None
                                                    and available()
                                                ):
                                                    # Agda may print a
                                                    # definitionally equal
                                                    # function endpoint using
                                                    # an applied singleton
                                                    # argument instead of the
                                                    # source lambda binder.
                                                    # Textual endpoint closure
                                                    # is therefore only a
                                                    # fast path: ask the
                                                    # kernel whether any
                                                    # well-typed contextual
                                                    # lift inhabits the exact
                                                    # target before splitting
                                                    # another recursive field.
                                                    stats.actions_generated += 1
                                                    stats.actions_considered += 1
                                                    stats.recursive_function_lift_queries += 1
                                                    checked_lift = (
                                                        active_session.check_candidate(
                                                            goal.goal_id,
                                                            expression,
                                                        )
                                                    )
                                                    if checked_lift.accepted:
                                                        lifted_edit = (
                                                            reconstruct_case_split(
                                                                current_source,
                                                                goal,
                                                                (
                                                                    f"{clause_lhs} = "
                                                                    f"{expression}",
                                                                ),
                                                            )
                                                        )
                                                        break
                                            if (
                                                lifted_edit is not None
                                                or not available()
                                            ):
                                                break
                                    if lifted_edit is not None or not available():
                                        break
                                    applications = premise_relation_evidence_applications(
                                        action,
                                        relation_operator=(target_relation.operator),
                                        term_arguments=term_arguments,
                                        evidence_arguments=tuple(
                                            expression
                                            for expression, _type, _position in grounded_function_evidence
                                        ),
                                        evidence_types=tuple(
                                            type_text
                                            for _expression, type_text, _position in grounded_function_evidence
                                        ),
                                        endpoint_contexts=(
                                            target_relation.left,
                                            target_relation.right,
                                        ),
                                        max_applications=4,
                                    )
                                    for expression in applications:
                                        if expression in attempted_lifts:
                                            continue
                                        attempted_lifts.add(expression)
                                        if not available():
                                            break
                                        stats.actions_generated += 1
                                        stats.actions_considered += 1
                                        stats.recursive_function_lift_queries += 1
                                        checked_candidate = (
                                            active_session.check_candidate(
                                                goal.goal_id, expression
                                            )
                                        )
                                        if not checked_candidate.accepted:
                                            continue
                                        lifted_edit = reconstruct_case_split(
                                            current_source,
                                            goal,
                                            (f"{clause_lhs} = {expression}",),
                                        )
                                        break
                                    if lifted_edit is not None or not available():
                                        break
                                anchors_by_position: dict[
                                    int, tuple[int, str, str, str]
                                ] = {}
                                for anchored_lift in anchored_lifts:
                                    anchors_by_position.setdefault(
                                        anchored_lift[0], anchored_lift
                                    )
                                ordered_anchors = tuple(
                                    anchors_by_position[position]
                                    for position in sorted(anchors_by_position)
                                )
                                square_anchors: tuple[tuple[int, str, str, str], ...]
                                if len(ordered_anchors) >= 2:
                                    lower_anchor = ordered_anchors[0]
                                    upper_anchor = ordered_anchors[-1]
                                    square_anchors = (
                                        (
                                            lower_anchor[0],
                                            lower_anchor[1],
                                            target_relation.left,
                                            lower_anchor[3],
                                        ),
                                        (
                                            upper_anchor[0],
                                            upper_anchor[1],
                                            upper_anchor[2],
                                            target_relation.right,
                                        ),
                                    )
                                    for (
                                        _position,
                                        anchor_expression,
                                        anchor_left,
                                        anchor_right,
                                    ) in square_anchors:
                                        recursive_results.append(
                                            (
                                                anchor_expression,
                                                f"({anchor_left}) "
                                                f"{target_relation.operator} "
                                                f"({anchor_right})",
                                            )
                                        )
                                else:
                                    square_anchors = ()
                                if (
                                    lifted_edit is None
                                    and len(square_anchors) == 2
                                    and context_functions
                                    and available()
                                ):
                                    # Two higher-order recursive edges may
                                    # leave a square between their inner
                                    # endpoints.  Build that square by the
                                    # same finite tower operations already in
                                    # scope: eliminate singleton indices,
                                    # apply the recursive theorem at the
                                    # exposed children, extend pointwise
                                    # evidence to function evidence, and lift
                                    # it through the surrounding constructor.
                                    # Every component is selected solely by
                                    # its displayed telescope and checked by
                                    # Agda; no W-type, equality, or constructor
                                    # name is recognized here.
                                    current_arguments = (
                                        _clause_arguments(clause_lhs, root_name)
                                        if root_name is not None
                                        else ()
                                    )
                                    descendant_arguments: dict[
                                        int, tuple[str, str]
                                    ] = {}
                                    for recursive_spec in recursive_specs:
                                        position = recursive_spec.recursive_position
                                        if (
                                            position is None
                                            or position >= len(current_arguments)
                                            or position in descendant_arguments
                                        ):
                                            continue
                                        for seed in recursive_spec.structural_seeds:
                                            seed_type = context_types.get(seed)
                                            if seed_type is None:
                                                continue
                                            index_domain = _first_explicit_domain(
                                                seed_type
                                            )
                                            try:
                                                seed_codomain = split_top_level_arrows(
                                                    seed_type
                                                )[-1]
                                            except ValueError:
                                                continue
                                            if (
                                                index_domain is None
                                                or _safe_result_head(seed_codomain)
                                                != _safe_result_head(
                                                    recursive_spec.recursive_domain
                                                )
                                            ):
                                                continue
                                            concrete_index_domain = index_domain
                                            index_catalog = constructor_catalog(
                                                goal,
                                                state,
                                                _safe_result_head(
                                                    concrete_index_domain
                                                ),
                                            )
                                            index_entries = tuple(
                                                dict.fromkeys(
                                                    (
                                                        *index_catalog,
                                                        *scope_catalog,
                                                    )
                                                )
                                            )
                                            index_candidates = tuple(
                                                name
                                                for name, type_text in sorted(
                                                    (
                                                        entry
                                                        for entry in index_entries
                                                        if explicit_arity(entry[1]) == 0
                                                    ),
                                                    key=lambda entry: (
                                                        normalize_type_text(entry[1])
                                                        != normalize_type_text(
                                                            concrete_index_domain
                                                        ),
                                                        _safe_result_head(entry[1])
                                                        != _safe_result_head(
                                                            concrete_index_domain
                                                        ),
                                                        entry[0],
                                                    ),
                                                )
                                            )[:12]
                                            # A displayed dependent domain may
                                            # be a stuck family application,
                                            # so its constructor catalogue need
                                            # not expose the constructor of its
                                            # normal form.  Probe nullary scoped
                                            # inhabitants by applying the live
                                            # child function; Agda decides
                                            # definitional compatibility.
                                            for index_constructor in index_candidates:
                                                if not available():
                                                    break
                                                indexed_seed = render_application(
                                                    seed,
                                                    (index_constructor,),
                                                )
                                                stats.actions_generated += 1
                                                stats.actions_considered += 1
                                                stats.recursive_function_lift_queries += 1
                                                inferred_child = (
                                                    active_session.infer_type(
                                                        state,
                                                        goal_id=goal.goal_id,
                                                        expression=indexed_seed,
                                                    )
                                                )
                                                if (
                                                    inferred_child is not None
                                                    and _safe_result_head(
                                                        inferred_child
                                                    )
                                                    == _safe_result_head(
                                                        recursive_spec.recursive_domain
                                                    )
                                                ):
                                                    descendant_arguments[position] = (
                                                        seed,
                                                        index_constructor,
                                                    )
                                                    break
                                            if position in descendant_arguments:
                                                break
                                    extensional_actions = tuple(
                                        action
                                        for action in scoped_actions
                                        if (
                                            explicit_arity(action.type_text) == 1
                                            and _safe_arrow_count(
                                                _first_explicit_domain(action.type_text)
                                                or ""
                                            )
                                            > 0
                                            and target_relation.operator
                                            in action.type_text
                                        )
                                    )[:3]
                                    contextual_actions = tuple(
                                        action
                                        for action in lift_actions
                                        if (
                                            explicit_arity(action.type_text) > 1
                                            and premise_relation_function_arity(
                                                action,
                                                relation_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            or 0
                                        )
                                        > 0
                                    )[:4]
                                    if len(descendant_arguments) >= 2 and len(
                                        current_arguments
                                    ) == explicit_arity(root_goal.target):
                                        bridge_found = False
                                        positions = tuple(sorted(descendant_arguments))
                                        for left_position in positions:
                                            for right_position in positions:
                                                if left_position == right_position:
                                                    continue
                                                base_arguments = list(current_arguments)
                                                patterns: list[str] = []
                                                for position in positions:
                                                    seed, index_constructor = (
                                                        descendant_arguments[position]
                                                    )
                                                    base_arguments[position] = (
                                                        render_application(
                                                            seed,
                                                            (index_constructor,),
                                                        )
                                                    )
                                                    patterns.append(index_constructor)
                                                (
                                                    base_arguments[left_position],
                                                    (base_arguments[right_position]),
                                                ) = (
                                                    base_arguments[right_position],
                                                    base_arguments[left_position],
                                                )
                                                base_evidence = render_application(
                                                    root_name or "",
                                                    base_arguments,
                                                )
                                                for (
                                                    extensional_action
                                                ) in extensional_actions:
                                                    for (
                                                        contextual_action
                                                    ) in contextual_actions:
                                                        for (
                                                            context_function
                                                        ) in context_functions[:2]:
                                                            proof = base_evidence
                                                            for (
                                                                index_constructor
                                                            ) in patterns[:2]:
                                                                pointwise = (
                                                                    f"(λ {{ "
                                                                    f"{index_constructor} "
                                                                    f"→ {proof} }})"
                                                                )
                                                                function_relation = render_application(
                                                                    extensional_action.expression,
                                                                    (pointwise,),
                                                                )
                                                                proof = render_application(
                                                                    contextual_action.expression,
                                                                    (
                                                                        context_function,
                                                                        function_relation,
                                                                    ),
                                                                )
                                                            if not available():
                                                                break
                                                            lower_edge = square_anchors[
                                                                0
                                                            ]
                                                            upper_edge = square_anchors[
                                                                1
                                                            ]
                                                            bridge_endpoints = (
                                                                (
                                                                    lower_edge[3],
                                                                    upper_edge[2],
                                                                ),
                                                            )
                                                            for (
                                                                bridge_left,
                                                                bridge_right,
                                                            ) in bridge_endpoints:
                                                                if not available():
                                                                    break
                                                                constrained_proof = (
                                                                    "((λ (agdaprover-proof : "
                                                                    f"({bridge_left}) "
                                                                    f"{target_relation.operator} "
                                                                    f"({bridge_right})) → "
                                                                    "agdaprover-proof) "
                                                                    f"({proof}))"
                                                                )
                                                                stats.actions_generated += 1
                                                                stats.actions_considered += 1
                                                                stats.recursive_function_lift_queries += 1
                                                                inferred_bridge = active_session.infer_type(
                                                                    state,
                                                                    goal_id=goal.goal_id,
                                                                    expression=(
                                                                        constrained_proof
                                                                    ),
                                                                )
                                                                if (
                                                                    inferred_bridge
                                                                    is not None
                                                                    and _INTERNAL_META.search(
                                                                        inferred_bridge
                                                                    )
                                                                    is None
                                                                    and parse_relation(
                                                                        inferred_bridge,
                                                                        expected_operator=(
                                                                            target_relation.operator
                                                                        ),
                                                                    )
                                                                    is not None
                                                                ):
                                                                    recursive_results.append(
                                                                        (
                                                                            constrained_proof,
                                                                            f"({bridge_left}) "
                                                                            f"{target_relation.operator} "
                                                                            f"({bridge_right})",
                                                                        )
                                                                    )
                                                                    bridge_found = True
                                                                    break
                                                        if (
                                                            bridge_found
                                                            or not available()
                                                        ):
                                                            break
                                                    if bridge_found or not available():
                                                        break
                                                if bridge_found or not available():
                                                    break
                                            if bridge_found or not available():
                                                break
                            if (
                                lifted_edit is None
                                and len(grounded_function_evidence) >= 2
                                and available()
                            ):
                                nested_contexts = _nested_outer_contexts(
                                    target_relation.left,
                                    target_relation.right,
                                    "agdaprover-value",
                                )
                                current_arguments = (
                                    _clause_arguments(clause_lhs, root_name)
                                    if root_name is not None
                                    else ()
                                )
                                nested_descendant_arguments: dict[
                                    int, tuple[str, str]
                                ] = {}
                                for recursive_spec in recursive_specs:
                                    position = recursive_spec.recursive_position
                                    if (
                                        position is None
                                        or position >= len(current_arguments)
                                        or position in nested_descendant_arguments
                                    ):
                                        continue
                                    for seed in recursive_spec.structural_seeds:
                                        seed_type = context_types.get(seed)
                                        if seed_type is None:
                                            continue
                                        index_domain = _first_explicit_domain(seed_type)
                                        try:
                                            seed_codomain = split_top_level_arrows(
                                                seed_type
                                            )[-1]
                                        except ValueError:
                                            continue
                                        if index_domain is None or _safe_result_head(
                                            seed_codomain
                                        ) != _safe_result_head(
                                            recursive_spec.recursive_domain
                                        ):
                                            continue
                                        index_catalog = constructor_catalog(
                                            goal,
                                            state,
                                            _safe_result_head(index_domain),
                                        )
                                        nullary_indices = tuple(
                                            name
                                            for name, type_text in index_catalog
                                            if explicit_arity(type_text) == 0
                                        )
                                        if len(nullary_indices) == 1:
                                            nested_descendant_arguments[position] = (
                                                seed,
                                                nullary_indices[0],
                                            )
                                            break
                                if (
                                    len(nested_contexts) >= 2
                                    and len(nested_descendant_arguments) >= 2
                                    and len(current_arguments)
                                    == explicit_arity(root_goal.target)
                                ):
                                    recursive_arguments = list(current_arguments)
                                    index_patterns: list[str] = []
                                    for position, (
                                        seed,
                                        index_constructor,
                                    ) in sorted(nested_descendant_arguments.items()):
                                        recursive_arguments[position] = (
                                            render_application(
                                                seed, (index_constructor,)
                                            )
                                        )
                                        index_patterns.append(index_constructor)
                                    base_evidence = render_application(
                                        root_name or "", recursive_arguments
                                    )
                                    extensional_actions = tuple(
                                        action
                                        for action in scoped_actions
                                        if (
                                            explicit_arity(action.type_text) == 1
                                            and _safe_arrow_count(
                                                _first_explicit_domain(action.type_text)
                                                or ""
                                            )
                                            > 0
                                            and target_relation.operator
                                            in action.type_text
                                        )
                                    )[:3]
                                    contextual_actions = tuple(
                                        action
                                        for action in scoped_actions
                                        if (
                                            premise_relation_function_arity(
                                                action,
                                                relation_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            or 0
                                        )
                                        > 0
                                    )[:4]
                                    for extensional_action in extensional_actions:
                                        for contextual_action in contextual_actions:
                                            proof = base_evidence
                                            for depth_index, context in enumerate(
                                                reversed(nested_contexts)
                                            ):
                                                index_constructor = index_patterns[
                                                    min(
                                                        depth_index,
                                                        len(index_patterns) - 1,
                                                    )
                                                ]
                                                pointwise = (
                                                    f"(λ {{ {index_constructor} → "
                                                    f"{proof} }})"
                                                )
                                                function_relation = render_application(
                                                    extensional_action.expression,
                                                    (pointwise,),
                                                )
                                                proof = render_application(
                                                    contextual_action.expression,
                                                    (context, function_relation),
                                                )
                                            if not available():
                                                break
                                            stats.actions_generated += 1
                                            stats.actions_considered += 1
                                            stats.recursive_function_lift_queries += 1
                                            checked_tower = (
                                                active_session.check_candidate(
                                                    goal.goal_id, proof
                                                )
                                            )
                                            if checked_tower.accepted:
                                                lifted_edit = reconstruct_case_split(
                                                    current_source,
                                                    goal,
                                                    (f"{clause_lhs} = {proof}",),
                                                )
                                                break
                                        if lifted_edit is not None or not available():
                                            break
                        if (
                            lifted_edit is None
                            and clause_lhs is not None
                            and closure_carrier_type is not None
                        ):
                            # Preserve the cheapest structural explanation.
                            # Constructor-only closure is exact and avoids
                            # introducing unrelated scoped laws when recursive
                            # evidence already spans the goal.
                            for (
                                relation_constructor,
                                relation_operator,
                            ) in family_candidates:
                                lifted_edit = recursive_relation_closure_edit(
                                    current_source,
                                    goal,
                                    clause_lhs=clause_lhs,
                                    carrier_type=closure_carrier_type,
                                    recursive_results=tuple(
                                        dict.fromkeys(recursive_results)
                                    ),
                                    relation_constructor=relation_constructor,
                                    relation_operator=relation_operator,
                                    carrier_constructors=tuple(
                                        dict.fromkeys(closure_carrier_constructors)
                                    ),
                                    allow_term_contexts=False,
                                )
                                if lifted_edit is not None:
                                    break
                            if lifted_edit is None:
                                # Multi-field constructors become ordinary
                                # unary contexts once their nonrecursive fields
                                # are fixed by a clause (for example
                                # ``payload ∷_``).  Direct syntactic context
                                # closure is kernel-query free and should run
                                # before retrieving unrelated scoped laws.
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    lifted_edit = recursive_relation_closure_edit(
                                        current_source,
                                        goal,
                                        clause_lhs=clause_lhs,
                                        carrier_type=closure_carrier_type,
                                        recursive_results=tuple(
                                            dict.fromkeys(recursive_results)
                                        ),
                                        relation_constructor=relation_constructor,
                                        relation_operator=relation_operator,
                                        carrier_constructors=tuple(
                                            dict.fromkeys(closure_carrier_constructors)
                                        ),
                                        allow_term_contexts=True,
                                    )
                                    if lifted_edit is not None:
                                        break
                            if lifted_edit is None and available():
                                # Pretty-printed mixfix applications can hide
                                # a definitionally exposed subterm.  Surface
                                # text alone cannot distinguish
                                # ``C (x op y)`` from ``C x op y``, so the
                                # ordinary context graph deliberately rejects
                                # the latter.  Admit that broader parse only
                                # as a speculative reconstruction and run a
                                # fresh whole-module check immediately.  A
                                # genuine definitional context is retained;
                                # an accidental substring never enters the
                                # proof graph or terminal search frontier.
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    speculative_context_edit = (
                                        recursive_relation_closure_edit(
                                            current_source,
                                            goal,
                                            clause_lhs=clause_lhs,
                                            carrier_type=closure_carrier_type,
                                            recursive_results=tuple(
                                                dict.fromkeys(recursive_results)
                                            ),
                                            relation_constructor=(relation_constructor),
                                            relation_operator=relation_operator,
                                            carrier_constructors=tuple(
                                                dict.fromkeys(
                                                    closure_carrier_constructors
                                                )
                                            ),
                                            allow_term_contexts=True,
                                            allow_unparenthesized_contexts=True,
                                            allow_implicit_fixity_grouping=(
                                                reorders_homogeneous_coordinates(
                                                    root_goal.target
                                                )
                                            ),
                                        )
                                    )
                                    repeated_algebraic_boundary = False
                                    if (
                                        has_productive_elimination_candidate
                                        and target_relation is not None
                                    ):
                                        # A repeated visible binary operation
                                        # signals a genuine nested algebraic
                                        # boundary, where an associativity or
                                        # distributivity law may repair the
                                        # speculative context.  Otherwise a
                                        # fresh structural coordinate is the
                                        # cheaper way to expose the actual
                                        # mixfix parse and its computation
                                        # rule.  Declaration metadata, not an
                                        # operator spelling, identifies the
                                        # finite set of binary tokens.
                                        if scope_catalog is None:
                                            scope_catalog = scope_declarations(
                                                goal, state
                                            )
                                        visible_binary_operators = tuple(
                                            notation.surface_operator
                                            for name, _type in scope_catalog
                                            for notation in (
                                                binary_mixfix_notation(name),
                                            )
                                            if notation is not None
                                        )
                                        target_endpoints = (
                                            target_relation.left,
                                            target_relation.right,
                                        )
                                        repeated_algebraic_boundary = any(
                                            normalize_type_text(endpoint)
                                            .split()
                                            .count(operator)
                                            >= 2
                                            for endpoint in target_endpoints
                                            for operator in (visible_binary_operators)
                                        )
                                        prefer_productive_elimination = not (
                                            repeated_algebraic_boundary
                                        )
                                    if (
                                        speculative_context_edit is None
                                        and prefer_productive_elimination
                                    ):
                                        speculative_context_edit = (
                                            recursive_relation_closure_edit(
                                                current_source,
                                                goal,
                                                clause_lhs=clause_lhs,
                                                carrier_type=closure_carrier_type,
                                                recursive_results=tuple(
                                                    dict.fromkeys(recursive_results)
                                                ),
                                                relation_constructor=(
                                                    relation_constructor
                                                ),
                                                relation_operator=relation_operator,
                                                carrier_constructors=tuple(
                                                    dict.fromkeys(
                                                        closure_carrier_constructors
                                                    )
                                                ),
                                                allow_term_contexts=True,
                                                allow_unparenthesized_contexts=True,
                                                allow_kernel_endpoint_conversion=True,
                                            )
                                        )
                                    if speculative_context_edit is None:
                                        continue
                                    stats.actions_generated += 1
                                    stats.actions_considered += 1
                                    if candidate_closes_interaction_leaf(
                                        speculative_context_edit
                                    ):
                                        lifted_edit = speculative_context_edit
                                        break
                                    if prefer_productive_elimination:
                                        break
                                # A rejected speculative conversion yields to
                                # the next structural coordinate below.  A
                                # kernel-accepted complete leaf is retained
                                # even when another split is available.
                            # A recursive edge rarely closes an algebraic law
                            # by itself.  Instantiate earlier scoped laws from
                            # either endpoint of the current goal, infer their
                            # exact result edges, and hand those proof terms to
                            # the same finite relation closure.  No declaration
                            # name or carrier constructor receives a special
                            # role; surface matching only proposes terms and
                            # Agda decides every application.
                            if (
                                lifted_edit is None
                                and target_relation is not None
                                and recursive_results
                                and isinstance(active_session, ScopeDeclarationSession)
                                and not (
                                    has_cross_carrier_elimination_candidate
                                    and not has_function_structural_seed
                                )
                                and not prefer_productive_elimination
                            ):
                                if scope_catalog is None:
                                    scope_catalog = scope_declarations(goal, state)
                                scoped_actions = rank_scope_premises(
                                    goal,
                                    scope_catalog,
                                    excluded_names=(
                                        frozenset((root_name,))
                                        if root_name is not None
                                        else frozenset()
                                    ),
                                )
                                rewrite_declarations = tuple(
                                    (action.expression, action.type_text)
                                    for action in scoped_actions
                                )
                                # Try the bounded symbolic rewrite graph
                                # before asking Agda to type a wider local
                                # congruence layer.  Associative/commutative
                                # and constructor-context laws are often
                                # already connected by the recursive edges;
                                # in that case saturation cannot improve the
                                # proof and only spends kernel calls.
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    lifted_edit = recursive_relation_closure_edit(
                                        current_source,
                                        goal,
                                        clause_lhs=clause_lhs,
                                        carrier_type=closure_carrier_type,
                                        recursive_results=tuple(
                                            dict.fromkeys(recursive_results)
                                        ),
                                        relation_constructor=relation_constructor,
                                        relation_operator=relation_operator,
                                        carrier_constructors=tuple(
                                            dict.fromkeys(closure_carrier_constructors)
                                        ),
                                        rewrite_declarations=(rewrite_declarations),
                                    )
                                    if lifted_edit is not None:
                                        break
                                if lifted_edit is None:
                                    # Globally rank exact endpoint
                                    # instantiations before the wider local
                                    # saturation rounds.  A distributive or
                                    # naturality law often supplies the one
                                    # boundary edge around a recursive
                                    # hypothesis, but declaration order is a
                                    # poor proxy for that relevance.  Surface
                                    # overlap only schedules the proposals;
                                    # Agda infers every resulting edge.
                                    endpoint_proposals: list[
                                        tuple[tuple[int, int, int, int, int], str]
                                    ] = []
                                    exact_endpoints = (
                                        target_relation.left,
                                        target_relation.right,
                                        *(
                                            endpoint
                                            for _expression, inferred_type in recursive_results
                                            for edge in (
                                                parse_relation(
                                                    inferred_type,
                                                    expected_operator=(
                                                        target_relation.operator
                                                    ),
                                                ),
                                            )
                                            if edge is not None
                                            for endpoint in (edge.left, edge.right)
                                        ),
                                    )
                                    for action_index, action in enumerate(
                                        scoped_actions
                                    ):
                                        for application_index, expression in enumerate(
                                            premise_relation_endpoint_applications(
                                                action,
                                                relation_operator=(
                                                    target_relation.operator
                                                ),
                                                endpoints=exact_endpoints,
                                            )[:8]
                                        ):
                                            ordered, shared = (
                                                premise_application_context_score(
                                                    expression,
                                                    endpoint_contexts=(
                                                        target_relation.left,
                                                        target_relation.right,
                                                    ),
                                                )
                                            )
                                            endpoint_proposals.append(
                                                (
                                                    (
                                                        -premise_result_overlap(
                                                            goal, action
                                                        ),
                                                        -ordered,
                                                        -shared,
                                                        action_index,
                                                        application_index,
                                                    ),
                                                    expression,
                                                )
                                            )
                                    exact_results = list(
                                        dict.fromkeys(recursive_results)
                                    )
                                    exact_seen = {
                                        expression
                                        for expression, _type_text in exact_results
                                    }
                                    exact_stop = min(
                                        action_budget,
                                        stats.actions_considered
                                        + (
                                            8
                                            if has_productive_elimination_candidate
                                            else 12
                                        ),
                                    )
                                    for _priority, expression in sorted(
                                        endpoint_proposals, key=lambda item: item[0]
                                    ):
                                        if expression in exact_seen:
                                            continue
                                        if (
                                            not available()
                                            or stats.actions_considered >= exact_stop
                                        ):
                                            break
                                        exact_seen.add(expression)
                                        stats.actions_generated += 1
                                        stats.premise_candidates += 1
                                        inferred = active_session.infer_type(
                                            state,
                                            goal_id=goal.goal_id,
                                            expression=expression,
                                        )
                                        stats.actions_considered += 1
                                        stats.premise_queries += 1
                                        stats.relation_saturation_queries += 1
                                        if (
                                            parse_relation(
                                                inferred or "",
                                                expected_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            is not None
                                        ):
                                            exact_results.append(
                                                (expression, inferred or "")
                                            )
                                            for (
                                                relation_constructor,
                                                relation_operator,
                                            ) in family_candidates:
                                                lifted_edit = recursive_relation_closure_edit(
                                                    current_source,
                                                    goal,
                                                    clause_lhs=clause_lhs,
                                                    carrier_type=(closure_carrier_type),
                                                    recursive_results=tuple(
                                                        dict.fromkeys(exact_results)
                                                    ),
                                                    relation_constructor=(
                                                        relation_constructor
                                                    ),
                                                    relation_operator=(
                                                        relation_operator
                                                    ),
                                                    carrier_constructors=tuple(
                                                        dict.fromkeys(
                                                            closure_carrier_constructors
                                                        )
                                                    ),
                                                    rewrite_declarations=(
                                                        rewrite_declarations
                                                    ),
                                                )
                                                if lifted_edit is not None:
                                                    recursive_results = exact_results
                                                    break
                                            if lifted_edit is not None:
                                                break
                                    for (
                                        relation_constructor,
                                        relation_operator,
                                    ) in family_candidates:
                                        if lifted_edit is not None:
                                            break
                                        lifted_edit = recursive_relation_closure_edit(
                                            current_source,
                                            goal,
                                            clause_lhs=clause_lhs,
                                            carrier_type=closure_carrier_type,
                                            recursive_results=tuple(
                                                dict.fromkeys(exact_results)
                                            ),
                                            relation_constructor=(relation_constructor),
                                            relation_operator=relation_operator,
                                            carrier_constructors=tuple(
                                                dict.fromkeys(
                                                    closure_carrier_constructors
                                                )
                                            ),
                                            rewrite_declarations=(rewrite_declarations),
                                        )
                                        if lifted_edit is not None:
                                            recursive_results = exact_results
                                            break
                                if lifted_edit is None:
                                    # First instantiate ordinary visible laws
                                    # at terms already present in the target.
                                    # This is substantially cheaper than
                                    # congruence saturation and often exposes
                                    # the one boundary edge needed by the
                                    # symbolic rewrite graph (for example a
                                    # distributive step around a recursive
                                    # hypothesis).  The procedure is entirely
                                    # signature-driven and therefore applies
                                    # to any inductive carrier.
                                    preliminary_results = list(
                                        dict.fromkeys(recursive_results)
                                    )
                                    preliminary_endpoints = [
                                        target_relation.left,
                                        target_relation.right,
                                    ]
                                    for (
                                        _expression,
                                        inferred_type,
                                    ) in preliminary_results:
                                        recursive_edge = parse_relation(
                                            inferred_type,
                                            expected_operator=(
                                                target_relation.operator
                                            ),
                                        )
                                        if recursive_edge is not None:
                                            preliminary_endpoints.extend(
                                                (
                                                    recursive_edge.left,
                                                    recursive_edge.right,
                                                )
                                            )
                                    preliminary_terms = tuple(
                                        dict.fromkeys(
                                            (
                                                *(
                                                    entry.name
                                                    for entry in goal.context
                                                    if entry.in_scope
                                                    and entry.name
                                                    and normalize_type_text(entry.type)
                                                    == normalize_type_text(
                                                        closure_carrier_type
                                                    )
                                                ),
                                                *(
                                                    action.expression
                                                    for action in scoped_actions
                                                    if explicit_arity(action.type_text)
                                                    == 0
                                                    and _safe_result_head(
                                                        action.type_text
                                                    )
                                                    == _safe_result_head(
                                                        closure_carrier_type
                                                    )
                                                ),
                                                *recursive_subject_terms,
                                            )
                                        )
                                    )[:10]
                                    preliminary_seen = {
                                        expression
                                        for expression, _type_text in preliminary_results
                                    }
                                    preliminary_stop = min(
                                        action_budget,
                                        stats.actions_considered
                                        + (
                                            20
                                            if has_productive_elimination_candidate
                                            else 24
                                        ),
                                    )

                                    def discover_contextual_relation_evidence(
                                        evidence_results: list[tuple[str, str]],
                                        current_goal: GoalInfo = goal,
                                        current_scope_catalog: tuple[
                                            tuple[str, str], ...
                                        ]
                                        | None = scope_catalog,
                                        current_target_relation: RelationView
                                        | None = target_relation,
                                        current_state: StateToken = state,
                                        current_family_candidates: tuple[
                                            tuple[str, str], ...
                                        ] = family_candidates,
                                    ) -> tuple[ContextualRelationEvidence, ...]:
                                        """Align function-valued endpoints through live rules.

                                        A scoped one-argument rule from pointwise relation
                                        evidence to a function relation is treated purely as
                                        a proposal.  Empty and nullary-constructor domains
                                        provide a finite set of pointwise clauses; Agda checks
                                        the exact function endpoints and the later contextual
                                        lift.  This is the representation-neutral bridge needed
                                        by W-like fields, records containing functions, and
                                        ordinary finite function spaces.
                                        """

                                        if current_target_relation is None:
                                            return ()
                                        alignments: list[
                                            ContextualRelationEvidence
                                        ] = []
                                        extensional_scope_actions = rank_scope_premises(
                                            current_goal,
                                            tuple(
                                                dict.fromkeys(
                                                    (
                                                        *(current_scope_catalog or ()),
                                                        *(
                                                            (
                                                                entry.name,
                                                                entry.type,
                                                            )
                                                            for entry in current_goal.context
                                                            if entry.name
                                                        ),
                                                    )
                                                )
                                            ),
                                            excluded_names=(
                                                frozenset((root_name,))
                                                if root_name is not None
                                                else frozenset()
                                            ),
                                            max_candidates=min(
                                                128,
                                                len(current_scope_catalog or ())
                                                + len(current_goal.context),
                                            ),
                                        )
                                        extensional_actions = tuple(
                                            action
                                            for action in extensional_scope_actions
                                            if explicit_arity(action.type_text) == 1
                                            and _safe_arrow_count(
                                                _first_explicit_domain(action.type_text)
                                                or ""
                                            )
                                            > 0
                                            and current_target_relation.operator
                                            in action.type_text
                                        )
                                        if not extensional_actions:
                                            return ()
                                        evidence_endpoints = tuple(
                                            endpoint
                                            for _expression, inferred in evidence_results
                                            for edge in (
                                                parse_relation(
                                                    inferred,
                                                    expected_operator=(
                                                        current_target_relation.operator
                                                    ),
                                                ),
                                            )
                                            if edge is not None
                                            for endpoint in (edge.left, edge.right)
                                        )
                                        context_variable = "agdaprover-context-value"
                                        attempted: set[tuple[str, str]] = set()
                                        for evidence_endpoint in evidence_endpoints:
                                            for target_endpoint in (
                                                current_target_relation.left,
                                                current_target_relation.right,
                                            ):
                                                context = common_outer_relation_context(
                                                    evidence_endpoint,
                                                    target_endpoint,
                                                    context_variable,
                                                )
                                                if context is None:
                                                    continue
                                                (
                                                    inner_left,
                                                    inner_right,
                                                    context_body,
                                                ) = context
                                                context_key = (
                                                    normalize_type_text(inner_left),
                                                    normalize_type_text(inner_right),
                                                )
                                                if context_key in attempted:
                                                    continue
                                                attempted.add(context_key)
                                                function_type: str | None = None
                                                for inner in (
                                                    inner_right,
                                                    inner_left,
                                                ):
                                                    if not available():
                                                        return tuple(alignments)
                                                    stats.actions_considered += 1
                                                    stats.recursive_function_lift_queries += 1
                                                    inferred_inner = active_session.infer_type(
                                                        current_state,
                                                        goal_id=current_goal.goal_id,
                                                        expression=inner,
                                                    )
                                                    if (
                                                        inferred_inner is not None
                                                        and _INTERNAL_META.search(
                                                            inferred_inner
                                                        )
                                                        is None
                                                        and _first_explicit_domain(
                                                            inferred_inner
                                                        )
                                                        is not None
                                                    ):
                                                        function_type = inferred_inner
                                                        break
                                                if function_type is None:
                                                    continue
                                                index_domain = _first_explicit_domain(
                                                    function_type
                                                )
                                                if index_domain is None:
                                                    continue
                                                index_catalog = constructor_catalog(
                                                    current_goal,
                                                    current_state,
                                                    _safe_result_head(index_domain),
                                                )
                                                index_candidates = tuple(
                                                    name
                                                    for name, type_text in sorted(
                                                        dict.fromkeys(
                                                            (
                                                                *index_catalog,
                                                                *(
                                                                    current_scope_catalog
                                                                    or ()
                                                                ),
                                                            )
                                                        ),
                                                        key=lambda entry: (
                                                            normalize_type_text(
                                                                entry[1]
                                                            )
                                                            != normalize_type_text(
                                                                index_domain
                                                            ),
                                                            _safe_result_head(entry[1])
                                                            != _safe_result_head(
                                                                index_domain
                                                            ),
                                                            entry[0],
                                                        ),
                                                    )
                                                    if explicit_arity(type_text) == 0
                                                )[:4]
                                                pointwise_abstractions = (
                                                    "(λ ())",
                                                    *(
                                                        f"(λ {{ {index_constructor} → "
                                                        f"{relation_constructor} }})"
                                                        for relation_constructor, _operator in current_family_candidates
                                                        for index_constructor in index_candidates
                                                    ),
                                                )
                                                alignment_found = False
                                                for (
                                                    extensional_action
                                                ) in extensional_actions[:3]:
                                                    for (
                                                        pointwise
                                                    ) in pointwise_abstractions:
                                                        if not available():
                                                            return tuple(alignments)
                                                        function_evidence = render_application(
                                                            extensional_action.expression,
                                                            (pointwise,),
                                                        )
                                                        constrained = (
                                                            "((λ (agdaprover-proof : "
                                                            f"({inner_left}) "
                                                            f"{current_target_relation.operator} "
                                                            f"({inner_right})) → "
                                                            "agdaprover-proof) "
                                                            f"({function_evidence}))"
                                                        )
                                                        stats.actions_generated += 1
                                                        stats.actions_considered += 1
                                                        stats.recursive_function_lift_queries += 1
                                                        inferred_evidence = active_session.infer_type(
                                                            current_state,
                                                            goal_id=current_goal.goal_id,
                                                            expression=constrained,
                                                        )
                                                        if (
                                                            inferred_evidence is None
                                                            or _INTERNAL_META.search(
                                                                inferred_evidence
                                                            )
                                                            is not None
                                                            or parse_relation(
                                                                inferred_evidence,
                                                                expected_operator=(
                                                                    current_target_relation.operator
                                                                ),
                                                            )
                                                            is None
                                                        ):
                                                            continue
                                                        alignments.append(
                                                            ContextualRelationEvidence(
                                                                expression=constrained,
                                                                inner_type=(
                                                                    function_type
                                                                ),
                                                                outer_left=(
                                                                    evidence_endpoint
                                                                ),
                                                                outer_right=(
                                                                    target_endpoint
                                                                ),
                                                                context_body=(
                                                                    context_body
                                                                ),
                                                                variable=(
                                                                    context_variable
                                                                ),
                                                            )
                                                        )
                                                        alignment_found = True
                                                        break
                                                    if alignment_found:
                                                        break
                                                if len(alignments) >= 2:
                                                    return tuple(alignments)
                                        return tuple(alignments)

                                    # Four fair grounding slices cover both
                                    # endpoint orders and two placements of
                                    # the most relevant missing bridge term.
                                    # Closure runs after every slice, so
                                    # simpler one- and two-step obligations pay
                                    # no extra queries.
                                    for preliminary_round in range(4):
                                        preliminary_added = False
                                        preliminary_target_edge = False
                                        # Declaration order is unrelated to a
                                        # law's usefulness.  Retain dynamic
                                        # endpoint growth within each round.
                                        # Laws connecting more of the goal's
                                        # declared operations come first,
                                        # followed by structural overlap.
                                        # Agda still infers every proposed
                                        # application.
                                        preliminary_actions = tuple(
                                            sorted(
                                                scoped_actions,
                                                key=lambda action: (
                                                    -premise_result_overlap(
                                                        goal, action
                                                    ),
                                                    explicit_arity(action.type_text),
                                                    action.expression,
                                                ),
                                            )
                                        )
                                        for action in preliminary_actions:
                                            endpoint_applications = (
                                                premise_relation_endpoint_applications(
                                                    action,
                                                    relation_operator=(
                                                        target_relation.operator
                                                    ),
                                                    endpoints=tuple(
                                                        preliminary_endpoints
                                                    ),
                                                )
                                            )
                                            grounded = (
                                                premise_relation_ground_applications(
                                                    action,
                                                    relation_operator=(
                                                        target_relation.operator
                                                    ),
                                                    endpoints=tuple(
                                                        preliminary_endpoints
                                                    ),
                                                    arguments=preliminary_terms,
                                                )
                                                if preliminary_terms
                                                else ()
                                            )
                                            grounding_width = 4
                                            start = preliminary_round * grounding_width
                                            applications = tuple(
                                                dict.fromkeys(
                                                    (
                                                        *endpoint_applications[:1],
                                                        *grounded[
                                                            start : start
                                                            + grounding_width
                                                        ],
                                                    )
                                                )
                                            )
                                            stats.actions_generated += len(applications)
                                            stats.premise_candidates += len(
                                                applications
                                            )
                                            for expression in applications:
                                                if expression in preliminary_seen:
                                                    continue
                                                if (
                                                    not available()
                                                    or stats.actions_considered
                                                    >= preliminary_stop
                                                ):
                                                    break
                                                preliminary_seen.add(expression)
                                                inferred = active_session.infer_type(
                                                    state,
                                                    goal_id=goal.goal_id,
                                                    expression=expression,
                                                )
                                                stats.actions_considered += 1
                                                stats.premise_queries += 1
                                                if inferred is None:
                                                    continue
                                                edge = parse_relation(
                                                    inferred,
                                                    expected_operator=(
                                                        target_relation.operator
                                                    ),
                                                )
                                                if edge is None:
                                                    continue
                                                edge_key = (
                                                    normalize_type_text(edge.left),
                                                    normalize_type_text(edge.right),
                                                )
                                                target_key = (
                                                    normalize_type_text(
                                                        target_relation.left
                                                    ),
                                                    normalize_type_text(
                                                        target_relation.right
                                                    ),
                                                )
                                                preliminary_results.append(
                                                    (expression, inferred)
                                                )
                                                preliminary_endpoints.extend(
                                                    (edge.left, edge.right)
                                                )
                                                preliminary_added = True
                                                if edge_key in (
                                                    target_key,
                                                    tuple(reversed(target_key)),
                                                ):
                                                    preliminary_target_edge = True
                                                    break
                                            if preliminary_target_edge:
                                                break
                                            if (
                                                not available()
                                                or stats.actions_considered
                                                >= preliminary_stop
                                            ):
                                                break
                                        if preliminary_added:
                                            contextual_relation_evidence = (
                                                discover_contextual_relation_evidence(
                                                    preliminary_results
                                                )
                                                if has_function_structural_seed
                                                else ()
                                            )
                                            for (
                                                relation_constructor,
                                                relation_operator,
                                            ) in family_candidates:
                                                lifted_edit = recursive_relation_closure_edit(
                                                    current_source,
                                                    goal,
                                                    clause_lhs=clause_lhs,
                                                    carrier_type=(closure_carrier_type),
                                                    recursive_results=tuple(
                                                        dict.fromkeys(
                                                            preliminary_results
                                                        )
                                                    ),
                                                    relation_constructor=(
                                                        relation_constructor
                                                    ),
                                                    relation_operator=(
                                                        relation_operator
                                                    ),
                                                    carrier_constructors=tuple(
                                                        dict.fromkeys(
                                                            closure_carrier_constructors
                                                        )
                                                    ),
                                                    rewrite_declarations=(
                                                        rewrite_declarations
                                                    ),
                                                    contextual_evidence=(
                                                        contextual_relation_evidence
                                                    ),
                                                )
                                                if lifted_edit is not None:
                                                    break
                                            if (
                                                lifted_edit is None
                                                and contextual_relation_evidence
                                            ):
                                                # Agda's fixity table can make
                                                # an unparenthesized compound
                                                # a genuine subterm even when
                                                # the conservative surface
                                                # parser cannot certify it.
                                                # Generate the broader lift
                                                # only after ordinary closure
                                                # has failed, then require a
                                                # fresh kernel check of this
                                                # exact interaction leaf.
                                                for (
                                                    relation_constructor,
                                                    relation_operator,
                                                ) in family_candidates:
                                                    speculative_edit = recursive_relation_closure_edit(
                                                        current_source,
                                                        goal,
                                                        clause_lhs=clause_lhs,
                                                        carrier_type=(
                                                            closure_carrier_type
                                                        ),
                                                        recursive_results=tuple(
                                                            dict.fromkeys(
                                                                preliminary_results
                                                            )
                                                        ),
                                                        relation_constructor=(
                                                            relation_constructor
                                                        ),
                                                        relation_operator=(
                                                            relation_operator
                                                        ),
                                                        carrier_constructors=tuple(
                                                            dict.fromkeys(
                                                                closure_carrier_constructors
                                                            )
                                                        ),
                                                        rewrite_declarations=(
                                                            rewrite_declarations
                                                        ),
                                                        contextual_evidence=(
                                                            contextual_relation_evidence
                                                        ),
                                                        allow_unparenthesized_contexts=True,
                                                        allow_implicit_fixity_grouping=True,
                                                        allow_kernel_endpoint_conversion=True,
                                                    )
                                                    if (
                                                        speculative_edit is not None
                                                        and candidate_closes_interaction_leaf(
                                                            speculative_edit
                                                        )
                                                    ):
                                                        lifted_edit = speculative_edit
                                                        break
                                        if lifted_edit is not None:
                                            break
                                        if not preliminary_added:
                                            break
                                    recursive_results = preliminary_results
                                # Saturate a very small proof-relevant layer
                                # around recursive evidence before graph
                                # closure.  Relation-valued declarations may
                                # consume ordinary terms (a local law) or an
                                # existing relation inhabitant (a congruence
                                # or composition principle).  Printed domain
                                # shapes select the finite pools; Agda infers
                                # every application and the endpoint carrier.
                                relation_terms = list(
                                    dict.fromkeys(
                                        (
                                            *_application_subterms(
                                                target_relation.left
                                            ),
                                            *_application_subterms(
                                                target_relation.right
                                            ),
                                            *(
                                                term
                                                for _expression, type_text in recursive_results
                                                for edge in (
                                                    parse_relation(
                                                        type_text,
                                                        expected_operator=(
                                                            target_relation.operator
                                                        ),
                                                    ),
                                                )
                                                if edge is not None
                                                for endpoint in (
                                                    edge.left,
                                                    edge.right,
                                                )
                                                for term in _application_subterms(
                                                    endpoint
                                                )
                                            ),
                                            *(
                                                entry.name
                                                for entry in goal.context
                                                if entry.in_scope and entry.name
                                            ),
                                        )
                                    )
                                )
                                relation_evidence = list(
                                    dict.fromkeys(recursive_results)
                                )
                                seed_relation_evidence_count = len(relation_evidence)
                                carrier_evidence = list(relation_evidence)
                                inferred_relation_expressions = {
                                    expression
                                    for expression, _type_text in relation_evidence
                                }
                                saturation_stop = min(
                                    action_budget,
                                    stats.actions_considered
                                    + (
                                        0
                                        if has_productive_elimination_candidate
                                        else 96
                                    ),
                                )
                                saturation_target_found = False
                                for _saturation_round in range(
                                    4 if lifted_edit is None else 0
                                ):
                                    round_stop = min(
                                        saturation_stop,
                                        stats.actions_considered
                                        + (
                                            0
                                            if has_productive_elimination_candidate
                                            else 24
                                        ),
                                    )
                                    added_evidence = False

                                    def saturation_priority(
                                        indexed: tuple[int, ScopePremiseAction],
                                        relation_operator: str = (
                                            target_relation.operator
                                            if target_relation is not None
                                            else ""
                                        ),
                                        saturation_round: int = _saturation_round,
                                    ) -> tuple[int, int, int, int, int]:
                                        index, candidate = indexed
                                        evidence_arity = (
                                            premise_relation_evidence_arity(
                                                candidate,
                                                relation_operator=relation_operator,
                                            )
                                            or 0
                                        )
                                        function_arity = (
                                            premise_relation_function_arity(
                                                candidate,
                                                relation_operator=relation_operator,
                                            )
                                            or 0
                                        )
                                        if saturation_round == 0:
                                            phase = int(evidence_arity > 0)
                                            evidence_order = evidence_arity
                                        elif saturation_round == 1:
                                            phase = int(evidence_arity == 0)
                                            evidence_order = evidence_arity
                                        else:
                                            phase = int(evidence_arity == 0)
                                            evidence_order = -evidence_arity
                                        return (
                                            phase,
                                            int(
                                                saturation_round > 0
                                                and function_arity == 0
                                            ),
                                            evidence_order,
                                            explicit_arity(candidate.type_text),
                                            index,
                                        )

                                    scheduled_applications: list[
                                        tuple[
                                            tuple[
                                                int,
                                                int,
                                                int,
                                                int,
                                                int,
                                                int,
                                                int,
                                                int,
                                            ],
                                            int,
                                            ScopePremiseAction,
                                            int,
                                            str,
                                        ]
                                    ] = []
                                    for action_index, action in enumerate(
                                        scoped_actions
                                    ):
                                        action_evidence_arity = (
                                            premise_relation_evidence_arity(
                                                action,
                                                relation_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            or 0
                                        )
                                        # Recursive hypotheses are the stable
                                        # roots of this local evidence graph.
                                        # Keep them ahead of derived edges,
                                        # while visiting newly derived edges
                                        # from newest to oldest.  Contextual
                                        # application ranking can then select
                                        # either without an order-dependent
                                        # cutoff.  This applies uniformly to
                                        # recursive records, one-constructor
                                        # types, and multi-constructor data.
                                        ordered_relation_evidence = (
                                            *relation_evidence[
                                                :seed_relation_evidence_count
                                            ],
                                            *reversed(
                                                relation_evidence[
                                                    seed_relation_evidence_count:
                                                ]
                                            ),
                                        )
                                        applications = premise_relation_evidence_applications(
                                            action,
                                            relation_operator=(
                                                target_relation.operator
                                            ),
                                            term_arguments=tuple(relation_terms),
                                            evidence_arguments=tuple(
                                                expression
                                                for expression, _type_text in ordered_relation_evidence
                                            ),
                                            evidence_types=tuple(
                                                type_text
                                                for _expression, type_text in ordered_relation_evidence
                                            ),
                                            endpoint_contexts=(
                                                target_relation.left,
                                                target_relation.right,
                                            ),
                                            max_applications=12,
                                        )
                                        stats.actions_generated += len(applications)
                                        stats.premise_candidates += len(applications)
                                        action_priority = saturation_priority(
                                            (action_index, action)
                                        )
                                        for application_index, expression in enumerate(
                                            applications
                                        ):
                                            ordered, shared = (
                                                premise_application_context_score(
                                                    expression,
                                                    endpoint_contexts=(
                                                        target_relation.left,
                                                        target_relation.right,
                                                    ),
                                                )
                                            )
                                            scheduled_applications.append(
                                                (
                                                    (
                                                        action_priority[0],
                                                        action_priority[1],
                                                        action_priority[2],
                                                        action_priority[3],
                                                        -ordered,
                                                        -shared,
                                                        action_priority[4],
                                                        application_index,
                                                    ),
                                                    action_index,
                                                    action,
                                                    action_evidence_arity,
                                                    expression,
                                                )
                                            )
                                    retained_by_action: dict[int, int] = {}
                                    for (
                                        _application_priority,
                                        action_index,
                                        selected_premise_action,
                                        action_evidence_arity,
                                        expression,
                                    ) in sorted(
                                        scheduled_applications,
                                        key=lambda candidate: candidate[0],
                                    ):
                                        retention_limit = (
                                            6 if action_evidence_arity > 0 else 2
                                        )
                                        if (
                                            retained_by_action.get(action_index, 0)
                                            >= retention_limit
                                        ):
                                            continue
                                        if expression in inferred_relation_expressions:
                                            continue
                                        if (
                                            not available(2)
                                            or stats.actions_considered + 2 > round_stop
                                        ):
                                            break
                                        inferred_relation_expressions.add(expression)
                                        inferred = active_session.infer_type(
                                            state,
                                            goal_id=goal.goal_id,
                                            expression=expression,
                                        )
                                        stats.actions_considered += 1
                                        stats.premise_queries += 1
                                        stats.relation_saturation_queries += 1
                                        if inferred is None:
                                            continue
                                        edge = parse_relation(
                                            inferred,
                                            expected_operator=(
                                                target_relation.operator
                                            ),
                                        )
                                        if edge is None:
                                            continue
                                        if normalize_type_text(
                                            edge.left
                                        ) == normalize_type_text(edge.right):
                                            # Reflexive evidence cannot enlarge
                                            # a shortest-path relation graph.
                                            # Its proof remains available through
                                            # ordinary premise search.
                                            continue
                                        relation_evidence.append((expression, inferred))
                                        stats.relation_saturation_edges += 1
                                        relation_terms.extend(
                                            _application_subterms(edge.left)
                                        )
                                        relation_terms.extend(
                                            _application_subterms(edge.right)
                                        )
                                        endpoint_type = active_session.infer_type(
                                            state,
                                            goal_id=goal.goal_id,
                                            expression=edge.left,
                                        )
                                        stats.actions_considered += 1
                                        stats.premise_queries += 1
                                        stats.relation_saturation_queries += 1
                                        if len(stats.relation_saturation_actions) < 64:
                                            stats.relation_saturation_actions.append(
                                                {
                                                    "expression": expression,
                                                    "premise": (
                                                        selected_premise_action.expression
                                                    ),
                                                    "round": _saturation_round,
                                                    "inferred_type": inferred,
                                                    "endpoint_type": endpoint_type,
                                                    "retained_for_carrier": bool(
                                                        endpoint_type is not None
                                                        and normalize_type_text(
                                                            endpoint_type
                                                        )
                                                        == normalize_type_text(
                                                            closure_carrier_type
                                                        )
                                                    ),
                                                }
                                            )
                                        if (
                                            endpoint_type is not None
                                            and normalize_type_text(endpoint_type)
                                            == normalize_type_text(closure_carrier_type)
                                        ):
                                            carrier_evidence.append(
                                                (expression, inferred)
                                            )
                                            if (
                                                normalize_type_text(edge.left),
                                                normalize_type_text(edge.right),
                                            ) == (
                                                normalize_type_text(
                                                    target_relation.left
                                                ),
                                                normalize_type_text(
                                                    target_relation.right
                                                ),
                                            ):
                                                saturation_target_found = True
                                        added_evidence = True
                                        retained_by_action[action_index] = (
                                            retained_by_action.get(action_index, 0) + 1
                                        )
                                        if saturation_target_found:
                                            break
                                    relation_terms = list(
                                        dict.fromkeys(relation_terms)
                                    )[:48]
                                    if saturation_target_found or not added_evidence:
                                        break
                                recursive_results = list(
                                    dict.fromkeys(carrier_evidence)
                                )
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    if lifted_edit is not None:
                                        break
                                    lifted_edit = recursive_relation_closure_edit(
                                        current_source,
                                        goal,
                                        clause_lhs=clause_lhs,
                                        carrier_type=closure_carrier_type,
                                        recursive_results=tuple(
                                            dict.fromkeys(recursive_results)
                                        ),
                                        relation_constructor=relation_constructor,
                                        relation_operator=relation_operator,
                                        carrier_constructors=tuple(
                                            dict.fromkeys(closure_carrier_constructors)
                                        ),
                                        rewrite_declarations=(rewrite_declarations),
                                        contextual_evidence=(
                                            contextual_relation_evidence
                                        ),
                                    )
                                    if lifted_edit is not None:
                                        break
                                endpoints = [
                                    target_relation.left,
                                    target_relation.right,
                                ]
                                for _expression, inferred_type in recursive_results:
                                    recursive_edge = parse_relation(
                                        inferred_type,
                                        expected_operator=target_relation.operator,
                                    )
                                    if recursive_edge is not None:
                                        endpoints.extend(
                                            (recursive_edge.left, recursive_edge.right)
                                        )
                                inferred_expressions = {
                                    expression
                                    for expression, _type in recursive_results
                                }
                                premise_stop = min(
                                    action_budget,
                                    stats.actions_considered
                                    + (
                                        0
                                        if has_productive_elimination_candidate
                                        else 24
                                    ),
                                )
                                ground_terms = tuple(
                                    dict.fromkeys(
                                        (
                                            *(
                                                entry.name
                                                for entry in goal.context
                                                if entry.in_scope
                                                and entry.name
                                                and normalize_type_text(entry.type)
                                                == normalize_type_text(
                                                    closure_carrier_type
                                                )
                                            ),
                                            *(
                                                action.expression
                                                for action in scoped_actions
                                                if explicit_arity(action.type_text) == 0
                                                and _safe_result_head(action.type_text)
                                                == _safe_result_head(
                                                    closure_carrier_type
                                                )
                                            ),
                                        )
                                    )
                                )[:6]
                                for relation_round in range(
                                    2 if lifted_edit is None else 0
                                ):
                                    added = False
                                    for action in scoped_actions:
                                        endpoint_applications = (
                                            premise_relation_endpoint_applications(
                                                action,
                                                relation_operator=(
                                                    target_relation.operator
                                                ),
                                                endpoints=tuple(endpoints),
                                            )
                                        )
                                        ground_applications: tuple[str, ...] = ()
                                        if ground_terms:
                                            grounded = (
                                                premise_relation_ground_applications(
                                                    action,
                                                    relation_operator=(
                                                        target_relation.operator
                                                    ),
                                                    endpoints=tuple(endpoints),
                                                    arguments=ground_terms,
                                                )
                                            )
                                            start = relation_round
                                            ground_applications = grounded[
                                                start : start + 1
                                            ]
                                        # Exact endpoint matches are cheap, but
                                        # they must not suppress applications
                                        # whose missing arguments expose a
                                        # definitional reduction.  Interleave
                                        # both classes and give every visible
                                        # law a small share of each round.
                                        applications = tuple(
                                            dict.fromkeys(
                                                (
                                                    *ground_applications,
                                                    *endpoint_applications[:1],
                                                )
                                            )
                                        )
                                        stats.actions_generated += len(applications)
                                        stats.premise_candidates += len(applications)
                                        for expression in applications:
                                            if expression in inferred_expressions:
                                                continue
                                            if (
                                                not available()
                                                or stats.actions_considered
                                                >= premise_stop
                                            ):
                                                break
                                            inferred_expressions.add(expression)
                                            inferred = active_session.infer_type(
                                                state,
                                                goal_id=goal.goal_id,
                                                expression=expression,
                                            )
                                            stats.actions_considered += 1
                                            stats.premise_queries += 1
                                            if inferred is None:
                                                continue
                                            edge = parse_relation(
                                                inferred,
                                                expected_operator=(
                                                    target_relation.operator
                                                ),
                                            )
                                            if edge is None:
                                                continue
                                            recursive_results.append(
                                                (expression, inferred)
                                            )
                                            endpoints.extend((edge.left, edge.right))
                                            added = True
                                        if added:
                                            for (
                                                relation_constructor,
                                                relation_operator,
                                            ) in family_candidates:
                                                lifted_edit = recursive_relation_closure_edit(
                                                    current_source,
                                                    goal,
                                                    clause_lhs=clause_lhs,
                                                    carrier_type=(closure_carrier_type),
                                                    recursive_results=tuple(
                                                        dict.fromkeys(recursive_results)
                                                    ),
                                                    relation_constructor=(
                                                        relation_constructor
                                                    ),
                                                    relation_operator=(
                                                        relation_operator
                                                    ),
                                                    carrier_constructors=tuple(
                                                        dict.fromkeys(
                                                            closure_carrier_constructors
                                                        )
                                                    ),
                                                    rewrite_declarations=(
                                                        rewrite_declarations
                                                    ),
                                                    contextual_evidence=(
                                                        contextual_relation_evidence
                                                    ),
                                                )
                                                if lifted_edit is not None:
                                                    break
                                        if lifted_edit is not None:
                                            break
                                        if (
                                            not available()
                                            or stats.actions_considered >= premise_stop
                                        ):
                                            break
                                    if lifted_edit is not None:
                                        break
                                    if not added:
                                        break
                            if lifted_edit is None:
                                for (
                                    relation_constructor,
                                    relation_operator,
                                ) in family_candidates:
                                    lifted_edit = recursive_relation_closure_edit(
                                        current_source,
                                        goal,
                                        clause_lhs=clause_lhs,
                                        carrier_type=closure_carrier_type,
                                        recursive_results=tuple(
                                            dict.fromkeys(recursive_results)
                                        ),
                                        relation_constructor=relation_constructor,
                                        relation_operator=relation_operator,
                                        carrier_constructors=tuple(
                                            dict.fromkeys(closure_carrier_constructors)
                                        ),
                                        rewrite_declarations=(rewrite_declarations),
                                        contextual_evidence=(
                                            contextual_relation_evidence
                                        ),
                                    )
                                    if lifted_edit is not None:
                                        break
                        if lifted_edit is not None:
                            stats.recursive_lift_clauses += 1
                            stats.recursive_lift_proposals += 1
                            stats.induction_proposals += 1
                            if len(stats.recursive_actions) < 64:
                                stats.recursive_actions.append(
                                    {
                                        "tag": "close-recursive-relation",
                                        "schema_version": (
                                            "agdaprover.recursive-closure.v1"
                                        ),
                                        "replacement": lifted_edit.get(
                                            "replacement", ""
                                        ),
                                    }
                                )
                            edits.append(lifted_edit)
                            continue
                    if (
                        recursive_clause is not None
                        and root_name is not None
                        and root_domain is not None
                        and isinstance(active_session, TermInferenceSession)
                        and isinstance(active_session, TransactionalKernelSession)
                        and available()
                    ):
                        state = active_session.current_state()
                        recursive_result_type = active_session.infer_type(
                            state,
                            goal_id=goal.goal_id,
                            expression=recursive_clause.recursive_call(root_name),
                        )
                        stats.actions_considered += 1
                        stats.recursive_lift_inference_queries += 1
                        if recursive_result_type is None:
                            stats.recursive_lift_inference_failures += 1
                        if recursive_result_type is not None:
                            target_relation = parse_relation(goal.target)
                            declarations: tuple[tuple[str, str], ...] = ()
                            if target_relation is not None:
                                declarations = constructor_catalog(
                                    goal,
                                    state,
                                    binary_mixfix_head(target_relation.operator),
                                )
                            recursive_elimination = None
                            family_candidates = reflexive_family_constructors(
                                declarations
                            )
                            stats.recursive_lift_family_candidates += len(
                                family_candidates
                            )
                            for (
                                relation_constructor,
                                relation_operator,
                            ) in family_candidates:
                                recursive_elimination = recursive_result_lifting_edit(
                                    current_source,
                                    goal,
                                    root_name=root_name,
                                    carrier_type=root_domain,
                                    clause=recursive_clause,
                                    recursive_result_type=recursive_result_type,
                                    relation_constructor=relation_constructor,
                                    relation_operator=relation_operator,
                                )
                                if recursive_elimination is not None:
                                    break
                            if recursive_elimination is not None:
                                stats.actions_generated += 1
                                stats.induction_proposals += 1
                                stats.recursive_lift_proposals += 1
                                edits.append(recursive_elimination)
                                continue

                    # Some post-elimination leaves are direct instances of a
                    # visible theorem whose explicit arguments occur in its
                    # result. Recover only those result-determined terms and
                    # ask Agda to check the complete application. This avoids
                    # launching recursive premise search for a one-edge leaf.
                    if (
                        case_split_seen
                        and isinstance(active_session, ScopeDeclarationSession)
                        and isinstance(active_session, TransactionalKernelSession)
                        and isinstance(active_session, TermInferenceSession)
                    ):
                        if scope_catalog is None:
                            scope_catalog = scope_declarations(
                                goal, active_session.current_state()
                            )
                        direct_actions = rank_scope_premises(
                            goal,
                            scope_catalog,
                            excluded_names=(
                                frozenset((root_name,))
                                if root_name is not None
                                else frozenset()
                            ),
                        )
                        direct_edit: dict[str, object] | None = None
                        direct_target_relation = parse_relation(goal.target)
                        direct_evidence: list[tuple[str, str]] = []
                        if direct_target_relation is not None:
                            endpoint_actions = sorted(
                                direct_actions,
                                key=lambda action: (
                                    -premise_result_overlap(goal, action),
                                    explicit_arity(action.type_text),
                                    action.expression,
                                ),
                            )[:12]
                            seen_endpoint_expressions: set[str] = set()
                            for action in endpoint_actions:
                                applications = premise_relation_endpoint_applications(
                                    action,
                                    relation_operator=(direct_target_relation.operator),
                                    endpoints=(
                                        direct_target_relation.left,
                                        direct_target_relation.right,
                                    ),
                                )[:2]
                                for expression in applications:
                                    if expression in seen_endpoint_expressions:
                                        continue
                                    seen_endpoint_expressions.add(expression)
                                    if not available():
                                        break
                                    stats.actions_considered += 1
                                    stats.actions_generated += 1
                                    stats.premise_queries += 1
                                    inferred = active_session.infer_type(
                                        active_session.current_state(),
                                        goal_id=goal.goal_id,
                                        expression=expression,
                                    )
                                    edge = parse_relation(
                                        inferred or "",
                                        expected_operator=(
                                            direct_target_relation.operator
                                        ),
                                    )
                                    if edge is not None:
                                        direct_evidence.append(
                                            (expression, inferred or "")
                                        )
                                if not available():
                                    break
                            if direct_evidence and available():
                                transformation_actions = tuple(
                                    sorted(
                                        (
                                            action
                                            for action in direct_actions
                                            if (
                                                premise_relation_evidence_arity(
                                                    action,
                                                    relation_operator=(
                                                        direct_target_relation.operator
                                                    ),
                                                )
                                                or 0
                                            )
                                            > 0
                                        ),
                                        key=lambda action: (
                                            premise_relation_evidence_arity(
                                                action,
                                                relation_operator=(
                                                    direct_target_relation.operator
                                                ),
                                            )
                                            or 0,
                                            -premise_result_overlap(goal, action),
                                            action.expression,
                                        ),
                                    )[:6]
                                )
                                direct_terms = tuple(
                                    dict.fromkeys(
                                        (
                                            *_application_subterms(
                                                direct_target_relation.left
                                            ),
                                            *_application_subterms(
                                                direct_target_relation.right
                                            ),
                                        )
                                    )
                                )
                                attempted_transformations: set[str] = set()
                                for action in transformation_actions:
                                    applications = premise_relation_evidence_applications(
                                        action,
                                        relation_operator=(
                                            direct_target_relation.operator
                                        ),
                                        term_arguments=direct_terms,
                                        evidence_arguments=tuple(
                                            expression
                                            for expression, _type in direct_evidence
                                        ),
                                        evidence_types=tuple(
                                            type_text
                                            for _expression, type_text in direct_evidence
                                        ),
                                        endpoint_contexts=(
                                            direct_target_relation.left,
                                            direct_target_relation.right,
                                        ),
                                        max_applications=4,
                                    )
                                    for expression in applications:
                                        if expression in attempted_transformations:
                                            continue
                                        attempted_transformations.add(expression)
                                        if not available():
                                            break
                                        stats.actions_considered += 1
                                        stats.actions_generated += 1
                                        stats.proof_checks += 1
                                        checked_transformation = (
                                            active_session.check_candidate(
                                                goal.goal_id, expression
                                            )
                                        )
                                        if not checked_transformation.accepted:
                                            continue
                                        direct_edit = reconstruct_hole_completion(
                                            current_source, goal, expression
                                        )
                                        stats.result_determined_premise_closures += 1
                                        break
                                    if direct_edit is not None or not available():
                                        break
                        if direct_edit is not None:
                            edits.append(direct_edit)
                            continue
                        for action in direct_actions[:16]:
                            direct_expression = premise_result_application(goal, action)
                            if direct_expression is None:
                                continue
                            if not available():
                                break
                            stats.actions_considered += 1
                            stats.actions_generated += 1
                            stats.premise_queries += 1
                            stats.result_determined_premise_queries += 1
                            stats.proof_checks += 1
                            checked_direct = active_session.check_candidate(
                                goal.goal_id, direct_expression
                            )
                            if not checked_direct.accepted:
                                continue
                            direct_edit = reconstruct_hole_completion(
                                current_source, goal, direct_expression
                            )
                            stats.result_determined_premise_closures += 1
                            break
                        if direct_edit is not None:
                            edits.append(direct_edit)
                            continue

                    case_actions = [
                        RefinementCandidate.case_split(entry.name, entry.type)
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    ]
                    dependency_plan: DependencyPlan | None = None
                    try:
                        dependency_plan = build_dependency_plan(goal)
                    except ValueError:
                        # Planning is heuristic and may not reject syntax that
                        # Agda itself has already elaborated successfully.
                        stats.dependency_planning_fallbacks += 1
                    if dependency_plan is not None:
                        stats.dependency_towers_built += 1
                        stats.max_dependency_depth = max(
                            stats.max_dependency_depth,
                            dependency_plan.tower.max_depth(),
                        )
                        stats.proof_relevant_nodes_observed += (
                            dependency_plan.proof_relevant_nodes
                        )
                        stats.parallel_inhabitants_observed += (
                            dependency_plan.parallel_inhabitants
                        )

                    # Elimination and construction must alternate.  A case
                    # split can expose a blocked leaf that is immediately
                    # discharged by a visible declaration through a nested
                    # premise chain.  Dependency ordering eliminates the most
                    # informative cells first; after no named split remains,
                    # structural search owns the leaf.
                    preferred_constructor_arity = (
                        max(
                            0,
                            sum(
                                1
                                for entry in goal.context
                                if entry.in_scope and entry.name
                            )
                            - recursive_baseline_context_size,
                        )
                        if recursive_baseline_context_size is not None
                        else None
                    )
                    has_recursive_descendant = bool(
                        recursive_call is not None
                        and preferred_constructor_arity is not None
                        and preferred_constructor_arity > 0
                        and any(
                            entry.in_scope
                            and entry.name
                            and _safe_result_head(entry.type)
                            == _safe_result_head(recursive_call.recursive_domain)
                            for entry in goal.context
                        )
                    )
                    has_relevant_local_function = any(
                        entry.in_scope
                        and entry.name
                        and _safe_arrow_count(entry.type)
                        and _safe_result_head(entry.type)
                        == _safe_result_head(goal.target)
                        for entry in goal.context
                    )
                    recursive_result_matches_goal = any(
                        _safe_result_head(split_top_level_arrows(spec.root_type)[-1])
                        == _safe_result_head(goal.target)
                        for spec in recursive_specs
                    )
                    relational_elimination_available = has_relational_context_evidence(
                        goal.target,
                        tuple(
                            entry.type
                            for entry in goal.context
                            if entry.in_scope and entry.name
                        ),
                    )
                    should_try_structural = bool(
                        not case_actions
                        or recursive_specs
                        or has_recursive_descendant
                        or has_relevant_local_function
                        or (
                            recursive_split_depth is not None
                            and depth >= recursive_split_depth + 2
                            and preferred_constructor_arity is not None
                            and preferred_constructor_arity > 0
                        )
                    )
                    scheduling_classification = classify_structural_scheduling(
                        recursive_result_head_matches_goal=(
                            recursive_result_matches_goal
                        ),
                        construction_result_head_matches_goal=(
                            recursive_result_matches_goal or has_relevant_local_function
                        ),
                        structural_construction_available=(
                            should_try_structural
                            and not unresolved_program_dependencies
                        ),
                        productive_elimination_available=(
                            has_productive_elimination_candidate
                        ),
                        structural_descent_available=bool(
                            recursive_specs or has_recursive_descendant
                        ),
                        higher_order_structural_descent_available=any(
                            _first_explicit_domain(spec.recursive_domain) is not None
                            for spec in recursive_specs
                        ),
                        dependencies_ready=not unresolved_program_dependencies,
                        homogeneous_coordinate_permutation=(
                            reorders_homogeneous_coordinates(root_goal.target)
                        ),
                        reflexive_relation_target=is_reflexive_relation_target(
                            goal.target
                        ),
                        relational_elimination_available=(
                            relational_elimination_available
                        ),
                    )
                    structural_attempted = False
                    if (
                        case_split_seen
                        and scheduling_classification.structural_construction_available
                        and not relational_elimination_available
                        and (
                            not scheduling_classification.productive_elimination_available
                            or has_relevant_local_function
                            or recursive_result_matches_goal
                        )
                        and isinstance(active_session, TransactionalKernelSession)
                        and available()
                    ):
                        structural_attempted = True
                        structural = construct_leaf(
                            active_session,
                            goal,
                            leaf_depth=depth,
                            recursive_spec=(
                                recursive_specs[0]
                                if recursive_specs
                                else recursive_call
                            ),
                            allow_wrapping=(
                                recursive_split_depth is not None
                                and depth >= recursive_split_depth + 2
                            ),
                            preferred_arity=preferred_constructor_arity,
                            case_alternatives_remain=bool(case_actions),
                        )
                        if structural.solutions:
                            stats.structural_leaf_closures += 1
                            edits.append(
                                reconstruct_hole_completion(
                                    current_source,
                                    goal,
                                    structural.solutions[0].proof_text,
                                )
                            )
                            level_choices.extend(
                                structural.solutions[0].plan.choices_on_proof()
                            )
                            continue
                        if (
                            structural.status == "resource-exhausted"
                            and not case_actions
                        ):
                            raise TimeoutError(structural.diagnostic)

                    def dependency_key(
                        action: RefinementCandidate,
                        plan: DependencyPlan | None = dependency_plan,
                        current_goal: GoalInfo = goal,
                    ) -> tuple[object, ...]:
                        priority = (
                            plan.priority(action.expression)
                            if plan is not None
                            else (2, 2, 2, 0, 0, 0)
                        )
                        return (*priority, *action.symbolic_key(current_goal))

                    case_actions.sort(key=dependency_key)
                    preferred_root_scrutinee: str | None = None
                    if not case_split_seen and preferred_root_position is not None:
                        visible_names = tuple(
                            entry.name
                            for entry in goal.context
                            if entry.in_scope and entry.name
                        )
                        root_arity = explicit_arity(root_goal.target)
                        root_arguments = (
                            visible_names[-root_arity:]
                            if root_arity and len(visible_names) >= root_arity
                            else ()
                        )
                        preferred_root_scrutinee = (
                            root_arguments[preferred_root_position]
                            if preferred_root_position < len(root_arguments)
                            else None
                        )
                        case_actions.sort(
                            key=lambda action: (
                                action.expression != preferred_root_scrutinee,
                                dependency_key(action),
                            )
                        )
                    current_clause_lhs = (
                        recursive_clause_lhs(current_source, goal)
                        if root_name is not None
                        else None
                    )
                    current_clause_arguments = (
                        _clause_arguments(current_clause_lhs, root_name)
                        if current_clause_lhs is not None and root_name is not None
                        else ()
                    )
                    constructor_descendants = {
                        strip_outer_parentheses(term)
                        for argument in current_clause_arguments
                        for terms in (
                            _top_level_terms(strip_outer_parentheses(argument)),
                        )
                        if len(terms) >= 2
                        for term in terms[1:]
                    }

                    def repeated_coordinate_penalty(
                        action: RefinementCandidate,
                        descendants: frozenset[str] = frozenset(
                            constructor_descendants
                        ),
                    ) -> int:
                        # Before descending through the same constructor field
                        # again, inspect another still-variable coordinate.
                        # This is the finite product induction discipline that
                        # prevents ``C (C (C ...))`` case-search trails.
                        return int(action.expression in descendants)

                    stats.actions_generated += len(case_actions)
                    case_by_expression = {
                        action.expression: action for action in case_actions
                    }
                    context_types = {
                        entry.name: entry.type
                        for entry in goal.context
                        if entry.in_scope and entry.name
                    }
                    ranked_cases = rank_policy(
                        goal,
                        tuple(
                            policy_candidate(
                                family="case-variable",
                                tag="eliminate-local",
                                expression=action.expression,
                                type_text=context_types.get(
                                    action.expression, action.local_type or "unknown"
                                ),
                                symbolic_key=dependency_key(action),
                                metadata=(
                                    (
                                        "repeated-coordinate",
                                        str(repeated_coordinate_penalty(action)),
                                    ),
                                ),
                            )
                            for action in case_actions
                        ),
                        classification=scheduling_classification,
                    )
                    case_actions = [
                        case_by_expression[candidate.expression]
                        for candidate in ranked_cases
                    ]
                    case_choices = active_policy.snapshot_choices("case-variable", goal)
                    accepted_cases: list[
                        tuple[
                            dict[str, object],
                            RefinementCandidate,
                            int,
                        ]
                    ] = []
                    for case_action in case_actions:
                        if not available():
                            raise TimeoutError(
                                "batched case search exhausted its action budget"
                            )
                        stats.actions_considered += 1
                        stats.case_queries += 1
                        choice = case_choices.get(case_action.expression)
                        if choice is not None:
                            active_policy.recorder.mark(
                                choice.decision_id, choice.candidate_id
                            )
                        checked_case = active_session.check_case_split(
                            goal.goal_id, case_action.expression
                        )
                        if not checked_case.accepted:
                            if choice is not None:
                                active_policy.recorder.mark(
                                    choice.decision_id,
                                    choice.candidate_id,
                                    outcome="invalid",
                                )
                            continue
                        subgoals = sum(
                            len(_HOLE.findall(clause))
                            for clause in checked_case.clauses
                        )
                        try:
                            proposed_edit = reconstruct_case_split(
                                current_source, goal, checked_case.clauses
                            )
                        except ValueError:
                            continue
                        accepted_cases.append((proposed_edit, case_action, subgoals))
                        if subgoals == 0:
                            stats.zero_constructor_closures += 1
                            break
                        if (
                            preferred_root_scrutinee is not None
                            and case_action.expression == preferred_root_scrutinee
                        ):
                            # This alternative explicitly fixes its recursive
                            # coordinate; scoring other coordinates can no
                            # longer affect it and only reloads the module.
                            break
                        if len(accepted_cases) >= 4:
                            # Lookahead is a bounded ordering device, not a
                            # second unbounded case-search frontier.
                            break
                    if not accepted_cases:
                        # Named hypotheses are only split *proposals*. Once
                        # Agda rejects them all, retain the established case
                        # tree and try applications/projections/construction
                        # in this leaf instead of restarting at the root.
                        if (
                            case_split_seen
                            and not structural_attempted
                            and not unresolved_program_dependencies
                            and isinstance(active_session, TransactionalKernelSession)
                            and available()
                        ):
                            structural = construct_leaf(
                                active_session,
                                goal,
                                leaf_depth=depth,
                                recursive_spec=(
                                    recursive_specs[0] if recursive_specs else None
                                ),
                                allow_wrapping=(
                                    recursive_split_depth is not None
                                    and depth >= recursive_split_depth + 2
                                ),
                                preferred_arity=preferred_constructor_arity,
                                case_alternatives_remain=False,
                            )
                            if structural.solutions:
                                stats.structural_leaf_closures += 1
                                edits.append(
                                    reconstruct_hole_completion(
                                        current_source,
                                        goal,
                                        structural.solutions[0].proof_text,
                                    )
                                )
                                level_choices.extend(
                                    structural.solutions[0].plan.choices_on_proof()
                                )
                                continue
                            if structural.status == "resource-exhausted":
                                raise TimeoutError(structural.diagnostic)
                        return no_proof(
                            "no supported case or recursive action closed a leaf",
                        )
                    if len(accepted_cases) == 1 or accepted_cases[0][2] == 0:
                        selected_edit, selected_action, selected_subgoals = (
                            accepted_cases[0]
                        )
                    else:
                        local_types = {
                            entry.name: entry.type
                            for entry in goal.context
                            if entry.in_scope and entry.name
                        }

                        preferred_cases = tuple(
                            candidate
                            for candidate in accepted_cases
                            if preferred_root_scrutinee is not None
                            and candidate[1].expression == preferred_root_scrutinee
                        )
                        cross_carrier_cases = tuple(
                            candidate
                            for candidate in accepted_cases
                            if root_domain_heads
                            and _safe_result_head(
                                local_types.get(candidate[1].expression, "")
                            )
                            not in root_domain_heads
                        )
                        fresh_coordinate_cases = tuple(
                            candidate
                            for candidate in accepted_cases
                            if repeated_coordinate_penalty(candidate[1]) == 0
                        )
                        # An explicitly selected recursive coordinate is
                        # authoritative.  Otherwise expose a field from a
                        # genuinely different carrier before recurring into
                        # its owner.  Root parameters of the same type are not
                        # interchangeable merely because their constructor
                        # fan-out matches, so kernel lookahead compares those
                        # alternatives.
                        structurally_preferred = (
                            preferred_cases
                            or cross_carrier_cases
                            or (
                                fresh_coordinate_cases
                                if len(fresh_coordinate_cases) < len(accepted_cases)
                                else ()
                            )
                            or tuple(accepted_cases)
                        )
                        scored_cases: tuple[
                            tuple[
                                dict[str, object],
                                RefinementCandidate,
                                int,
                                tuple[int, int, int, int],
                            ],
                            ...,
                        ]
                        if len(structurally_preferred) == 1:
                            (
                                selected_edit,
                                selected_action,
                                selected_subgoals,
                            ) = structurally_preferred[0]
                            if len(stats.constructor_orders) < 64:
                                stats.constructor_orders.append(
                                    {
                                        "target": goal.target,
                                        "structural_case_selection": (
                                            selected_action.expression
                                        ),
                                    }
                                )
                            scored_cases = ()
                        else:
                            scored_cases = tuple(
                                (
                                    proposed_edit,
                                    action,
                                    subgoals,
                                    case_successor_score(proposed_edit),
                                )
                                for proposed_edit, action, subgoals in structurally_preferred
                            )
                        if scored_cases and len(stats.constructor_orders) < 64:
                            stats.constructor_orders.append(
                                {
                                    "target": goal.target,
                                    "case_lookahead": [
                                        {
                                            "scrutinee": action.expression,
                                            "score": list(score),
                                        }
                                        for _edit, action, _subgoals, score in scored_cases
                                    ],
                                }
                            )
                        if scored_cases:
                            (
                                selected_edit,
                                selected_action,
                                selected_subgoals,
                                _selected_score,
                            ) = min(
                                scored_cases,
                                key=lambda item: (
                                    item[3][0],
                                    item[3][1],
                                    repeated_coordinate_penalty(item[1]),
                                    dependency_key(item[1]),
                                    item[3][2],
                                    item[3][3],
                                ),
                            )
                    case_split_seen = True
                    if root_name is not None and selected_action.local_type is not None:
                        root_arity = explicit_arity(root_goal.target)
                        current_lhs = recursive_clause_lhs(current_source, goal)
                        parsed_arguments = (
                            _clause_arguments(current_lhs, root_name)
                            if current_lhs is not None
                            else ()
                        )
                        if len(parsed_arguments) == root_arity:
                            root_arguments = parsed_arguments
                        else:
                            visible_names = tuple(
                                entry.name
                                for entry in goal.context
                                if entry.in_scope and entry.name
                            )
                            root_arguments = (
                                visible_names[-root_arity:]
                                if root_arity and len(visible_names) >= root_arity
                                else ()
                            )
                        recursive_position = next(
                            (
                                index
                                for index, name in enumerate(root_arguments)
                                if strip_outer_parentheses(name)
                                == selected_action.expression
                            ),
                            None,
                        )
                        # Keep recursion anchored to a displayed argument of
                        # the definition.  Later eliminations may split a
                        # constructor field (a list inside a one-constructor
                        # tree, for example); that field is a route to a
                        # smaller root value, not a new recursive domain.
                        # Overwriting the anchor here prevents the generic
                        # one-constructor wrapper from rebuilding that value.
                        if recursive_position is not None or recursive_call is None:
                            recursive_call = RecursiveCallSpec(
                                root_name=root_name,
                                root_type=root_goal.target,
                                recursive_domain=selected_action.local_type,
                                argument_names=root_arguments,
                                recursive_position=recursive_position,
                            )
                            recursive_split_depth = depth
                            recursive_baseline_context_size = max(
                                0,
                                sum(
                                    1
                                    for entry in goal.context
                                    if entry.in_scope and entry.name
                                )
                                - 1,
                            )
                    stats.generated_subgoals += selected_subgoals
                    if dependency_plan is not None and (
                        dependency_plan.is_dependency_guided(selected_action.expression)
                    ):
                        stats.dependency_guided_splits += 1
                    if dependency_plan is not None:
                        elimination = dependency_plan.elimination_action(
                            selected_action.expression
                        )
                        if elimination is not None:
                            record_elimination_action(elimination.to_dict())
                    edits.append(selected_edit)
                    selected_choice = case_choices.get(selected_action.expression)
                    if selected_choice is not None:
                        level_choices.append(selected_choice)

                current_source, delta = _apply_disjoint_edits(current_source, edits)
                # Only choices whose edits entered this source branch survive.
                # Lookahead and failed structural alternatives earn no credit.
                committed_choices.extend(level_choices)
                current_end += delta
                depth += 1
                stats.levels_completed += 1
                stats.max_depth = max(stats.max_depth, depth)
                replacement = current_source[region_start:current_end]
                if _HOLE.search(replacement) is None:
                    # This remains a proposal.  The caller either loads the
                    # resulting joint state or performs fresh validation,
                    # so another speculative module load adds no evidence.
                    patch = reconstruct_guided_completion(
                        original_source, root_goal, replacement
                    )
                    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                    return CaseBatchResult(
                        "solved",
                        patch,
                        replacement,
                        stats,
                        policy_choices=tuple(committed_choices),
                    )
        except TimeoutError as error:
            stats.elapsed_ms = (time.monotonic() - started) * 1000.0
            return CaseBatchResult("resource-exhausted", None, None, stats, str(error))
        except ValueError as error:
            return no_proof(str(error))

    raise RuntimeError("batched case session exited without a result")
