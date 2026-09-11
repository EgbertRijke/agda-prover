"""Bounded, kernel-checked search for a jointly constrained goal prefix."""

from __future__ import annotations

import hashlib
import json
import os
import re
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from .actions import RefinementCandidate
from .artifacts import file_sha256
from .bridge.resources import current_process_rss, temporary_workspace
from .budget import SearchBudget
from .case_search import CaseBatchStats, batched_case_prove
from .constructor_search import ConstructorStats, constructor_tree_prove
from .contracts import (
    GoalInfo,
    ProverResult,
    TaskSpec,
    search_budget_envelope,
    task_identity,
)
from .dependency_planner import (
    goal_has_concrete_nullary_scrutinee,
    goal_has_dependency_tower,
)
from .focused import FocusedCandidatesResult, FocusedStats, focused_candidates
from .kernel.p0 import AgdaBridgeError, AgdaLoadError, AgdaSession, open_kernel_session
from .kernel.protocol import (
    KernelSessionFactory,
    ScopeDeclarationSession,
    TransactionalKernelSession,
)
from .notation import binary_mixfix_notation, strip_outer_parentheses
from .observability.policy_trace import (
    PolicyChoice,
    PolicyTraceRecorder,
    validated_proof_evidence,
)
from .offline import assert_offline_configuration
from .or_policy import ORPolicyRouter, policy_candidate
from .presentation import (
    apply_source_edit,
    declaration_name_at_goal,
    reconstruct_case_split,
    reconstruct_checked_clause_completion,
    reconstruct_hole_completion,
    reconstruct_intro,
    reconstruct_joint_completion,
    reconstruct_term_as_clause,
)
from .principal_variation import (
    PrincipalVariationObserver,
    joint_principal_variation,
)
from .project import (
    agda_source_suffix,
    attach_module_scope,
    choose_goal_prefix,
    require_agda_source_file,
)
from .project.sources import mask_literate_markdown
from .ranking.protocol import ProofTermRanker
from .ranking.runtime import configured_model_ids, load_proof_models
from .reasoning.classifications import has_relational_elimination_shape
from .reasoning.evidence import has_structured_builder, telescope_introduction
from .relation_path import RelationView, explicit_arity, parse_relation
from .resource_budget import ResourceLimitError, ResourceScope, charge_io
from .retrieval_stats import ScopedRetrievalStats
from .scope_catalog import visible_scope_declarations
from .search_frontier import BatchedFrontier
from .terms import Term, render_term, symbolic_key
from .type_syntax import (
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
from .verifier_budget import VerifierCallLimitExceeded, VerifierCallScope

JOINT_ALGORITHM = "kernel-checked-joint-prefix-best-first-v1"
_MAX_STRUCTURAL_ALTERNATIVES = 8
_MAX_RECORDED_PREMISE_ATTEMPTS = 64
_MAX_RECORDED_SKELETON_ATTEMPTS = 64
_MAX_RECORDED_ELIMINATION_ACTIONS = 64


@dataclass
class JointStats(ScopedRetrievalStats):
    algorithm: str = JOINT_ALGORITHM
    target_goals: int = 0
    states_expanded: int = 0
    states_enqueued: int = 0
    frontier_peak: int = 0
    frontier_pruned: int = 0
    transposition_hits: int = 0
    dead_states: int = 0
    dead_state_diagnostics: list[str] = field(default_factory=list)
    terminal_validation_rejections: int = 0
    actions_considered: int = 0
    actions_generated: int = 0
    depth_pruned: int = 0
    max_depth: int = 0
    kernel_loads: int = 0
    kernel_load_elapsed_ms: float = 0.0
    goal_inspections: int = 0
    refinement_queries: int = 0
    constructor_queries: int = 0
    constructor_catalog_queries: int = 0
    premise_catalog_queries: int = 0
    premise_queries: int = 0
    premise_refinement_queries: int = 0
    premise_candidates: int = 0
    premise_attempts: list[dict[str, object]] = field(default_factory=list)
    premise_attempts_omitted: int = 0
    completion_queries: int = 0
    incomplete_solutions_pruned: int = 0
    case_queries: int = 0
    zero_constructor_candidates: int = 0
    zero_constructor_closures: int = 0
    zero_candidate_validation_checks: int = 0
    case_batches: int = 0
    case_levels: int = 0
    focused_batches: int = 0
    focused_batch_goals: int = 0
    focused_fallbacks_deferred: int = 0
    focused_fallbacks_resumed: int = 0
    generated_subgoals: int = 0
    proof_checks: int = 0
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
    recursive_actions: list[dict[str, object]] = field(default_factory=list)
    relation_saturation_queries: int = 0
    relation_saturation_edges: int = 0
    relation_saturation_actions: list[dict[str, object]] = field(default_factory=list)
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
    dependency_towers_built: int = 0
    dependency_planning_fallbacks: int = 0
    dependency_guided_splits: int = 0
    dependency_ready_goals_selected: int = 0
    observed_definition_candidates: int = 0
    observed_definition_queries: int = 0
    observed_equation_candidates: int = 0
    progressive_widening_fallbacks: int = 0
    constraint_widening_fallbacks: int = 0
    budget_widening_fallbacks: int = 0
    budget_widening_enabled: bool = True
    contextual_evidence_enabled: bool = True
    max_dependency_depth: int = 0
    proof_relevant_nodes_observed: int = 0
    parallel_inhabitants_observed: int = 0
    elimination_actions: list[dict[str, object]] = field(default_factory=list)
    elimination_actions_omitted: int = 0
    model_calls: int = 0
    model_batches: int = 0
    model_elapsed_ms: float = 0.0
    source_bytes_materialized: int = 0
    source_bytes_written: int = 0
    elapsed_ms: float = 0.0
    depth_limit: int | None = None
    focused: dict[str, int | float] = field(default_factory=dict)
    nnue_accumulator: dict[str, int] | None = None

    def to_dict(self) -> dict[str, object]:
        return self.stats_dict()


@dataclass(order=True)
class _State:
    priority: tuple[int, int, int, int]
    sequence: int
    replacement: str = field(compare=False)
    depth: int = field(compare=False)
    steps: tuple[dict[str, object], ...] = field(compare=False)
    widened_declarations: frozenset[str] = field(
        default_factory=frozenset,
        compare=False,
    )
    budget_widened: bool = field(default=False, compare=False)
    # Observational lineage belongs to this source branch, never the shared
    # router's most recently explored alternative. It does not affect ordering
    # or transposition identity; a duplicate keeps the first queued witness.
    policy_choices: tuple[PolicyChoice, ...] = field(default=(), compare=False)
    # A continuation of this exact source state, not a property of later goals.
    # Approximate focused terms may be rejected by Agda or their descendants.
    skip_focused: bool = field(default=False, compare=False)


@dataclass(frozen=True)
class _DeferredBudgetWidening:
    state: _State
    source: str
    region_end: int
    remaining_goals: int
    action_start: int
    action_limit: int

    def exhausted(self, actions_considered: int) -> bool:
        return actions_considered - self.action_start >= self.action_limit


def _can_amortize_budget_widening(remaining_actions: int, remaining_goals: int) -> bool:
    """Do not add restart work to a run already short of one slice per goal."""
    return remaining_actions > 160 * max(1, remaining_goals)


def _search_state_digest(
    replacement: str,
    widened_declarations: frozenset[str],
    budget_widened: bool = False,
    skip_focused: bool = False,
) -> str:
    # Keep the budget tier distinct from source/declaration text, including
    # declarations whose valid names happen to resemble an internal marker.
    payload = json.dumps(
        (replacement, sorted(widened_declarations), budget_widened, skip_focused),
        ensure_ascii=False,
        separators=(",", ":"),
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


# Compatibility alias for prototype callers that imported the former private
# helper. New orchestration uses the shared pure selector directly.
_select_cutoff = choose_goal_prefix


def _replace_goal(
    source: str, goal: GoalInfo, replacement: str
) -> tuple[str, dict[str, object]]:
    start = goal.source_range[0] - 1
    end = goal.source_range[1] - 1
    if start < 0 or end <= start or end > len(source):
        raise ValueError("Agda returned an invalid joint-search goal range")
    selected = source[start:end]
    if not (selected == "?" or (selected.startswith("{!") and selected.endswith("!}"))):
        raise ValueError("joint-search goal range does not select a source hole")
    try:
        edit = reconstruct_hole_completion(source, goal, replacement)
    except ValueError:
        # Partial Agda previews are search states rather than supplied proof
        # terms, so their holes and layout must remain exactly as Agda emits.
        edit = {
            "schema_version": "agdaprover.reconstruction.p0.v1",
            "style": "term",
            "source_range": [start + 1, end + 1],
            "original": selected,
            "replacement": replacement,
            "binders": [],
            "body": replacement,
        }
    return apply_source_edit(source, edit), edit


def _edit_within_region(
    edit: dict[str, object], *, region_start: int, region_end: int
) -> bool:
    source_range = edit.get("source_range")
    return bool(
        isinstance(source_range, list)
        and len(source_range) == 2
        and all(isinstance(value, int) for value in source_range)
        and region_start <= source_range[0] - 1
        and source_range[1] - 1 <= region_end
    )


def _accumulate_case_stats(target: JointStats, source: CaseBatchStats) -> int:
    """Merge a case-search trace and return its kernel query count."""

    target.merge_retrieval(source)
    target.actions_considered += source.actions_considered
    target.actions_generated += source.actions_generated
    target.refinement_queries += source.refinement_queries
    target.constructor_queries += source.constructor_queries
    target.constructor_catalog_queries += source.constructor_catalog_queries
    target.premise_catalog_queries += source.premise_catalog_queries
    target.premise_queries += source.premise_queries
    target.premise_refinement_queries += source.premise_refinement_queries
    target.premise_candidates += source.premise_candidates
    target.evidence_inference_queries += source.evidence_inference_queries
    target.evidence_terms += source.evidence_terms
    target.evidence_path_queries += source.evidence_path_queries
    remaining_premise_slots = max(
        0, _MAX_RECORDED_PREMISE_ATTEMPTS - len(target.premise_attempts)
    )
    retained_premise_attempts = source.premise_attempts[:remaining_premise_slots]
    target.premise_attempts.extend(retained_premise_attempts)
    target.premise_attempts_omitted += (
        source.premise_attempts_omitted
        + len(source.premise_attempts)
        - len(retained_premise_attempts)
    )
    target.completion_queries += source.completion_queries
    target.incomplete_solutions_pruned += source.incomplete_solutions_pruned
    target.case_queries += source.case_queries
    target.proof_checks += source.proof_checks
    target.zero_constructor_candidates += source.zero_constructor_candidates
    target.zero_constructor_closures += source.zero_constructor_closures
    target.zero_candidate_validation_checks += source.zero_candidate_validation_checks
    target.case_batches += 1
    target.case_levels += source.levels_completed
    target.induction_proposals += source.induction_proposals
    target.recursive_lift_proposals += source.recursive_lift_proposals
    target.recursive_lift_clauses += source.recursive_lift_clauses
    target.recursive_lift_inference_queries += source.recursive_lift_inference_queries
    target.recursive_lift_inference_failures += source.recursive_lift_inference_failures
    target.recursive_lift_family_candidates += source.recursive_lift_family_candidates
    target.recursive_function_abstractions += source.recursive_function_abstractions
    target.recursive_function_lift_queries += source.recursive_function_lift_queries
    target.recursive_subject_search_actions += source.recursive_subject_search_actions
    target.recursive_subject_inference_queries += (
        source.recursive_subject_inference_queries
    )
    target.recursive_subjects_generated += source.recursive_subjects_generated
    target.recursive_catalog_queries += source.recursive_catalog_queries
    target.recursive_wrappers_generated += source.recursive_wrappers_generated
    target.recursive_applications_generated += source.recursive_applications_generated
    target.recursive_inference_queries += source.recursive_inference_queries
    target.recursive_applications_inferred += source.recursive_applications_inferred
    target.recursive_applications_pruned += source.recursive_applications_pruned
    target.recursive_compositions_generated += source.recursive_compositions_generated
    target.recursive_composition_inference_queries += (
        source.recursive_composition_inference_queries
    )
    target.recursive_compositions_inferred += source.recursive_compositions_inferred
    target.recursive_proof_checks += source.recursive_proof_checks
    remaining_recursive_slots = max(0, 64 - len(target.recursive_actions))
    target.recursive_actions.extend(
        source.recursive_actions[:remaining_recursive_slots]
    )
    target.relation_saturation_queries += source.relation_saturation_queries
    target.relation_saturation_edges += source.relation_saturation_edges
    remaining_saturation_slots = max(0, 64 - len(target.relation_saturation_actions))
    target.relation_saturation_actions.extend(
        source.relation_saturation_actions[:remaining_saturation_slots]
    )
    target.local_refinement_candidates += source.local_refinement_candidates
    target.local_refinement_queries += source.local_refinement_queries
    target.skeleton_queries += source.skeleton_queries
    target.skeleton_candidates += source.skeleton_candidates
    target.skeleton_frontier_peak = max(
        target.skeleton_frontier_peak, source.skeleton_frontier_peak
    )
    remaining_skeleton_slots = max(
        0, _MAX_RECORDED_SKELETON_ATTEMPTS - len(target.skeleton_attempts)
    )
    retained_skeleton_attempts = source.skeleton_attempts[:remaining_skeleton_slots]
    target.skeleton_attempts.extend(retained_skeleton_attempts)
    target.skeleton_attempts_omitted += (
        source.skeleton_attempts_omitted
        + len(source.skeleton_attempts)
        - len(retained_skeleton_attempts)
    )
    remaining_order_slots = max(0, 64 - len(target.constructor_orders))
    target.constructor_orders.extend(source.constructor_orders[:remaining_order_slots])
    target.dependency_towers_built += source.dependency_towers_built
    target.dependency_planning_fallbacks += source.dependency_planning_fallbacks
    target.dependency_guided_splits += source.dependency_guided_splits
    target.max_dependency_depth = max(
        target.max_dependency_depth, source.max_dependency_depth
    )
    target.proof_relevant_nodes_observed += source.proof_relevant_nodes_observed
    target.parallel_inhabitants_observed += source.parallel_inhabitants_observed
    remaining_elimination_slots = max(
        0, _MAX_RECORDED_ELIMINATION_ACTIONS - len(target.elimination_actions)
    )
    retained_elimination_actions = source.elimination_actions[
        :remaining_elimination_slots
    ]
    target.elimination_actions.extend(retained_elimination_actions)
    target.elimination_actions_omitted += (
        source.elimination_actions_omitted
        + len(source.elimination_actions)
        - len(retained_elimination_actions)
    )
    target.generated_subgoals += source.generated_subgoals
    target.goal_inspections += source.goal_inspections
    target.kernel_loads += source.kernel_loads
    target.kernel_load_elapsed_ms += source.kernel_load_elapsed_ms
    target.model_calls += source.model_calls
    target.model_batches += source.model_batches
    target.model_elapsed_ms += source.model_elapsed_ms
    for name, value in source.focused.items():
        target.focused[name] = target.focused.get(name, 0) + value
    target.source_bytes_materialized += source.source_bytes_materialized
    target.source_bytes_written += source.source_bytes_written
    return (
        source.refinement_queries
        + source.case_queries
        + source.proof_checks
        + source.constructor_catalog_queries
        + source.premise_catalog_queries
        + source.completion_queries
        + source.recursive_inference_queries
        + source.recursive_subject_inference_queries
        + source.recursive_catalog_queries
        + source.recursive_composition_inference_queries
        + source.recursive_lift_inference_queries
        + source.recursive_function_lift_queries
        + source.evidence_inference_queries
        + source.evidence_path_queries
    )


def _rank_terms(
    goal: GoalInfo, terms: tuple[Term, ...], model: ProofTermRanker | None
) -> tuple[Term, ...]:
    if model is None or len(terms) <= 1:
        return terms
    scores = model.score_terms(goal, terms)
    return tuple(
        term
        for term, _score in sorted(
            zip(terms, scores, strict=True),
            key=lambda item: (-float(item[1]), symbolic_key(goal.target, item[0])),
        )
    )


def _needs_joint_alternatives(
    source: str,
    goal: GoalInfo,
    region_end: int,
    source_file: Path | None = None,
) -> bool:
    """Whether a later selected declaration can observe this definition.

    If the declaration name does not occur after its own clause and before the
    joint cutoff, its alternative inhabitants cannot affect a later selected
    goal. Literate prose is excluded from the lexical observation without
    changing physical source positions. Comments and strings conservatively
    retain alternatives, just as they do for ordinary Agda source.
    """

    visible_source = (
        mask_literate_markdown(source)
        if source_file is not None and agda_source_suffix(source_file) == ".lagda.md"
        else source
    )
    hole_start = goal.source_range[0] - 1
    line_start = visible_source.rfind("\n", 0, hole_start) + 1
    prefix = visible_source[line_start:hole_start]
    equals = prefix.rfind("=")
    if equals < 0:
        return True
    lhs = prefix[:equals].strip()
    if not lhs:
        return True
    name = lhs.split()[0]
    line_end = visible_source.find("\n", goal.source_range[1] - 1)
    if line_end < 0:
        line_end = goal.source_range[1] - 1
    suffix = visible_source[line_end:region_end]
    notation = binary_mixfix_notation(name)
    if notation is not None:
        # A mixfix declaration is defined as ``_op_`` but ordinarily used as
        # the surface token ``op``.  Compare the latter so later constraints
        # retain the definition's recursive alternatives.
        return notation.surface_operator in suffix
    if name.isidentifier() or all(
        character.isalnum() or character in "_'-" for character in name
    ):
        return (
            re.search(
                rf"(?<![\w'-]){re.escape(name)}(?![\w'-])",
                suffix,
            )
            is not None
        )
    return name in suffix


def _declaration_signature(source: str, goal: GoalInfo) -> tuple[str, str] | None:
    """Return the owning declaration and its displayed type before GOAL.

    This is a scheduling observation only.  Agda still supplies every live
    goal and validates every edit; failure to recover a signature simply
    preserves source-order search.
    """

    try:
        name = declaration_name_at_goal(source, goal)
    except ValueError:
        return None
    hole_start = goal.source_range[0] - 1
    if not name or not 0 <= hole_start <= len(source):
        return None
    matches = tuple(
        re.finditer(
            rf"(?m)^[ \t]*{re.escape(name)}[ \t]*:[ \t]*",
            source[:hole_start],
        )
    )
    if not matches:
        return None
    match = matches[-1]
    assignment_start = source.rfind("\n", 0, hole_start) + 1
    if assignment_start <= match.end():
        return None
    return name, source[match.end() : assignment_start]


def _mentions_declaration(text: str, name: str) -> bool:
    notation = binary_mixfix_notation(name)
    token = notation.surface_operator if notation is not None else name
    if token.isidentifier() or all(
        character.isalnum() or character in "_'-" for character in token
    ):
        return (
            re.search(
                rf"(?<![\w'-]){re.escape(token)}(?![\w'-])",
                text,
            )
            is not None
        )
    return token in text


def _select_dependency_ready_goal(
    source: str,
    remaining_goals: tuple[GoalInfo, ...],
    selected_declarations: frozenset[str],
) -> GoalInfo | None:
    """Prefer a law as soon as all provisional declarations it observes exist.

    Interleaving a definition with its first ready observation prevents joint
    search from constructing an unrelated cross-product of provisional
    definitions.  The dependency relation is deliberately conservative and
    lexical; it changes ordering only, never visibility, typing, or the set of
    generated actions.
    """

    signatures = tuple(
        recovered
        for goal in remaining_goals
        for recovered in (_declaration_signature(source, goal),)
        if recovered is not None
    )
    remaining_names = {name for name, _signature in signatures}
    completed_names = set(selected_declarations) - remaining_names
    if not completed_names:
        return None
    ordered_goals = sorted(remaining_goals, key=lambda item: item.source_range)
    source_first = ordered_goals[0]
    for goal in ordered_goals:
        recovered = _declaration_signature(source, goal)
        if recovered is None:
            continue
        _name, signature = recovered
        dependencies = {
            declaration
            for declaration in selected_declarations
            if _mentions_declaration(signature, declaration)
        }
        if dependencies and dependencies <= completed_names:
            try:
                result = split_top_level_arrows(signature)[-1]
            except ValueError:
                return None
            relation = parse_relation(result)
            if relation is None:
                return None
            left = strip_outer_parentheses(relation.left)
            right = strip_outer_parentheses(relation.right)
            if any(
                (
                    normalize_type_text(left) == normalize_type_text(declaration)
                    or normalize_type_text(right) == normalize_type_text(declaration)
                    or (
                        _is_head_application(left, declaration)
                        != _is_head_application(right, declaration)
                    )
                )
                for declaration in dependencies
            ):
                # Source-order search will select this goal anyway.  Marking
                # it as an interleaved constraint would needlessly impose the
                # narrow observation budget and enqueue a widening twin.
                return None if goal is source_first else goal
            # An algebraic law on both endpoints ends the contiguous block of
            # direct computation observations.  Do not jump past it to treat
            # a later unit or absorption law as a defining equation.
            return None
    return None


def _observed_nullary_definition_candidates(
    source: str,
    remaining_goals: tuple[GoalInfo, ...],
    declaration: str,
) -> tuple[str, ...]:
    """Read exact nullary values from later, explicit observation laws.

    A constraint such as ``observe-c : c ~ constructor ...`` is semantic
    evidence for a candidate value of ``c``.  This is deliberately polymorphic
    in the carrier, relation, and term shape: Agda parses the observation and
    remains the sole authority that the proposed endpoint inhabits the current
    goal.  If the observation is absent or ambiguous, ordinary bounded search
    remains available through progressive widening.
    """

    wanted = normalize_type_text(declaration)
    candidates: list[str] = []
    for later_goal in remaining_goals:
        recovered = _declaration_signature(source, later_goal)
        if recovered is None:
            continue
        _later_name, signature = recovered
        try:
            result = split_top_level_arrows(signature)[-1]
        except ValueError:
            continue
        relation = parse_relation(result)
        if relation is None:
            continue
        left = strip_outer_parentheses(relation.left)
        right = strip_outer_parentheses(relation.right)
        if normalize_type_text(left) == wanted:
            candidates.append(right)
        if normalize_type_text(right) == wanted:
            candidates.append(left)
    return tuple(dict.fromkeys(candidates))


def _is_head_application(expression: str, declaration: str) -> bool:
    """Whether DECLARATION is the outer displayed head of EXPRESSION."""

    terms = _top_level_surface_terms(strip_outer_parentheses(expression))

    def is_operator_token(term: str) -> bool:
        stripped = term.strip()
        if not stripped or stripped[0] in "([{⦃":
            return False
        return not all(
            character.isalnum() or character in "_'.-" for character in stripped
        )

    notation = binary_mixfix_notation(declaration)
    if notation is not None:
        outer_operators = tuple(term for term in terms[1:-1] if is_operator_token(term))
        return outer_operators == (notation.surface_operator,)
    return (
        bool(terms)
        and terms[0] == declaration
        and not any(is_operator_token(term) for term in terms[1:])
    )


def _function_observation_relation(
    result: str, declaration: str
) -> RelationView | None:
    """Find the outer relation around one displayed function application."""

    notation = binary_mixfix_notation(declaration)
    function_token = notation.surface_operator if notation is not None else None
    primary = parse_relation(result)
    if primary is not None:
        if _is_head_application(primary.left, declaration) or _is_head_application(
            primary.right, declaration
        ):
            return primary
        if function_token is None or primary.operator != function_token:
            return None
    for token in _top_level_surface_terms(result)[1:-1]:
        if token == function_token or token.isidentifier():
            continue
        relation = parse_relation(
            result,
            expected_operator=token,
        )
        if relation is None:
            continue
        left_head = _is_head_application(relation.left, declaration)
        right_head = _is_head_application(relation.right, declaration)
        if left_head or right_head:
            return relation
    return None


def _observed_function_equations(
    source: str,
    remaining_goals: tuple[GoalInfo, ...],
    declaration: str,
) -> tuple[str, ...]:
    """Recover an initial constructor-equation block for a function.

    Only relations with the function as the outer head of exactly one endpoint
    contribute a clause.  Once a law places the function at both endpoints,
    the defining block is complete and algebraic consequences are ignored.
    This separates explicit computation rules from associativity-like laws
    without naming either the datatype or the operation.
    """

    equations: list[str] = []
    remaining_names = {
        recovered[0]
        for later_goal in remaining_goals
        for recovered in (_declaration_signature(source, later_goal),)
        if recovered is not None
    }

    def has_rigid_mixfix_operand(expression: str, signature: str) -> bool:
        notation = binary_mixfix_notation(declaration)
        if notation is None:
            return True
        variables: set[str] = set()
        try:
            domains = split_top_level_arrows(signature)[:-1]
        except ValueError:
            domains = ()
        for domain in domains:
            for group in split_adjacent_binders(domain) or (domain,):
                try:
                    parsed = parse_named_binder(group)
                except ValueError:
                    parsed = None
                if parsed is not None:
                    variables.update(parsed.names)
        terms = _top_level_surface_terms(strip_outer_parentheses(expression))
        try:
            operator_index = terms.index(notation.surface_operator)
        except ValueError:
            return False
        operands = (
            " ".join(terms[:operator_index]),
            " ".join(terms[operator_index + 1 :]),
        )
        return any(
            bool(operand_terms)
            and strip_outer_parentheses(operand_terms[0]) not in variables
            for operand in operands
            for operand_terms in (
                _top_level_surface_terms(strip_outer_parentheses(operand)),
            )
        )

    for later_goal in remaining_goals:
        recovered = _declaration_signature(source, later_goal)
        if recovered is None:
            continue
        _later_name, signature = recovered
        try:
            result = split_top_level_arrows(signature)[-1]
        except ValueError:
            continue
        relation = _function_observation_relation(result, declaration)
        if relation is None:
            if equations:
                break
            continue
        left = strip_outer_parentheses(relation.left)
        right = strip_outer_parentheses(relation.right)
        left_head = _is_head_application(left, declaration)
        right_head = _is_head_application(right, declaration)
        if left_head and right_head:
            # The first relation that observes the function on both sides is
            # already an algebraic law, even when no computation equation has
            # preceded it.  It closes the only contiguous observation block;
            # later unit/absorption laws must not be reinterpreted as defining
            # clauses merely because one operand happens to be rigid.
            break
        if left_head:
            if not has_rigid_mixfix_operand(left, signature):
                if equations:
                    break
                continue
            if any(
                name != declaration and _mentions_declaration(right, name)
                for name in remaining_names
            ):
                if equations:
                    break
                continue
            equations.append(f"{left} = {right}")
        elif right_head:
            if not has_rigid_mixfix_operand(right, signature):
                if equations:
                    break
                continue
            if any(
                name != declaration and _mentions_declaration(left, name)
                for name in remaining_names
            ):
                if equations:
                    break
                continue
            equations.append(f"{right} = {left}")
    unique_equations = tuple(dict.fromkeys(equations))
    if len(unique_equations) == 1:
        _left, separator, right = unique_equations[0].partition(" = ")
        bare_endpoint = strip_outer_parentheses(right)
        if (
            separator
            and len(_top_level_surface_terms(bare_endpoint)) == 1
            and not _mentions_declaration(right, declaration)
        ):
            # One isolated constructor-shaped law is equally compatible with
            # an algebraic unit and a computation rule in the opposite
            # recursion coordinate when its result is only a bare variable.
            # Treat it as insufficient evidence.  Ordinary kernel-guided
            # elimination still covers nonrecursive one-constructor functions,
            # while constructor-shaped unary observations remain available.
            return ()
    return unique_equations


def _top_level_surface_terms(text: str) -> tuple[str, ...]:
    """Split an Agda surface fragment at unparenthesized whitespace."""

    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    stack: list[str] = []
    terms: list[str] = []
    start: int | None = None
    stripped = text.strip()
    for index, character in enumerate(stripped):
        if character in pairs:
            stack.append(pairs[character])
        elif character in closing and stack and stack[-1] == character:
            stack.pop()
        if character.isspace() and not stack:
            if start is not None:
                terms.append(stripped[start:index])
                start = None
        elif start is None:
            start = index
    if start is not None:
        terms.append(stripped[start:])
    return tuple(terms)


def _observed_binary_argument_order(
    source: str,
    remaining_goals: tuple[GoalInfo, ...],
    declaration: str,
) -> tuple[int, int] | None:
    """Rank binary recursion coordinates from later constructor observations.

    A displayed law such as ``op (constructor x) y = ...`` provides a
    representation-neutral reason to try the first coordinate before a law
    that mentions only variables.  This is an ordering hint over the complete
    coordinate set; malformed or ambiguous surface syntax falls back to the
    stable historical order.
    """

    notation = binary_mixfix_notation(declaration)
    if notation is None:
        return None
    scores = [0, 0]
    for goal in remaining_goals:
        recovered = _declaration_signature(source, goal)
        if recovered is None:
            continue
        _name, signature = recovered
        if not _mentions_declaration(signature, declaration):
            continue
        variables: set[str] = set()
        try:
            telescope = split_top_level_arrows(signature)[:-1]
        except ValueError:
            telescope = ()
        for part in telescope:
            for group in split_adjacent_binders(part) or (part,):
                try:
                    binder = parse_named_binder(group)
                except ValueError:
                    binder = None
                if binder is not None:
                    variables.update(binder.names)
        terms = _top_level_surface_terms(signature)
        for index, term in enumerate(terms):
            if (
                term != notation.surface_operator
                or index == 0
                or index + 1 >= len(terms)
            ):
                continue
            operands = (
                strip_outer_parentheses(terms[index - 1]),
                strip_outer_parentheses(terms[index + 1]),
            )
            for position, operand in enumerate(operands):
                if operand and operand not in variables:
                    scores[position] += 1
    if scores[0] == scores[1]:
        return None
    return (0, 1) if scores[0] > scores[1] else (1, 0)


def _observed_recursive_composition_order(
    source: str,
    remaining_goals: tuple[GoalInfo, ...],
    declaration: str,
) -> bool | None:
    """Whether a later equation places the unchanged local before recursion."""

    notation = binary_mixfix_notation(declaration)
    if notation is None:
        return None
    local_first_votes = 0
    recursive_first_votes = 0
    for goal in remaining_goals:
        recovered = _declaration_signature(source, goal)
        if recovered is None:
            continue
        _name, signature = recovered
        if not _mentions_declaration(signature, declaration):
            continue
        variables: set[str] = set()
        try:
            telescope = split_top_level_arrows(signature)[:-1]
        except ValueError:
            telescope = ()
        for part in telescope:
            for group in split_adjacent_binders(part) or (part,):
                try:
                    binder = parse_named_binder(group)
                except ValueError:
                    binder = None
                if binder is not None:
                    variables.update(binder.names)
        terms = _top_level_surface_terms(signature)
        for index in range(1, len(terms) - 1):
            operator = terms[index]
            if operator in {"→", "=", "≡", "＝", notation.surface_operator}:
                continue
            left = strip_outer_parentheses(terms[index - 1])
            right = strip_outer_parentheses(terms[index + 1])
            left_recursive = notation.surface_operator in left
            right_recursive = notation.surface_operator in right
            if left_recursive == right_recursive:
                continue
            if right_recursive and left in variables:
                local_first_votes += 1
            elif left_recursive and right in variables:
                recursive_first_votes += 1
    if local_first_votes == recursive_first_votes:
        return None
    return local_first_votes > recursive_first_votes


def _owning_declaration_name(source: str, goal: GoalInfo) -> str | None:
    """Recover the clause head even when the goal is nested in its RHS."""

    try:
        return declaration_name_at_goal(source, goal)
    except ValueError:
        hole_start = goal.source_range[0] - 1
        if not 0 <= hole_start <= len(source):
            return None
        line_start = source.rfind("\n", 0, hole_start) + 1
        prefix = source[line_start:hole_start]
        equals = prefix.find("=")
        if equals < 0:
            return None
        parts = prefix[:equals].strip().split()
        return parts[0] if parts else None


def _is_lambda_projection(term: Term) -> bool:
    """Whether TERM only returns one of its introduced arguments."""

    binders = 0
    current = term
    while current.tag == "lambda" and current.body is not None:
        binders += 1
        current = current.body
    return bool(
        binders
        and current.tag == "bound"
        and current.index is not None
        and current.index < binders
    )


def _is_lambda_constant(term: Term) -> bool:
    """Whether an introduced function ignores every bound argument."""

    if term.tag != "lambda":
        return False

    def uses_bound(node: Term) -> bool:
        if node.tag == "bound":
            return True
        return any(
            child is not None and uses_bound(child)
            for child in (node.function, node.argument, node.body)
        )

    return not uses_bound(term)


def prove_joint_prefix(
    task: TaskSpec,
    *,
    session_factory: KernelSessionFactory = AgdaSession,
    progress_observer: PrincipalVariationObserver | None = None,
) -> ProverResult:
    """Solve every original open goal through a source-order cutoff atomically.

    Earlier definitions remain search alternatives until all selected later
    declarations elaborate and close.  A later dead end therefore backtracks
    to a different earlier definition instead of committing a locally valid
    proof prematurely.
    """

    started = time.monotonic()
    source_file = task.source_file.resolve()
    result = ProverResult(
        task_id=task_identity(
            task,
            "",
            mode="prove-prefix",
            policy_profile="p0-joint-prefix-search-v1",
            toolchain_id=None,
            model_ids={"primary": None, "refinement": None},
        ),
        status="internal-error",
        source_file=str(source_file),
        source_hash="",
        ranker=task.ranker,
        policy_profile="p0-joint-prefix-search-v1",
    )
    stats = JointStats(
        depth_limit=task.max_depth,
        budget_widening_enabled=os.environ.get("AGDAPROVER_JOINT_BUDGET_WIDENING", "1")
        != "0",
        contextual_evidence_enabled=os.environ.get(
            "AGDAPROVER_CONTEXTUAL_EVIDENCE", "1"
        )
        != "0",
    )
    policy_router: ORPolicyRouter | None = None
    selected_policy_choices: tuple[PolicyChoice, ...] = ()
    focused_policy = None
    call_scope = VerifierCallScope()
    resource_scope = ResourceScope(task.resources, memory_sample=current_process_rss)
    try:
        resource_scope.open()
        call_scope.open(task.max_verifier_calls)
        require_agda_source_file(source_file)
        if (
            task.max_candidates <= 0
            or task.max_term_size <= 0
            or (task.timeout_seconds is not None and task.timeout_seconds <= 0)
            or (task.max_depth is not None and task.max_depth < 0)
        ):
            raise ValueError("budgets must be positive")
        budget = SearchBudget(
            task.max_candidates, task.timeout_seconds, started_at=started
        )
        assert_offline_configuration(task, deadline=budget.deadline)
        original_source = source_file.read_text()
        result.source_hash = file_sha256(source_file, deadline=budget.deadline)
        configured_ids = configured_model_ids(task, deadline=budget.deadline)
        result.task_id = task_identity(
            task,
            result.source_hash,
            mode="prove-prefix",
            policy_profile=result.policy_profile,
            toolchain_id=None,
            model_ids=configured_ids,
        )

        models = load_proof_models(
            task, deadline=budget.deadline, command="prove-prefix"
        )
        term_model = models.term
        focused_model = models.focused
        refinement_model = models.refinement
        result.model_id = models.primary_id
        result.action_model_id = models.refinement_id
        focused_policy = None

        with temporary_workspace(prefix="agdaprover-joint-") as temporary:
            overlay_root = Path(temporary)
            workspace = prepare_project_overlay(
                source_file,
                original_source,
                overlay_root,
                project_configuration=task.project_configuration,
                timeout_seconds=budget.require_time("initial project overlay"),
            )
            candidate_path, _overlay_files = workspace.source_file, workspace.files
            with open_kernel_session(
                session_factory,
                project_configuration=workspace.configuration,
                timeout_seconds=budget.require_time("initial Agda load"),
                deadline=budget.deadline,
            ) as session:
                result.toolchain_id = session.toolchain_id
                result.task_id = task_identity(
                    task,
                    result.source_hash,
                    mode="prove-prefix",
                    policy_profile=result.policy_profile,
                    toolchain_id=result.toolchain_id,
                    project_inputs_id=workspace.inputs.identity
                    if workspace.inputs is not None
                    else None,
                    model_ids={
                        "primary": result.model_id,
                        "refinement": result.action_model_id,
                    },
                )
                policy_router = ORPolicyRouter(
                    focused_model=focused_model,
                    refinement_model=refinement_model,
                    recorder=PolicyTraceRecorder(),
                    budget_envelope=search_budget_envelope(task),
                    provenance={
                        "source_file": str(source_file),
                        "source_sha256": result.source_hash,
                        "agda_version": session.version,
                        "toolchain_id": result.toolchain_id,
                        "policy_profile": result.policy_profile,
                        "ranker": task.ranker,
                    },
                )
                focused_policy = policy_router.focused_policy
                load_started = time.monotonic()
                original_goals = session.load_module(
                    candidate_path
                    if workspace.configuration is not None
                    else source_file
                )
                stats.kernel_loads += 1
                stats.kernel_load_elapsed_ms += (
                    time.monotonic() - load_started
                ) * 1000.0
                cutoff, target_goals = choose_goal_prefix(original_goals, task)
                stats.target_goals = len(target_goals)
                selected_declarations = frozenset(
                    name
                    for target_goal in target_goals
                    for recovered in (
                        _declaration_signature(original_source, target_goal),
                    )
                    if recovered is not None
                    for name in (recovered[0],)
                )
                inspected_cutoff = attach_module_scope(
                    session.inspect_goal(cutoff), original_source, source_file
                )
                policy_router.provenance["module_scope_id"] = (
                    inspected_cutoff.module_scope.scope_id
                    if inspected_cutoff.module_scope is not None
                    else None
                )
                stats.goal_inspections += 1
                result.goal = inspected_cutoff.to_dict()
                result.joint_goals = [
                    attach_module_scope(goal, original_source, source_file).to_dict()
                    for goal in target_goals
                ]

                first_start = target_goals[0].source_range[0] - 1
                region_start = original_source.rfind("\n", 0, first_start) + 1
                initial_end = cutoff.source_range[1] - 1
                if not region_start < initial_end:
                    raise ValueError("selected joint goal prefix has an invalid range")

                sequence = 0
                initial_replacement = original_source[region_start:initial_end]
                queue = BatchedFrontier[_State]()
                # Resume these only once the ordinary frontier is empty. A
                # successful fast path keeps its original scheduling and incurs
                # no speculative checker calls to qualify a proposed term.
                focused_fallbacks: list[tuple[_State, int]] = []
                initial_state = _State(
                    (len(target_goals), 0, 0, sequence),
                    sequence,
                    initial_replacement,
                    0,
                    (),
                )
                queue.push(
                    initial_state.priority, initial_state.sequence, initial_state
                )
                stats.states_enqueued = 1
                stats.frontier_peak = 1
                queued = {_search_state_digest(initial_replacement, frozenset())}
                seen: set[str] = set()
                saw_exhaustion = False

                def publish_variation(
                    state: _State,
                    remaining: tuple[GoalInfo, ...],
                    active: GoalInfo | None,
                ) -> None:
                    if progress_observer is None:
                        return
                    try:
                        progress_observer(
                            joint_principal_variation(
                                task_id=result.task_id,
                                source_file=source_file,
                                source_sha256=result.source_hash,
                                target_goals=target_goals,
                                remaining_goals=remaining,
                                active_goal=active,
                                priority=state.priority,
                                depth=state.depth,
                                steps=state.steps,
                                states_expanded=stats.states_expanded,
                                frontier_size=len(queue) + len(focused_fallbacks),
                                original_source=original_source,
                            )
                        )
                    except VerifierCallLimitExceeded:
                        raise
                    except Exception:
                        # Progress is observational and must never change proof
                        # search or fresh-validation semantics.
                        return

                def enqueue(
                    state_source: str,
                    state_region_end: int,
                    depth: int,
                    estimated_goals: int,
                    steps: tuple[dict[str, object], ...],
                    *,
                    policy_choices: tuple[PolicyChoice, ...],
                    priority_bias: int = 0,
                    widened_declarations: frozenset[str] = frozenset(),
                    budget_widened: bool = False,
                    skip_focused: bool = False,
                ) -> None:
                    nonlocal saw_exhaustion, sequence
                    replacement = state_source[region_start:state_region_end]
                    digest = _search_state_digest(
                        replacement, widened_declarations, budget_widened, skip_focused
                    )
                    if digest in seen or digest in queued:
                        stats.transposition_hits += 1
                        return
                    if len(queue) >= task.max_candidates:
                        stats.frontier_pruned += 1
                        saw_exhaustion = True
                        return
                    if len(queue) + len(focused_fallbacks) >= task.max_candidates:
                        # Deferred work must not displace an ordinary candidate
                        # at a tight frontier limit. Retain the resource refusal
                        # if the surviving candidates subsequently fail.
                        focused_fallbacks.pop()
                        stats.frontier_pruned += 1
                        saw_exhaustion = True
                    sequence += 1
                    queued.add(digest)
                    remaining = max(0, estimated_goals)
                    next_state = _State(
                        (remaining, priority_bias, depth, sequence),
                        sequence,
                        replacement,
                        depth,
                        steps,
                        widened_declarations,
                        budget_widened,
                        policy_choices,
                        skip_focused,
                    )
                    queue.push(next_state.priority, next_state.sequence, next_state)
                    stats.states_enqueued += 1
                    stats.frontier_peak = max(
                        stats.frontier_peak, len(queue) + len(focused_fallbacks)
                    )

                # Independent focused goals form one speculative source batch.
                # The original state remains queued as a complete fallback, so
                # Agda rejection loses only this optimization, not completeness.
                batch_source = original_source
                batch_edits: list[dict[str, object]] = []
                for shallow_goal in target_goals:
                    if goal_has_dependency_tower(
                        shallow_goal
                    ) or _needs_joint_alternatives(
                        original_source, shallow_goal, initial_end, source_file
                    ):
                        continue
                    remaining_actions = budget.remaining_actions()
                    if remaining_actions <= 0:
                        break
                    batch_focused = focused_candidates(
                        shallow_goal,
                        action_budget=remaining_actions,
                        solution_limit=1,
                        timeout_seconds=budget.require_time(
                            "joint independent focused batch"
                        ),
                        max_depth=task.max_depth,
                        branch_scorer=(
                            policy_router.score_focused
                            if focused_policy is not None
                            else None
                        ),
                        batch_invertible=True,
                    )
                    budget.account_actions(batch_focused.stats.actions_considered)
                    stats.actions_considered += batch_focused.stats.actions_considered
                    stats.actions_generated += batch_focused.stats.actions_generated
                    stats.model_calls += batch_focused.stats.model_calls
                    stats.model_batches += batch_focused.stats.policy_nodes
                    stats.model_elapsed_ms += batch_focused.stats.model_elapsed_ms
                    for name in (
                        "nodes_expanded",
                        "cache_hits",
                        "cycles_pruned",
                        "depth_pruned",
                    ):
                        stats.focused[name] = int(stats.focused.get(name, 0)) + int(
                            getattr(batch_focused.stats, name)
                        )
                    if not batch_focused.terms:
                        continue
                    term = batch_focused.terms[0]
                    try:
                        edit = reconstruct_term_as_clause(
                            original_source,
                            shallow_goal,
                            term,
                            forbidden_names=(
                                entry.name for entry in shallow_goal.context
                            ),
                        )
                    except ValueError:
                        continue
                    if _edit_within_region(
                        edit, region_start=region_start, region_end=initial_end
                    ):
                        batch_edits.append(edit)

                if batch_edits and (
                    task.max_depth is None or len(batch_edits) <= task.max_depth
                ):
                    batch_end = initial_end
                    for edit in reversed(batch_edits):
                        batch_source = apply_source_edit(batch_source, edit)
                        batch_end += len(str(edit["replacement"])) - len(
                            str(edit["original"])
                        )
                    enqueue(
                        batch_source,
                        batch_end,
                        len(batch_edits),
                        len(target_goals) - len(batch_edits),
                        tuple(reversed(batch_edits)),
                        policy_choices=(),
                    )
                    stats.focused_batches += 1
                    stats.focused_batch_goals += len(batch_edits)

                pending_widening: _DeferredBudgetWidening | None = None
                while queue or pending_widening is not None or focused_fallbacks:
                    if pending_widening is not None:
                        previous = pending_widening
                        pending_widening = None
                        if previous.exhausted(stats.actions_considered):
                            # Only a censored expansion needs a wider replay.
                            # Replaying successful short expansions duplicates
                            # work and can outrank their newly exposed children.
                            enqueue(
                                previous.source,
                                previous.region_end,
                                previous.state.depth,
                                previous.remaining_goals,
                                previous.state.steps,
                                policy_choices=previous.state.policy_choices,
                                priority_bias=8,
                                widened_declarations=previous.state.widened_declarations,
                                budget_widened=True,
                                skip_focused=previous.state.skip_focused,
                            )
                            stats.budget_widening_fallbacks += 1
                    if not queue and focused_fallbacks:
                        fallback, open_count = focused_fallbacks.pop()
                        enqueue(
                            original_source[:region_start]
                            + fallback.replacement
                            + original_source[initial_end:],
                            region_start + len(fallback.replacement),
                            fallback.depth,
                            open_count,
                            fallback.steps,
                            policy_choices=fallback.policy_choices,
                            priority_bias=8,
                            widened_declarations=fallback.widened_declarations,
                            budget_widened=fallback.budget_widened,
                            skip_focused=True,
                        )
                        stats.focused_fallbacks_resumed += 1
                    if not queue:
                        continue
                    # Already-enqueued states may be terminal solutions, so an
                    # exhausted action allowance stops further expansion but
                    # does not prevent their final kernel load.
                    if budget.wall_exhausted():
                        saw_exhaustion = True
                        break
                    state = queue.pop()
                    digest = _search_state_digest(
                        state.replacement,
                        state.widened_declarations,
                        state.budget_widened,
                        state.skip_focused,
                    )
                    queued.discard(digest)
                    if digest in seen:
                        stats.transposition_hits += 1
                        continue
                    seen.add(digest)
                    stats.states_expanded += 1
                    stats.max_depth = max(stats.max_depth, state.depth)
                    state_source = (
                        original_source[:region_start]
                        + state.replacement
                        + original_source[initial_end:]
                    )
                    state_region_end = region_start + len(state.replacement)
                    encoded_size = len(state_source.encode("utf-8"))
                    stats.source_bytes_materialized += encoded_size
                    candidate_path.write_text(state_source)
                    charge_io(len(state_source.encode()))
                    stats.source_bytes_written += encoded_size
                    load_started = time.monotonic()
                    try:
                        loaded = session.load_module(candidate_path)
                    except AgdaLoadError as error:
                        stats.dead_states += 1
                        if len(stats.dead_state_diagnostics) < 8:
                            stats.dead_state_diagnostics.append(str(error)[:2000])
                        continue
                    finally:
                        stats.kernel_loads += 1
                        stats.kernel_load_elapsed_ms += (
                            time.monotonic() - load_started
                        ) * 1000.0

                    remaining_goals = tuple(
                        goal
                        for goal in loaded
                        if region_start <= goal.source_range[0] - 1
                        and goal.source_range[1] - 1 <= state_region_end
                    )
                    if not remaining_goals:
                        publish_variation(state, (), None)
                        patch = reconstruct_joint_completion(
                            original_source,
                            start_offset=region_start,
                            end_offset=initial_end,
                            replacement=state.replacement,
                            target_goal_count=len(target_goals),
                            cutoff_position=cutoff.source_range[0],
                            steps=state.steps,
                        )
                        validation, trust_report = validate_reconstruction(
                            source_file,
                            patch,
                            agda_executable=session.executable,
                            agda_version=session.version,
                            project_configuration=task.project_configuration,
                            expected_inputs=workspace.inputs,
                            timeout_seconds=budget.require_time(
                                "fresh joint-proof validation"
                            ),
                        )
                        result.cost.add(
                            fresh_validation_runs=validation.get(
                                "fresh_validation_runs", 1
                            )
                        )
                        if validation["checked"]:
                            result.validation = validation
                            result.trust_report = trust_report
                            result.patch = patch
                            result.proof_term = state.replacement
                            result.status = "verified"
                            selected_policy_choices = state.policy_choices
                            result.diagnostics.append(
                                {
                                    "kind": "joint-search",
                                    "message": (
                                        f"jointly verified {len(target_goals)} goal"
                                        f"{'s' if len(target_goals) != 1 else ''} "
                                        "through the selected cutoff"
                                    ),
                                }
                            )
                        elif (
                            validation.get("prefix_validation", {}).get("status")
                            == "unavailable"
                        ):
                            result.status = "toolchain-error"
                            result.validation = validation
                            result.trust_report = trust_report
                            result.diagnostics.append(
                                {
                                    "kind": "toolchain",
                                    "message": "Prefix validation requires the Agda source parser; run scripts/build-source-parser or set AGDAPROVER_SOURCE_PARSER.",
                                }
                            )
                            break
                        elif (
                            validation["timed_out"]
                            or validation.get("prefix_validation", {}).get("status")
                            == "resource-exhausted"
                        ):
                            result.status = "resource-exhausted"
                            result.diagnostics.append(
                                {
                                    "kind": "resource",
                                    "message": "fresh joint validation exhausted its resource budget",
                                }
                            )
                        else:
                            # Transactional interaction checks do not run all
                            # whole-module obligations (notably termination).
                            # A rejected terminal proposal is therefore a dead
                            # search state, not an internal inconsistency.
                            stats.dead_states += 1
                            stats.terminal_validation_rejections += 1
                            if len(stats.dead_state_diagnostics) < 8:
                                stats.dead_state_diagnostics.append(
                                    validation["diagnostic"][:2000]
                                    or "fresh Agda rejected a terminal proposal"
                                )
                            continue
                        break

                    if task.max_depth is not None and state.depth >= task.max_depth:
                        stats.depth_pruned += 1
                        saw_exhaustion = True
                        continue

                    selected = _select_dependency_ready_goal(
                        state_source,
                        remaining_goals,
                        selected_declarations,
                    )
                    dependency_ready_selected = selected is not None
                    if selected is None:
                        selected = min(
                            remaining_goals, key=lambda goal: goal.source_range
                        )
                    else:
                        stats.dependency_ready_goals_selected += 1
                    goal = attach_module_scope(
                        session.inspect_goal(selected), state_source, source_file
                    )
                    stats.goal_inspections += 1
                    publish_variation(state, remaining_goals, goal)
                    retain_alternatives = _needs_joint_alternatives(
                        state_source, goal, state_region_end, source_file
                    )
                    owning_declaration = _owning_declaration_name(state_source, goal)
                    fully_widened = bool(
                        owning_declaration
                        and owning_declaration in state.widened_declarations
                    )
                    successor_widened = (
                        state.widened_declarations - {owning_declaration}
                        if owning_declaration is not None
                        else state.widened_declarations
                    )
                    if (
                        dependency_ready_selected
                        and not fully_widened
                        and owning_declaration is not None
                    ):
                        enqueue(
                            state_source,
                            state_region_end,
                            state.depth,
                            len(remaining_goals),
                            state.steps,
                            policy_choices=state.policy_choices,
                            priority_bias=8,
                            widened_declarations=(
                                state.widened_declarations | {owning_declaration}
                            ),
                            skip_focused=state.skip_focused,
                        )
                        stats.constraint_widening_fallbacks += 1
                    goal_action_start = stats.actions_considered
                    competing_alternatives = (
                        stats.budget_widening_enabled
                        and bool(queue)
                        and not state.budget_widened
                        and _can_amortize_budget_widening(
                            budget.remaining_actions(), len(remaining_goals)
                        )
                    )
                    goal_action_limit = (
                        160
                        if (dependency_ready_selected and not fully_widened)
                        or competing_alternatives
                        else task.max_candidates
                    )
                    if (
                        competing_alternatives
                        and budget.remaining_actions() > goal_action_limit
                    ):
                        # Finalize at the next loop boundary, including paths
                        # that finish early with a constructor or case proof.
                        pending_widening = _DeferredBudgetWidening(
                            state,
                            state_source,
                            state_region_end,
                            len(remaining_goals),
                            goal_action_start,
                            goal_action_limit,
                        )

                    def remaining_goal_actions(
                        current_goal_action_limit: int = goal_action_limit,
                        current_goal_action_start: int = goal_action_start,
                    ) -> int:
                        return min(
                            budget.remaining_actions(),
                            max(
                                0,
                                current_goal_action_limit
                                - (
                                    stats.actions_considered - current_goal_action_start
                                ),
                            ),
                        )

                    remaining_actions = remaining_goal_actions()
                    if remaining_actions <= 0:
                        saw_exhaustion = True
                        continue
                    if (
                        not fully_widened
                        and owning_declaration is not None
                        and top_level_arrow_count(goal.target) == 0
                        and isinstance(session, TransactionalKernelSession)
                    ):
                        observed_candidates = _observed_nullary_definition_candidates(
                            state_source,
                            remaining_goals,
                            owning_declaration,
                        )
                        observed_accepted = False
                        for expression in observed_candidates[:4]:
                            if remaining_goal_actions() <= 0:
                                break
                            stats.actions_generated += 1
                            stats.actions_considered += 1
                            stats.observed_definition_candidates += 1
                            stats.observed_definition_queries += 1
                            stats.refinement_queries += 1
                            result.verifier_calls += 1
                            checked = session.check_candidate(goal.goal_id, expression)
                            if not checked.accepted:
                                continue
                            next_source, edit = _replace_goal(
                                state_source, goal, expression
                            )
                            if not _edit_within_region(
                                edit,
                                region_start=region_start,
                                region_end=state_region_end,
                            ):
                                continue
                            delta = len(str(edit["replacement"])) - len(
                                str(edit["original"])
                            )
                            enqueue(
                                next_source,
                                state_region_end + delta,
                                state.depth + 1,
                                len(remaining_goals) - 1,
                                state.steps + (edit,),
                                policy_choices=state.policy_choices,
                                priority_bias=-6,
                                widened_declarations=successor_widened,
                            )
                            observed_accepted = True
                            break
                        if observed_accepted:
                            # Let the exact theory endpoint reach its
                            # observation without eagerly enumerating an
                            # unrelated constructor forest.  Ambiguous
                            # observations are filtered before this point.
                            continue
                    elif (
                        not fully_widened
                        and owning_declaration is not None
                        and top_level_arrow_count(goal.target) > 0
                    ):
                        observed_equations = _observed_function_equations(
                            state_source,
                            remaining_goals,
                            owning_declaration,
                        )
                        if observed_equations and remaining_goal_actions() > 0:
                            stats.actions_generated += 1
                            stats.actions_considered += 1
                            stats.observed_equation_candidates += 1
                            try:
                                observed_edit = reconstruct_case_split(
                                    state_source, goal, observed_equations
                                )
                            except ValueError:
                                observed_edit = None
                            if observed_edit is not None and _edit_within_region(
                                observed_edit,
                                region_start=region_start,
                                region_end=state_region_end,
                            ):
                                next_source = apply_source_edit(
                                    state_source, observed_edit
                                )
                                delta = len(str(observed_edit["replacement"])) - len(
                                    str(observed_edit["original"])
                                )
                                enqueue(
                                    next_source,
                                    state_region_end + delta,
                                    state.depth + 1,
                                    len(remaining_goals) - 1,
                                    state.steps + (observed_edit,),
                                    policy_choices=state.policy_choices,
                                    priority_bias=-5,
                                    widened_declarations=successor_widened,
                                )
                                # Follow the complete, conservatively selected
                                # constructor-observation block before broader
                                # structural enumeration.
                                continue
                    solution_limit = remaining_actions if retain_alternatives else 1
                    focused = (
                        FocusedCandidatesResult("no-proof", (), FocusedStats())
                        if state.skip_focused
                        else focused_candidates(
                            goal,
                            action_budget=remaining_actions,
                            solution_limit=solution_limit,
                            timeout_seconds=budget.require_time(
                                "joint focused alternatives"
                            ),
                            max_depth=(
                                None
                                if task.max_depth is None
                                else task.max_depth - state.depth
                            ),
                            branch_scorer=(
                                policy_router.score_focused
                                if focused_policy is not None
                                else None
                            ),
                            batch_invertible=True,
                        )
                    )
                    budget.account_actions(focused.stats.actions_considered)
                    stats.actions_considered += focused.stats.actions_considered
                    stats.actions_generated += focused.stats.actions_generated
                    stats.model_calls += focused.stats.model_calls
                    stats.model_batches += focused.stats.policy_nodes
                    stats.model_elapsed_ms += focused.stats.model_elapsed_ms
                    for name in (
                        "nodes_expanded",
                        "cache_hits",
                        "cycles_pruned",
                        "depth_pruned",
                    ):
                        stats.focused[name] = int(stats.focused.get(name, 0)) + int(
                            getattr(focused.stats, name)
                        )
                    if focused.status == "resource-exhausted":
                        saw_exhaustion = True

                    term_ranking_started = time.monotonic()
                    terms = _rank_terms(goal, focused.terms, term_model)
                    if term_model is not None and len(terms) > 1:
                        stats.model_calls += len(terms)
                        stats.model_batches += 1
                        stats.model_elapsed_ms += (
                            time.monotonic() - term_ranking_started
                        ) * 1000.0
                    current_open = len(remaining_goals)
                    if terms:
                        # Finding an inhabitant in the erased implicational
                        # approximation is not a cut in dependent search. Keep
                        # the original source/lineage for structural fallback,
                        # including after a later or fresh-check rejection.
                        if len(queue) + len(focused_fallbacks) >= task.max_candidates:
                            stats.frontier_pruned += 1
                            saw_exhaustion = True
                        else:
                            focused_fallbacks.append((state, current_open))
                            stats.focused_fallbacks_deferred += 1
                            stats.frontier_peak = max(
                                stats.frontier_peak,
                                len(queue) + len(focused_fallbacks),
                            )
                    for term in () if fully_widened else terms:
                        try:
                            edit = reconstruct_term_as_clause(
                                state_source,
                                goal,
                                term,
                                forbidden_names=(entry.name for entry in goal.context),
                            )
                        except ValueError:
                            rendered = render_term(term)
                            next_source, edit = _replace_goal(
                                state_source, goal, rendered
                            )
                        else:
                            next_source = apply_source_edit(state_source, edit)
                        if not _edit_within_region(
                            edit,
                            region_start=region_start,
                            region_end=state_region_end,
                        ):
                            continue
                        delta = len(str(edit["replacement"])) - len(
                            str(edit["original"])
                        )
                        enqueue(
                            next_source,
                            state_region_end + delta,
                            state.depth + 1,
                            current_open - 1,
                            state.steps + (edit,),
                            policy_choices=state.policy_choices,
                            widened_declarations=successor_widened,
                        )

                    def run_case_batch(
                        current_goal: GoalInfo = goal,
                        current_state: _State = state,
                        loaded_goals: tuple[GoalInfo, ...] = loaded,
                        current_region_end: int = state_region_end,
                        current_source_text: str = state_source,
                        open_count: int = current_open,
                        force_beyond_exact_local: bool = False,
                        preferred_root_position: int | None = None,
                        recursive_program_profile: Literal[
                            "unary-recursive", "binary-recursive"
                        ]
                        | None = None,
                        recursive_composition_local_first: bool = False,
                        restore_parent: bool = True,
                        current_widened_declarations: frozenset[str] = (
                            successor_widened
                        ),
                    ) -> bool:
                        nonlocal saw_exhaustion

                        def record_case_stats(batch_stats: CaseBatchStats) -> None:
                            result.verifier_calls += _accumulate_case_stats(
                                stats, batch_stats
                            )

                        batched = batched_case_prove(
                            candidate_path,
                            current_goal,
                            action_budget=remaining_goal_actions(),
                            timeout_seconds=budget.require_time(
                                "joint batched case search"
                            ),
                            max_depth=(
                                None
                                if task.max_depth is None
                                else task.max_depth - current_state.depth
                            ),
                            focused_model=focused_model,
                            refinement_model=refinement_model,
                            policy_router=policy_router,
                            session_factory=session_factory,
                            project_configuration=workspace.configuration,
                            session=session,
                            initial_goals=loaded_goals,
                            allow_exact_local=not force_beyond_exact_local,
                            preferred_root_position=preferred_root_position,
                            recursive_program_profile=recursive_program_profile,
                            recursive_composition_local_first=(
                                recursive_composition_local_first
                            ),
                            on_statistics=record_case_stats,
                        )
                        batch_stats = batched.stats
                        budget.account_actions(batch_stats.actions_considered)
                        if batched.status == "resource-exhausted":
                            saw_exhaustion = True
                        if batched.patch is None:
                            # A reused batched-case session may have loaded one
                            # or more speculative intermediate clause levels.
                            # Restore the exact joint state before another
                            # specialist receives CURRENT_GOAL; otherwise its
                            # interaction id and telescope belong to a stale
                            # revision and reconstruction can drop binders.
                            candidate_path.write_text(current_source_text)
                            charge_io(len(current_source_text.encode()))
                            encoded_size = len(current_source_text.encode("utf-8"))
                            stats.source_bytes_materialized += encoded_size
                            stats.source_bytes_written += encoded_size
                            restore_started = time.monotonic()
                            session.load_module(candidate_path)
                            stats.kernel_loads += 1
                            stats.kernel_load_elapsed_ms += (
                                time.monotonic() - restore_started
                            ) * 1000.0
                            return False
                        edit = batched.patch
                        if not _edit_within_region(
                            edit,
                            region_start=region_start,
                            region_end=current_region_end,
                        ):
                            return False
                        next_source = apply_source_edit(current_source_text, edit)
                        delta = len(str(edit["replacement"])) - len(
                            str(edit["original"])
                        )
                        try:
                            case_result_relation = parse_relation(
                                split_top_level_arrows(current_goal.target)[-1]
                            )
                        except ValueError:
                            case_result_relation = None
                        enqueue(
                            next_source,
                            current_region_end + delta,
                            current_state.depth + max(1, batch_stats.max_depth),
                            open_count - 1,
                            current_state.steps + (edit,),
                            policy_choices=(
                                current_state.policy_choices + batched.policy_choices
                            ),
                            priority_bias=(
                                -5
                                if recursive_program_profile is None
                                and batch_stats.local_closures > 0
                                and case_result_relation is None
                                else (
                                    -3 if recursive_program_profile is not None else -1
                                )
                            ),
                            widened_declarations=current_widened_declarations,
                        )
                        if restore_parent:
                            # Further joint alternatives must start from
                            # exactly the same proof state; the batched
                            # specialist loaded its speculative clause levels
                            # into the shared Agda process while constructing
                            # this candidate.  When this is the terminal
                            # specialist for the state, the next frontier pop
                            # loads its own source and this replay is redundant.
                            candidate_path.write_text(current_source_text)
                            charge_io(len(current_source_text.encode()))
                            encoded_size = len(current_source_text.encode("utf-8"))
                            stats.source_bytes_materialized += encoded_size
                            stats.source_bytes_written += encoded_size
                            restore_started = time.monotonic()
                            session.load_module(candidate_path)
                            stats.kernel_loads += 1
                            stats.kernel_load_elapsed_ms += (
                                time.monotonic() - restore_started
                            ) * 1000.0
                        return True

                    # Exhaustive evaluation of a concrete nullary datatype is
                    # normally cheaper and more decisive than trying every
                    # global theorem with a matching result head. If it fails,
                    # the normal structural/premise search still runs below.
                    case_batch_attempted = False
                    case_batch_accepted = False
                    projection_needs_alternative = bool(
                        retain_alternatives
                        and any(_is_lambda_projection(term) for term in terms)
                    )
                    observable_data_function = False
                    if (
                        retain_alternatives
                        and not terms
                        and top_level_arrow_count(goal.target)
                        and isinstance(session, TransactionalKernelSession)
                    ):
                        try:
                            codomain = split_top_level_arrows(goal.target)[-1]
                            codomain_head = result_head(codomain)
                        except ValueError:
                            codomain_head = ""
                        if codomain_head:
                            codomain_catalog = session.constructor_candidates(
                                session.current_state(),
                                goal_id=goal.goal_id,
                                type_head=codomain_head,
                            )
                            stats.constructor_catalog_queries += 1
                            result.verifier_calls += 1
                            observable_data_function = any(
                                result_head(type_text) == codomain_head
                                for _name, type_text in codomain_catalog
                            )
                    structural_function_needs_alternative = bool(
                        retain_alternatives
                        and (
                            observable_data_function
                            or (
                                terms
                                and any(_is_lambda_constant(term) for term in terms)
                            )
                        )
                    )
                    function_needs_alternative = (
                        projection_needs_alternative
                        or structural_function_needs_alternative
                    )
                    relational_elimination_needs_alternative = bool(
                        retain_alternatives
                        and has_relational_elimination_shape(goal.target)
                    )
                    progressive_alternatives_omitted = False
                    ready_structured_builder = False
                    if (
                        not terms
                        and stats.contextual_evidence_enabled
                        and isinstance(session, ScopeDeclarationSession)
                        and isinstance(session, TransactionalKernelSession)
                    ):
                        declarations, queries = visible_scope_declarations(
                            session, session.current_state(), goal
                        )
                        stats.premise_catalog_queries += queries
                        result.verifier_calls += queries
                        owner = _owning_declaration_name(state_source, goal)
                        ready_structured_builder = has_structured_builder(
                            goal.target,
                            tuple(e.type for e in goal.context if e.in_scope),
                            tuple(
                                (name, ty) for name, ty in declarations if name != owner
                            ),
                        )
                    if (
                        (
                            not terms
                            or function_needs_alternative
                            or relational_elimination_needs_alternative
                        )
                        and remaining_goal_actions() > 0
                        and not ready_structured_builder
                        # Introduce a displayed hidden telescope before case
                        # synthesis, which otherwise auto-inserts inaccessible
                        # endpoints. The ordinary case fallback remains below.
                        and (
                            not stats.contextual_evidence_enabled
                            or telescope_introduction(
                                goal.target,
                                frozenset(
                                    entry.name for entry in goal.context if entry.name
                                ),
                                trailing_only=True,
                            )
                            is None
                        )
                        and (
                            function_needs_alternative
                            or relational_elimination_needs_alternative
                            or goal_has_concrete_nullary_scrutinee(goal)
                            or goal_has_dependency_tower(goal)
                        )
                    ):
                        case_batch_attempted = True
                        if (
                            not terms
                            or not function_needs_alternative
                            or relational_elimination_needs_alternative
                        ):
                            case_batch_accepted = run_case_batch(
                                force_beyond_exact_local=False,
                                restore_parent=(
                                    function_needs_alternative
                                    or relational_elimination_needs_alternative
                                ),
                            )
                        if function_needs_alternative:
                            # Observable function definitions require genuine
                            # primitive-recursion alternatives in addition to
                            # projections.  Enumerate the finite cross-product
                            # of explicit recursion positions and generic
                            # constructor/composition schemas; later goals
                            # provide the semantic constraints that prune it.
                            prior_binary_operation = False
                            current_name = declaration_name_at_goal(state_source, goal)
                            if isinstance(
                                session, ScopeDeclarationSession
                            ) and isinstance(session, TransactionalKernelSession):
                                declarations, scope_queries = (
                                    visible_scope_declarations(
                                        session, session.current_state(), goal
                                    )
                                )
                                stats.premise_catalog_queries += scope_queries
                                result.verifier_calls += scope_queries
                                try:
                                    carrier_head = result_head(
                                        split_top_level_arrows(goal.target)[-1]
                                    )
                                except ValueError:
                                    carrier_head = ""
                                carrier_constructors = (
                                    session.constructor_candidates(
                                        session.current_state(),
                                        goal_id=goal.goal_id,
                                        type_head=carrier_head,
                                    )
                                    if carrier_head
                                    else ()
                                )
                                if carrier_head:
                                    stats.constructor_catalog_queries += 1
                                    result.verifier_calls += 1
                                constructor_names = {
                                    name.rsplit(".", 1)[-1]
                                    for name, _type_text in carrier_constructors
                                }
                                prior_binary_operation = any(
                                    name != current_name
                                    and name.rsplit(".", 1)[-1]
                                    != current_name.rsplit(".", 1)[-1]
                                    and name.rsplit(".", 1)[-1] not in constructor_names
                                    and explicit_arity(type_text) == 2
                                    and result_head(type_text) == carrier_head
                                    for name, type_text in declarations
                                )
                            profiles: tuple[
                                Literal["binary-recursive", "unary-recursive"], ...
                            ] = (
                                (
                                    "binary-recursive",
                                    "unary-recursive",
                                )
                                if prior_binary_operation
                                else ("unary-recursive",)
                            )
                            observed_composition_order = (
                                _observed_recursive_composition_order(
                                    state_source,
                                    remaining_goals,
                                    current_name,
                                )
                                if "binary-recursive" in profiles
                                else None
                            )
                            composition_orders = (
                                (observed_composition_order,)
                                if observed_composition_order is not None
                                and not fully_widened
                                else ((False, True) if fully_widened else (False,))
                            )
                            root_positions = tuple(range(explicit_arity(goal.target)))
                            observed_order = (
                                _observed_binary_argument_order(
                                    state_source,
                                    remaining_goals,
                                    current_name,
                                )
                                if len(root_positions) == 2
                                else None
                            )
                            if observed_order is not None:
                                root_positions = observed_order
                            if not prior_binary_operation:
                                # A constructor-map fold conventionally keeps
                                # leading arguments parametric.  Trying the
                                # final coordinate first tends to preserve
                                # computation in later algebraic laws.  Every
                                # coordinate remains an alternative.
                                if observed_order is None:
                                    root_positions = tuple(reversed(root_positions))
                            progressive_alternatives_omitted = bool(
                                not fully_widened
                                and (
                                    len(root_positions) > 1
                                    or len(profiles) > 1
                                    or (
                                        "binary-recursive" in profiles
                                        and observed_composition_order is None
                                    )
                                )
                            )
                            if progressive_alternatives_omitted:
                                root_positions = root_positions[:1]
                                profiles = profiles[:1]
                            for root_position in root_positions:
                                for profile in profiles:
                                    orders = (
                                        composition_orders
                                        if profile == "binary-recursive"
                                        else (False,)
                                    )
                                    for local_first in orders:
                                        if remaining_goal_actions() <= 0:
                                            saw_exhaustion = True
                                            break
                                        accepted = run_case_batch(
                                            force_beyond_exact_local=True,
                                            preferred_root_position=root_position,
                                            recursive_program_profile=profile,
                                            recursive_composition_local_first=(
                                                local_first
                                            ),
                                        )
                                        case_batch_accepted = (
                                            case_batch_accepted or accepted
                                        )
                                    if remaining_goal_actions() <= 0:
                                        break
                                if remaining_goal_actions() <= 0:
                                    break

                    constructor_accepted = False
                    constructor_needs_case_alternative = False
                    if (
                        (not terms or function_needs_alternative)
                        and (not case_batch_accepted or function_needs_alternative)
                        and not fully_widened
                        and isinstance(session, TransactionalKernelSession)
                        and remaining_goal_actions() > 0
                    ):

                        def record_constructor_stats(
                            constructor_stats: ConstructorStats,
                        ) -> None:
                            stats.merge_retrieval(constructor_stats)
                            stats.actions_considered += (
                                constructor_stats.actions_considered
                            )
                            stats.actions_generated += (
                                constructor_stats.actions_generated
                            )
                            stats.refinement_queries += (
                                constructor_stats.constructor_queries
                                + constructor_stats.premise_refinement_queries
                                + constructor_stats.local_refinement_queries
                            )
                            stats.constructor_queries += (
                                constructor_stats.constructor_queries
                            )
                            stats.local_refinement_candidates += (
                                constructor_stats.local_refinement_candidates
                            )
                            stats.local_refinement_queries += (
                                constructor_stats.local_refinement_queries
                            )
                            stats.skeleton_queries += constructor_stats.skeleton_queries
                            stats.skeleton_candidates += (
                                constructor_stats.skeleton_candidates
                            )
                            stats.skeleton_frontier_peak = max(
                                stats.skeleton_frontier_peak,
                                constructor_stats.skeleton_frontier_peak,
                            )
                            remaining_skeleton_slots = max(
                                0,
                                _MAX_RECORDED_SKELETON_ATTEMPTS
                                - len(stats.skeleton_attempts),
                            )
                            retained_skeleton_attempts = (
                                constructor_stats.skeleton_attempts[
                                    :remaining_skeleton_slots
                                ]
                            )
                            stats.skeleton_attempts.extend(retained_skeleton_attempts)
                            stats.skeleton_attempts_omitted += (
                                constructor_stats.skeleton_attempts_omitted
                                + len(constructor_stats.skeleton_attempts)
                                - len(retained_skeleton_attempts)
                            )
                            stats.premise_catalog_queries += (
                                constructor_stats.premise_catalog_queries
                            )
                            stats.constructor_catalog_queries += (
                                constructor_stats.catalog_queries
                            )
                            stats.premise_queries += constructor_stats.premise_queries
                            stats.premise_refinement_queries += (
                                constructor_stats.premise_refinement_queries
                            )
                            stats.premise_candidates += (
                                constructor_stats.premise_candidates
                            )
                            stats.evidence_inference_queries += (
                                constructor_stats.evidence_inference_queries
                            )
                            stats.evidence_terms += constructor_stats.evidence_terms
                            stats.evidence_path_queries += (
                                constructor_stats.evidence_path_queries
                            )
                            remaining_premise_slots = max(
                                0,
                                _MAX_RECORDED_PREMISE_ATTEMPTS
                                - len(stats.premise_attempts),
                            )
                            retained_premise_attempts = (
                                constructor_stats.premise_attempts[
                                    :remaining_premise_slots
                                ]
                            )
                            stats.premise_attempts.extend(retained_premise_attempts)
                            stats.premise_attempts_omitted += (
                                constructor_stats.premise_attempts_omitted
                                + len(constructor_stats.premise_attempts)
                                - len(retained_premise_attempts)
                            )
                            stats.completion_queries += (
                                constructor_stats.completion_queries
                            )
                            stats.incomplete_solutions_pruned += (
                                constructor_stats.incomplete_solutions_pruned
                            )
                            stats.recursive_subject_search_actions += (
                                constructor_stats.recursive_subject_search_actions
                            )
                            stats.recursive_subject_inference_queries += (
                                constructor_stats.recursive_subject_inference_queries
                            )
                            stats.recursive_subjects_generated += (
                                constructor_stats.recursive_subjects_generated
                            )
                            stats.recursive_catalog_queries += (
                                constructor_stats.recursive_catalog_queries
                            )
                            stats.recursive_wrappers_generated += (
                                constructor_stats.recursive_wrappers_generated
                            )
                            stats.recursive_applications_generated += (
                                constructor_stats.recursive_applications_generated
                            )
                            stats.recursive_inference_queries += (
                                constructor_stats.recursive_inference_queries
                            )
                            stats.recursive_applications_inferred += (
                                constructor_stats.recursive_applications_inferred
                            )
                            stats.recursive_applications_pruned += (
                                constructor_stats.recursive_applications_pruned
                            )
                            stats.recursive_compositions_generated += (
                                constructor_stats.recursive_compositions_generated
                            )
                            stats.recursive_composition_inference_queries += constructor_stats.recursive_composition_inference_queries
                            stats.recursive_compositions_inferred += (
                                constructor_stats.recursive_compositions_inferred
                            )
                            stats.recursive_proof_checks += (
                                constructor_stats.recursive_proof_checks
                            )
                            stats.proof_checks += constructor_stats.proof_checks
                            stats.goal_inspections += constructor_stats.goal_inspections
                            stats.generated_subgoals += (
                                constructor_stats.generated_subgoals
                            )
                            stats.model_calls += constructor_stats.model_calls
                            stats.model_batches += constructor_stats.model_batches
                            stats.model_elapsed_ms += constructor_stats.model_elapsed_ms
                            for name, value in constructor_stats.focused.items():
                                stats.focused[name] = stats.focused.get(name, 0) + value
                            result.verifier_calls += (
                                constructor_stats.constructor_queries
                                + constructor_stats.proof_checks
                                + constructor_stats.catalog_queries
                                + constructor_stats.premise_catalog_queries
                                + constructor_stats.premise_refinement_queries
                                + constructor_stats.completion_queries
                                + constructor_stats.local_refinement_queries
                                + constructor_stats.recursive_subject_inference_queries
                                + constructor_stats.recursive_inference_queries
                                + constructor_stats.recursive_catalog_queries
                                + constructor_stats.recursive_composition_inference_queries
                                + constructor_stats.evidence_inference_queries
                                + constructor_stats.evidence_path_queries
                            )

                        constructor = constructor_tree_prove(
                            session,
                            goal,
                            action_budget=remaining_goal_actions(),
                            timeout_seconds=budget.require_time(
                                "joint constructor-tree alternatives"
                            ),
                            max_depth=(
                                None
                                if task.max_depth is None
                                else task.max_depth - state.depth
                            ),
                            solution_limit=(
                                min(
                                    _MAX_STRUCTURAL_ALTERNATIVES,
                                    remaining_goal_actions(),
                                )
                                if retain_alternatives
                                else 1
                            ),
                            focused_model=focused_model,
                            refinement_model=refinement_model,
                            policy_router=policy_router,
                            excluded_premises=frozenset(
                                filter(
                                    None,
                                    (_owning_declaration_name(state_source, goal),),
                                )
                            ),
                            defer_concrete_premises=not case_batch_attempted,
                            on_statistics=record_constructor_stats,
                        )
                        constructor_stats = constructor.stats
                        budget.account_actions(constructor.stats.actions_considered)
                        if constructor.status == "resource-exhausted":
                            saw_exhaustion = True
                        constructor_accepted = bool(constructor.solutions)
                        for solution in constructor.solutions:
                            binders, body = solution.plan.clause_parts()
                            if binders and not any(
                                re.search(
                                    rf"(?<![\w'-]){re.escape(binder)}(?![\w'-])",
                                    body,
                                )
                                for binder in binders
                            ):
                                constructor_needs_case_alternative = True
                            edit = reconstruct_checked_clause_completion(
                                state_source,
                                goal,
                                binders=binders,
                                body=body,
                            )
                            if not _edit_within_region(
                                edit,
                                region_start=region_start,
                                region_end=state_region_end,
                            ):
                                continue
                            next_source = apply_source_edit(state_source, edit)
                            delta = len(str(edit["replacement"])) - len(
                                str(edit["original"])
                            )
                            enqueue(
                                next_source,
                                state_region_end + delta,
                                state.depth + max(1, constructor_stats.max_depth),
                                current_open - 1,
                                state.steps + (edit,),
                                policy_choices=(
                                    state.policy_choices
                                    + solution.plan.choices_on_proof()
                                ),
                                priority_bias=(
                                    -4
                                    if retain_alternatives
                                    and explicit_arity(goal.target) == 1
                                    and len(body.split()) > 1
                                    and body not in binders
                                    else (-2 if retain_alternatives else 0)
                                ),
                                widened_declarations=successor_widened,
                            )

                    if (
                        function_needs_alternative
                        and not fully_widened
                        and owning_declaration is not None
                        and progressive_alternatives_omitted
                    ):
                        enqueue(
                            state_source,
                            state_region_end,
                            state.depth,
                            current_open,
                            state.steps,
                            policy_choices=state.policy_choices,
                            priority_bias=6,
                            widened_declarations=(
                                state.widened_declarations | {owning_declaration}
                            ),
                            skip_focused=state.skip_focused,
                        )
                        stats.progressive_widening_fallbacks += 1

                    if (
                        not terms
                        and not case_batch_attempted
                        and (
                            not constructor_accepted
                            or (
                                retain_alternatives
                                and constructor_needs_case_alternative
                            )
                        )
                        and remaining_goal_actions() > 0
                    ):
                        case_batch_attempted = True
                        case_batch_accepted = run_case_batch(
                            force_beyond_exact_local=projection_needs_alternative
                        )

                    # If focused search found no complete term, ask Agda for
                    # its deterministic introduction/unique-constructor step.
                    refinement_accepted = constructor_accepted or case_batch_accepted
                    if (
                        not terms
                        and not constructor_accepted
                        and not case_batch_accepted
                        and remaining_goal_actions() > 0
                        and budget.charge_action()
                    ):
                        stats.actions_considered += 1
                        stats.actions_generated += 1
                        checked_refinement = session.check_refinement(goal.goal_id, "")
                        result.verifier_calls += 1
                        stats.refinement_queries += 1
                        if (
                            checked_refinement.accepted
                            and checked_refinement.preview is not None
                        ):
                            refinement_accepted = True
                            try:
                                arrow_goal = top_level_arrow_count(goal.target) > 0
                            except ValueError:
                                arrow_goal = False
                            if arrow_goal:
                                edit = reconstruct_intro(
                                    state_source, goal, checked_refinement.preview
                                )
                                next_source = apply_source_edit(state_source, edit)
                            else:
                                next_source, edit = _replace_goal(
                                    state_source, goal, checked_refinement.preview
                                )
                            if _edit_within_region(
                                edit,
                                region_start=region_start,
                                region_end=state_region_end,
                            ):
                                delta = len(str(edit["replacement"])) - len(
                                    str(edit["original"])
                                )
                                generated = max(
                                    1, checked_refinement.preview.count("?")
                                )
                                stats.generated_subgoals += generated
                                enqueue(
                                    next_source,
                                    state_region_end + delta,
                                    state.depth + 1,
                                    current_open - 1 + generated,
                                    state.steps + (edit,),
                                    policy_choices=state.policy_choices,
                                    widened_declarations=successor_widened,
                                )
                    elif (
                        not terms
                        and not constructor_accepted
                        and not case_batch_accepted
                    ):
                        saw_exhaustion = True

                    # Case splitting is an alternative even when a focused
                    # term exists: a later law can demand a constructor-specific
                    # definition instead of a projection or local hypothesis.
                    if not refinement_accepted:
                        case_actions = [
                            RefinementCandidate.case_split(entry.name, entry.type)
                            for entry in goal.context
                            if entry.in_scope and entry.name
                        ]
                        case_actions.sort(key=lambda action: action.symbolic_key(goal))
                        stats.actions_generated += len(case_actions)
                        if policy_router is None:
                            raise RuntimeError("joint policy router is unavailable")
                        before_items = policy_router.model_items_scored
                        before_batches = policy_router.model_batches
                        before_elapsed = policy_router.model_elapsed_ms
                        ranked = policy_router.rank(
                            goal,
                            tuple(
                                policy_candidate(
                                    family="case-variable",
                                    tag=action.tag,
                                    expression=action.expression,
                                    type_text=action.local_type or "unknown",
                                    symbolic_key=action.symbolic_key(goal),
                                )
                                for action in case_actions
                            ),
                        )
                        by_expression = {
                            action.expression: action for action in case_actions
                        }
                        case_actions = [
                            by_expression[candidate.expression]
                            for candidate in ranked.candidates
                        ]
                        stats.model_calls += (
                            policy_router.model_items_scored - before_items
                        )
                        stats.model_batches += (
                            policy_router.model_batches - before_batches
                        )
                        stats.model_elapsed_ms += (
                            policy_router.model_elapsed_ms - before_elapsed
                        )
                        case_choices = policy_router.snapshot_choices(
                            "case-variable", goal
                        )
                        for action in case_actions:
                            if (
                                remaining_goal_actions() <= 0
                                or not budget.charge_action()
                            ):
                                saw_exhaustion = True
                                break
                            choice = case_choices.get(action.expression)
                            if choice is not None:
                                policy_router.recorder.mark(
                                    choice.decision_id, choice.candidate_id
                                )
                            stats.actions_considered += 1
                            checked_case = session.check_case_split(
                                goal.goal_id, action.expression
                            )
                            result.verifier_calls += 1
                            stats.case_queries += 1
                            if not checked_case.accepted:
                                if choice is not None:
                                    policy_router.recorder.mark(
                                        choice.decision_id,
                                        choice.candidate_id,
                                        outcome="invalid",
                                    )
                                continue
                            try:
                                edit = reconstruct_case_split(
                                    state_source, goal, checked_case.clauses
                                )
                            except ValueError:
                                continue
                            if not _edit_within_region(
                                edit,
                                region_start=region_start,
                                region_end=state_region_end,
                            ):
                                continue
                            next_source = apply_source_edit(state_source, edit)
                            delta = len(str(edit["replacement"])) - len(
                                str(edit["original"])
                            )
                            stats.generated_subgoals += len(checked_case.clauses)
                            enqueue(
                                next_source,
                                state_region_end + delta,
                                state.depth + 1,
                                current_open - 1 + len(checked_case.clauses),
                                state.steps + (edit,),
                                policy_choices=(
                                    state.policy_choices + ((choice,) if choice else ())
                                ),
                                widened_declarations=successor_widened,
                            )

                if result.status == "internal-error" and result.patch is None:
                    if saw_exhaustion or budget.exhausted():
                        result.status = "resource-exhausted"
                        result.diagnostics.append(
                            {
                                "kind": "resource",
                                "message": (
                                    "joint prefix search exhausted its action, depth, "
                                    "or wall-time budget"
                                ),
                            }
                        )
                    else:
                        result.status = "unsolved"
                        result.diagnostics.append(
                            {
                                "kind": "search",
                                "message": (
                                    "no jointly valid assignment was found in the "
                                    "finite search fragment"
                                ),
                            }
                        )

    except (ValueError, AgdaLoadError) as error:
        result.status = "invalid-task"
        result.diagnostics.append({"kind": "input", "message": str(error)})
    except AgdaBridgeError as error:
        result.status = "toolchain-error"
        result.diagnostics.append({"kind": "protocol", "message": str(error)})
    except ValidationError as error:
        result.status = "policy-rejected"
        result.diagnostics.append({"kind": "policy", "message": str(error)})
    except (TimeoutError, VerifierCallLimitExceeded, ResourceLimitError) as error:
        result.status = "resource-exhausted"
        result.diagnostics.append({"kind": "resource", "message": str(error)})
    except OSError as error:
        result.status = "toolchain-error"
        result.diagnostics.append({"kind": "toolchain", "message": str(error)})
    finally:
        exhaustion = resource_scope.finish()
        if exhaustion is not None:
            result.status = "resource-exhausted"
            result.diagnostics.append({"kind": "resource", "message": str(exhaustion)})
        result.resource_budget = resource_scope.ledger.report()
        result.verifier_budget = call_scope.report()
        call_scope.close()
        # Aggregate exactly once on every exit, including quota/timeouts raised
        # inside a nested search. Work already performed must not become zero
        # merely because the normal end-of-search path was not reached.
        if focused_policy is not None:
            stats.nnue_accumulator = focused_policy.metrics()
        result.candidates_generated = stats.actions_considered
        result.model_calls = stats.model_calls
        result.model_elapsed_ms = stats.model_elapsed_ms
        result.cost.add(
            actions_generated=stats.actions_generated,
            actions_expanded=stats.actions_considered,
            actions_scored=stats.model_calls,
            kernel_loads=stats.kernel_loads,
            goal_inspections=stats.goal_inspections,
            speculative_checks=(
                stats.refinement_queries
                + stats.case_queries
                + stats.proof_checks
                + stats.premise_catalog_queries
                + stats.constructor_catalog_queries
                + stats.evidence_inference_queries
                + stats.evidence_path_queries
            ),
            candidate_terms_checked=stats.proof_checks,
            refinement_checks=stats.refinement_queries,
            case_split_checks=stats.case_queries,
            model_batches=stats.model_batches,
            model_items_scored=stats.model_calls,
            generated_subgoals=stats.generated_subgoals,
            source_bytes_materialized=stats.source_bytes_materialized,
            source_bytes_written=stats.source_bytes_written,
            kernel_load_elapsed_ms=stats.kernel_load_elapsed_ms,
        )
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        result.elapsed_ms = stats.elapsed_ms
        result.search_stats = stats.to_dict()
        if policy_router is not None:
            if result.status == "verified" and selected_policy_choices:
                evidence = validated_proof_evidence(
                    task_id=result.task_id,
                    source_sha256=result.source_hash,
                    patch=result.patch,
                    validation=result.validation,
                    trust_report=result.trust_report,
                )
                if evidence is not None:
                    try:
                        policy_router.recorder.mark_validated_proof(
                            selected_policy_choices, evidence=evidence
                        )
                    except ValueError as error:
                        # Trace corruption cannot change Agda acceptance or
                        # grant partial credit to an otherwise checked branch.
                        result.diagnostics.append(
                            {"kind": "training-trace", "message": str(error)}
                        )
            result.policy_trace.extend(policy_router.recorder.to_list())
            result.search_stats["or_policy"] = policy_router.metrics()
    return result
