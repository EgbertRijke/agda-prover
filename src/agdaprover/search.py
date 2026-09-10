"""Deterministic bounded proof search with symbolic or NNUE ordering."""

from __future__ import annotations

import time
from dataclasses import dataclass
from pathlib import Path

from agdaprover.observability.policy_trace import PolicyTraceRecorder

from .bridge.resources import current_process_rss
from .budget import SearchBudget
from .case_search import batched_case_prove
from .constructor_search import ConstructorStats, constructor_tree_prove
from .contracts import (
    CandidateAttempt,
    GoalInfo,
    ProverResult,
    TaskSpec,
    search_budget_envelope,
    task_identity,
)
from .focused import focused_prove
from .guided import guided_prove
from .impossibility import certify_impossible
from .kernel.p0 import (
    AgdaBridgeError,
    AgdaLoadError,
    AgdaSession,
    ProjectInputs,
    open_kernel_session,
    session_project_inputs,
)
from .kernel.protocol import KernelSessionFactory, TransactionalKernelSession
from .offline import assert_offline_configuration
from .or_policy import ORPolicyRouter
from .presentation import (
    declaration_name_at_goal,
    format_proof_term,
    reconstruct_checked_clause_completion,
    reconstruct_term_as_clause,
)
from .project import attach_module_scope, choose_goal, require_agda_source_file
from .project_configuration import ProjectConfiguration
from .ranking.protocol import ProofTermRanker
from .ranking.runtime import configured_model_ids, load_proof_models
from .reasoning import has_result_subject_elimination_shape
from .resource_budget import ResourceLimitError, ResourceScope
from .terms import Term, iter_terms, render_term, symbolic_key
from .type_syntax import (
    binder_domains,
    parse_named_binder,
    result_head,
    split_adjacent_binders,
    split_top_level_application,
    split_top_level_arrows,
    strip_outer_delimiters,
)
from .verification import ValidationError, file_sha256, validate_reconstruction
from .verifier_budget import VerifierCallLimitExceeded, VerifierCallScope


@dataclass(frozen=True)
class RankedCandidate:
    term: Term
    symbolic_key: tuple[int, int, str]
    nnue_score: float | None


def _has_abstract_final_result(goal: GoalInfo) -> bool:
    """Whether the goal telescope quantifies its own result type head."""

    try:
        telescope = split_top_level_arrows(goal.target)
        final_target = strip_outer_delimiters(telescope[-1]).strip()
        application = split_top_level_application(final_target)
    except ValueError:
        return False
    if not application:
        return False
    head = application[0]
    candidates = tuple(
        entry
        for entry in goal.context
        if entry.name == head and result_head(entry.type).startswith("Set")
    )
    binder_candidates = []
    for domain_group in telescope[:-1]:
        groups = split_adjacent_binders(domain_group) or (domain_group,)
        for group in groups:
            try:
                binder = parse_named_binder(group)
            except ValueError:
                return False
            if binder is not None and head in binder.names:
                binder_candidates.append(binder)
    candidate_types = (
        *(candidate.type for candidate in candidates),
        *(candidate.domain for candidate in binder_candidates),
    )
    for candidate_type in candidate_types:
        if not result_head(candidate_type).startswith("Set"):
            continue
        try:
            arity = sum(
                len(binder_domains(domain))
                for domain in split_top_level_arrows(candidate_type)[:-1]
            )
        except ValueError:
            continue
        if len(application) == arity + 1:
            return True
    return False


def _required_score(score: float | None) -> float:
    if score is None:
        raise ValueError("NNUE-ranked candidate has no score")
    return score


def rank_candidates(
    goal: GoalInfo,
    candidates: list[Term],
    *,
    ranker: str,
    model: ProofTermRanker | None,
) -> list[RankedCandidate]:
    nnue_scores = (
        model.score_terms(goal, candidates)
        if ranker == "nnue" and model is not None
        else [None] * len(candidates)
    )
    ranked = [
        RankedCandidate(
            term=term,
            symbolic_key=symbolic_key(goal.target, term),
            nnue_score=score,
        )
        for term, score in zip(candidates, nnue_scores, strict=True)
    ]
    if ranker == "symbolic":
        return sorted(ranked, key=lambda candidate: candidate.symbolic_key)
    if ranker == "nnue":
        if model is None:
            raise ValueError("NNUE ranking requires a model")
        return sorted(
            ranked,
            key=lambda candidate: (
                -_required_score(candidate.nnue_score),
                candidate.symbolic_key,
            ),
        )
    raise ValueError(f"unsupported ranker: {ranker}")


def prove(
    task: TaskSpec,
    *,
    include_attempts: bool = True,
    session_factory: KernelSessionFactory = AgdaSession,
    productive_elimination_first: bool = True,
) -> ProverResult:
    started = time.monotonic()
    source_file = task.source_file.resolve()
    result = ProverResult(
        task_id=task_identity(
            task,
            "",
            mode="prove",
            policy_profile="p0-search-v2",
            toolchain_id=None,
            model_ids={"primary": None, "refinement": None},
        ),
        status="internal-error",
        source_file=str(source_file),
        source_hash="",
        ranker=task.ranker,
    )
    policy_router: ORPolicyRouter | None = None
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
            task.max_candidates,
            task.timeout_seconds,
            started_at=started,
        )
        assert_offline_configuration(task, deadline=budget.deadline)
        result.source_hash = file_sha256(source_file, deadline=budget.deadline)
        configured_ids = configured_model_ids(task, deadline=budget.deadline)
        result.task_id = task_identity(
            task,
            result.source_hash,
            mode="prove",
            policy_profile=result.policy_profile,
            toolchain_id=None,
            model_ids=configured_ids,
        )
        models = load_proof_models(task, deadline=budget.deadline, command="prove")
        term_model = models.term
        focused_model = models.focused
        refinement_model = models.refinement
        result.model_id = models.primary_id
        result.action_model_id = models.refinement_id

        with open_kernel_session(
            session_factory,
            project_configuration=task.project_configuration,
            timeout_seconds=budget.require_time("initial Agda load"),
            deadline=budget.deadline,
        ) as session:
            result.toolchain_id = session.toolchain_id
            result.task_id = task_identity(
                task,
                result.source_hash,
                mode="prove",
                policy_profile=result.policy_profile,
                toolchain_id=result.toolchain_id,
                model_ids={
                    "primary": result.model_id,
                    "refinement": result.action_model_id,
                },
            )
            load_started = time.monotonic()
            loaded_goals = session.load_module(source_file)
            original_inputs = session_project_inputs(session)
            if original_inputs is not None and (
                task.project_configuration is not None or original_inputs.library_bound
            ):
                result.task_id = task_identity(
                    task,
                    result.source_hash,
                    mode="prove",
                    policy_profile=result.policy_profile,
                    toolchain_id=result.toolchain_id,
                    model_ids={
                        "primary": result.model_id,
                        "refinement": result.action_model_id,
                    },
                    project_inputs_id=original_inputs.identity,
                )
            result.cost.add(
                kernel_loads=1,
                kernel_load_elapsed_ms=(time.monotonic() - load_started) * 1000.0,
            )
            goal = attach_module_scope(
                session.inspect_goal(
                    choose_goal(loaded_goals, task.goal_id, task.goal_position)
                ),
                source_file.read_text(),
                source_file,
            )
            result.cost.add(goal_inspections=1)
            result.goal = goal.to_dict()
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
                    "module_scope_id": (
                        goal.module_scope.scope_id
                        if goal.module_scope is not None
                        else None
                    ),
                },
            )
            focused_policy = policy_router.focused_policy
            focused = focused_prove(
                goal,
                action_budget=budget.remaining_actions(),
                timeout_seconds=budget.require_time("focused search"),
                max_depth=task.max_depth,
                branch_scorer=(
                    policy_router.score_focused if focused_policy is not None else None
                ),
            )
            result.search_stats = focused.stats.to_dict()
            result.policy_trace = [
                {
                    **decision.to_dict(),
                    "budget_envelope": search_budget_envelope(task),
                }
                for decision in focused.decisions
            ]
            if focused_policy is not None:
                result.search_stats["nnue_accumulator"] = focused_policy.metrics()
            result.model_calls += focused.stats.model_calls
            result.model_elapsed_ms += focused.stats.model_elapsed_ms
            result.candidates_generated = focused.stats.actions_considered
            budget.account_actions(focused.stats.actions_considered)
            result.cost.add(
                actions_generated=focused.stats.actions_generated,
                actions_expanded=focused.stats.actions_considered,
                actions_scored=focused.stats.model_calls,
                model_batches=focused.stats.policy_nodes,
                model_items_scored=focused.stats.model_calls,
            )
            attempted_terms: set[Term] = set()
            if result.search_stats is None:
                result.search_stats = {}
            search_stats = result.search_stats

            batched_attempted = False

            def attempt_batched_case() -> bool:
                """Run the bounded case engine once and publish terminal results."""

                nonlocal batched_attempted
                if batched_attempted:
                    return False
                batched_attempted = True
                remaining_budget = budget.remaining_actions()
                if remaining_budget <= 0:
                    result.status = "resource-exhausted"
                    result.diagnostics.append(
                        {
                            "kind": "resource",
                            "message": "search action budget exhausted",
                        }
                    )
                    return True
                batched = batched_case_prove(
                    source_file,
                    goal,
                    action_budget=remaining_budget,
                    timeout_seconds=budget.require_time("batched case search"),
                    max_depth=task.max_depth,
                    focused_model=focused_model,
                    refinement_model=refinement_model,
                    policy_router=policy_router,
                    session_factory=session_factory,
                    project_configuration=task.project_configuration,
                )
                batch_stats = batched.stats
                budget.account_actions(batch_stats.actions_considered)
                search_stats["case_batch"] = batch_stats.to_dict()
                result.candidates_generated += batch_stats.actions_considered
                result.model_calls += batch_stats.model_calls
                result.model_elapsed_ms += batch_stats.model_elapsed_ms
                batch_checks = (
                    batch_stats.refinement_queries
                    + batch_stats.case_queries
                    + batch_stats.proof_checks
                    + batch_stats.constructor_catalog_queries
                    + batch_stats.premise_catalog_queries
                    + batch_stats.completion_queries
                )
                result.verifier_calls += batch_checks
                result.cost.add(
                    actions_generated=batch_stats.actions_generated,
                    actions_expanded=batch_stats.actions_considered,
                    actions_scored=batch_stats.model_calls,
                    kernel_loads=batch_stats.kernel_loads,
                    kernel_load_elapsed_ms=batch_stats.kernel_load_elapsed_ms,
                    goal_inspections=batch_stats.goal_inspections,
                    speculative_checks=batch_checks,
                    candidate_terms_checked=batch_stats.proof_checks,
                    refinement_checks=batch_stats.refinement_queries,
                    case_split_checks=batch_stats.case_queries,
                    model_batches=batch_stats.model_batches,
                    model_items_scored=batch_stats.model_calls,
                    generated_subgoals=batch_stats.generated_subgoals,
                    source_bytes_materialized=batch_stats.source_bytes_materialized,
                    source_bytes_written=batch_stats.source_bytes_written,
                )
                if batched.patch is not None and batched.proof_text is not None:
                    _finish_guided_candidate(
                        result,
                        source_file=source_file,
                        patch=batched.patch,
                        proof_text=batched.proof_text,
                        budget=budget,
                        agda_executable=session.executable,
                        agda_version=session.version,
                        project_configuration=task.project_configuration,
                        expected_inputs=original_inputs,
                    )
                    return True
                if batched.status == "resource-exhausted":
                    result.status = "resource-exhausted"
                    result.diagnostics.append(
                        {"kind": "resource", "message": batched.diagnostic}
                    )
                    return True
                return False

            if (
                focused.status == "resource-exhausted"
                and focused.exhaustion_kind == "wall-time"
            ):
                result.status = "resource-exhausted"
                result.diagnostics.append(
                    {"kind": "resource", "message": focused.diagnostic}
                )
                return result

            productive_elimination = (
                productive_elimination_first
                and focused.term is None
                and has_result_subject_elimination_shape(goal.target)
            )
            if productive_elimination and attempt_batched_case():
                return result

            opaque_result = _has_abstract_final_result(goal)
            if (
                focused.term is None
                and not opaque_result
                and isinstance(session, TransactionalKernelSession)
            ):

                def record_constructor_stats(
                    constructor_stats: ConstructorStats,
                ) -> None:
                    search_stats["constructors"] = constructor_stats.to_dict()
                    result.candidates_generated += constructor_stats.actions_considered
                    result.model_calls += constructor_stats.model_calls
                    result.model_elapsed_ms += constructor_stats.model_elapsed_ms
                    constructor_checks = (
                        constructor_stats.constructor_queries
                        + constructor_stats.proof_checks
                        + constructor_stats.catalog_queries
                        + constructor_stats.premise_catalog_queries
                        + constructor_stats.premise_refinement_queries
                        + constructor_stats.completion_queries
                    )
                    result.verifier_calls += constructor_checks
                    result.cost.add(
                        actions_generated=constructor_stats.actions_generated,
                        actions_expanded=constructor_stats.actions_considered,
                        actions_scored=constructor_stats.model_calls,
                        goal_inspections=constructor_stats.goal_inspections,
                        speculative_checks=constructor_checks,
                        candidate_terms_checked=constructor_stats.proof_checks,
                        refinement_checks=(
                            constructor_stats.constructor_queries
                            + constructor_stats.premise_refinement_queries
                        ),
                        model_batches=constructor_stats.model_batches,
                        model_items_scored=constructor_stats.model_calls,
                        generated_subgoals=constructor_stats.generated_subgoals,
                    )

                constructor = constructor_tree_prove(
                    session,
                    goal,
                    action_budget=budget.remaining_actions(),
                    timeout_seconds=budget.require_time("constructor-tree search"),
                    max_depth=task.max_depth,
                    focused_model=focused_model,
                    refinement_model=refinement_model,
                    policy_router=policy_router,
                    excluded_premises=frozenset(
                        (declaration_name_at_goal(source_file.read_text(), goal),)
                    ),
                    on_statistics=record_constructor_stats,
                )
                budget.account_actions(constructor.stats.actions_considered)
                if constructor.solutions:
                    solution = constructor.solutions[0]
                    binders, body = solution.plan.clause_parts()
                    patch = reconstruct_checked_clause_completion(
                        source_file.read_text(),
                        goal,
                        binders=binders,
                        body=body,
                    )
                    _finish_guided_candidate(
                        result,
                        source_file=source_file,
                        patch=patch,
                        proof_text=solution.proof_text,
                        budget=budget,
                        agda_executable=session.executable,
                        agda_version=session.version,
                        project_configuration=task.project_configuration,
                        expected_inputs=original_inputs,
                    )
                    return result

            if focused.status == "no-proof" and budget.remaining_seconds() > 0.01:
                impossibility = certify_impossible(
                    source_file,
                    goal,
                    agda_executable=session.executable,
                    agda_version=session.version,
                    checker_timeout_seconds=min(2.0, budget.remaining_seconds()),
                )
                result.search_stats["impossibility"] = impossibility.metrics()
                result.verifier_calls += impossibility.checker_calls
                result.cost.add(
                    fresh_validation_runs=impossibility.checker_calls,
                )
                if (
                    impossibility.status == "certified"
                    and impossibility.certificate is not None
                ):
                    result.status = "impossible"
                    result.impossibility_certificate = (
                        impossibility.certificate.to_dict()
                    )
                    result.validation = impossibility.validation
                    result.trust_report = impossibility.trust_report
                    result.diagnostics.append(
                        {
                            "kind": "impossibility",
                            "message": (
                                "This goal is impossible: Agda checked a refutation "
                                "of its complete polymorphic type."
                            ),
                        }
                    )
                    return result
                if impossibility.status == "checker-rejected":
                    result.diagnostics.append(
                        {
                            "kind": "impossibility-fallback",
                            "message": (
                                "refutation certification failed; continuing ordinary "
                                "proof search"
                            ),
                        }
                    )

            if focused.term is not None:
                attempted_terms.add(focused.term)
                rendered = render_term(focused.term)
                checked = session.check_candidate(goal.goal_id, rendered)
                result.verifier_calls += 1
                result.cost.add(
                    speculative_checks=1,
                    candidate_terms_checked=1,
                )
                result.attempts.append(
                    CandidateAttempt(
                        term=focused.term.to_dict(),
                        rendered=rendered,
                        outcome="accepted" if checked.accepted else "invalid",
                        diagnostic=checked.diagnostic[:2000],
                    )
                )
                if checked.accepted:
                    _finish_verified_candidate(
                        result,
                        source_file=source_file,
                        goal=goal,
                        term=focused.term,
                        rendered=rendered,
                        budget=budget,
                        agda_executable=session.executable,
                        agda_version=session.version,
                        project_configuration=task.project_configuration,
                        expected_inputs=original_inputs,
                    )
                    return result
                result.diagnostics.append(
                    {
                        "kind": "focused-fallback",
                        "message": (
                            "Agda rejected the focused-fragment proposal; "
                            "continuing with kernel-guided enumeration"
                        ),
                    }
                )
                result.policy_trace = []

            if not batched_attempted and attempt_batched_case():
                return result

            remaining_budget = budget.remaining_actions()
            if remaining_budget <= 0:
                result.status = "resource-exhausted"
                result.diagnostics.append(
                    {"kind": "resource", "message": "search action budget exhausted"}
                )
                return result
            guided = guided_prove(
                source_file,
                goal,
                action_budget=remaining_budget,
                timeout_seconds=budget.require_time("guided search"),
                max_depth=task.max_depth,
                focused_model=focused_model,
                refinement_model=refinement_model,
                policy_router=policy_router,
                session_factory=session_factory,
                project_configuration=task.project_configuration,
            )
            budget.account_actions(guided.stats.actions_considered)
            result.search_stats["guided"] = guided.stats.to_dict()
            result.candidates_generated += guided.stats.actions_considered
            result.model_calls += guided.stats.model_calls
            result.model_elapsed_ms += guided.stats.model_elapsed_ms
            result.verifier_calls += (
                guided.stats.refinement_queries + guided.stats.case_queries
            )
            result.cost.add(
                actions_generated=guided.stats.actions_generated,
                actions_expanded=guided.stats.actions_considered,
                actions_scored=guided.stats.model_calls,
                kernel_loads=guided.stats.kernel_loads,
                goal_inspections=guided.stats.goal_inspections,
                speculative_checks=(
                    guided.stats.refinement_queries + guided.stats.case_queries
                ),
                refinement_checks=guided.stats.refinement_queries,
                case_split_checks=guided.stats.case_queries,
                model_batches=guided.stats.model_batches,
                model_items_scored=guided.stats.model_calls,
                generated_subgoals=guided.stats.generated_subgoals,
                source_bytes_materialized=guided.stats.source_bytes_materialized,
                source_bytes_written=guided.stats.source_bytes_written,
                kernel_load_elapsed_ms=guided.stats.kernel_load_elapsed_ms,
            )
            if guided.status == "resource-exhausted":
                result.status = "resource-exhausted"
                result.diagnostics.append(
                    {"kind": "resource", "message": guided.diagnostic}
                )
                return result
            if guided.patch is not None and guided.proof_text is not None:
                _finish_guided_candidate(
                    result,
                    source_file=source_file,
                    patch=guided.patch,
                    proof_text=guided.proof_text,
                    budget=budget,
                    agda_executable=session.executable,
                    agda_version=session.version,
                    project_configuration=task.project_configuration,
                    expected_inputs=original_inputs,
                )
                return result

            local_names = tuple(
                entry.name for entry in goal.context if entry.in_scope and entry.name
            )
            candidates: list[Term] = []
            generation_complete = False
            generated = iter_terms(
                local_names,
                max_lambdas=3,
                max_size=task.max_term_size,
                continue_search=lambda: not budget.wall_exhausted(),
            )
            while len(candidates) < budget.remaining_actions():
                try:
                    term = next(generated)
                except StopIteration:
                    generation_complete = True
                    break
                if term not in attempted_terms:
                    candidates.append(term)
            if budget.wall_exhausted():
                raise TimeoutError("wall-time budget exhausted during term generation")
            result.candidates_generated += len(candidates)
            result.cost.add(actions_generated=len(candidates))
            ranking_started = time.monotonic()
            legacy_ranker = "nnue" if term_model is not None else "symbolic"
            ranked = rank_candidates(
                goal,
                candidates,
                ranker=legacy_ranker,
                model=term_model,
            )
            if term_model is not None:
                result.model_calls += len(ranked)
                result.model_elapsed_ms += (time.monotonic() - ranking_started) * 1000.0
                result.cost.add(
                    actions_scored=len(ranked),
                    model_batches=int(bool(ranked)),
                    model_items_scored=len(ranked),
                )

            for candidate in ranked:
                if not budget.charge_action():
                    result.status = "resource-exhausted"
                    result.diagnostics.append(
                        {
                            "kind": "resource",
                            "message": "candidate or wall-time budget exhausted",
                        }
                    )
                    break
                result.cost.add(actions_expanded=1)
                rendered = render_term(candidate.term)
                checked = session.check_candidate(goal.goal_id, rendered)
                result.verifier_calls += 1
                result.cost.add(
                    speculative_checks=1,
                    candidate_terms_checked=1,
                )
                attempt = CandidateAttempt(
                    term=candidate.term.to_dict(),
                    rendered=rendered,
                    outcome="accepted" if checked.accepted else "invalid",
                    diagnostic=checked.diagnostic[:2000],
                    nnue_score=candidate.nnue_score,
                )
                result.attempts.append(attempt)
                if not checked.accepted:
                    continue

                _finish_verified_candidate(
                    result,
                    source_file=source_file,
                    goal=goal,
                    term=candidate.term,
                    rendered=rendered,
                    budget=budget,
                    agda_executable=session.executable,
                    agda_version=session.version,
                    project_configuration=task.project_configuration,
                    expected_inputs=original_inputs,
                )
                break
            else:
                if generation_complete:
                    result.status = "unsolved"
                    result.diagnostics.append(
                        {
                            "kind": "search",
                            "message": "finite P0 candidate fragment was exhausted",
                        }
                    )
                else:
                    result.status = "resource-exhausted"
                    result.diagnostics.append(
                        {
                            "kind": "resource",
                            "message": "search action budget exhausted",
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
        result.elapsed_ms = (time.monotonic() - started) * 1000.0
        if policy_router is not None:
            result.policy_trace.extend(policy_router.recorder.to_list())
            if result.search_stats is None:
                result.search_stats = {}
            result.search_stats["or_policy"] = policy_router.metrics()
        if not include_attempts and result.attempts:
            result.attempts = []
    return result


def _finish_verified_candidate(
    result: ProverResult,
    *,
    source_file: Path,
    goal: GoalInfo,
    term: Term,
    rendered: str,
    budget: SearchBudget,
    agda_executable: str,
    agda_version: str,
    project_configuration: ProjectConfiguration | None = None,
    expected_inputs: ProjectInputs | None = None,
) -> None:
    """Reconstruct and independently validate an Agda-accepted term."""

    patch = reconstruct_term_as_clause(
        source_file.read_text(),
        goal,
        term,
        forbidden_names=(entry.name for entry in goal.context),
    )
    validation, trust_report = validate_reconstruction(
        source_file,
        patch,
        agda_executable=agda_executable,
        agda_version=agda_version,
        timeout_seconds=budget.require_time("fresh proof validation"),
        expected_inputs=expected_inputs,
        project_configuration=project_configuration,
    )
    result.cost.add(fresh_validation_runs=validation.get("fresh_validation_runs", 1))
    result.validation = validation
    result.trust_report = trust_report
    patch_binders = patch.get("binders")
    patch_body = patch.get("body")
    display_term = rendered
    if (
        patch.get("style") == "clause"
        and isinstance(patch_binders, list)
        and patch_binders
        and all(isinstance(name, str) for name in patch_binders)
        and isinstance(patch_body, str)
    ):
        display_term = f"λ {' '.join(patch_binders)} → {patch_body}"
    result.proof_term = format_proof_term(display_term).text
    result.patch = patch
    if validation["checked"]:
        result.status = "verified"
    elif validation["timed_out"]:
        result.status = "resource-exhausted"
        result.diagnostics.append(
            {"kind": "resource", "message": "fresh validation timed out"}
        )
    else:
        prefix_status = validation.get("prefix_validation", {}).get("status")
        result.status = (
            "toolchain-error"
            if prefix_status == "unavailable"
            else "resource-exhausted"
            if prefix_status == "resource-exhausted"
            else "unsolved"
            if prefix_status is not None
            else "internal-error"
        )
        result.diagnostics.append(
            {
                "kind": "validation-mismatch",
                "message": validation["diagnostic"] or "fresh Agda rejected candidate",
            }
        )


def _finish_guided_candidate(
    result: ProverResult,
    *,
    source_file: Path,
    patch: dict[str, object],
    proof_text: str,
    budget: SearchBudget,
    agda_executable: str,
    agda_version: str,
    project_configuration: ProjectConfiguration | None = None,
    expected_inputs: ProjectInputs | None = None,
) -> None:
    """Fresh-validate a completed multi-step source reconstruction."""

    validation, trust_report = validate_reconstruction(
        source_file,
        patch,
        agda_executable=agda_executable,
        agda_version=agda_version,
        timeout_seconds=budget.require_time("fresh guided-proof validation"),
        expected_inputs=expected_inputs,
        project_configuration=project_configuration,
    )
    result.cost.add(fresh_validation_runs=validation.get("fresh_validation_runs", 1))
    result.validation = validation
    result.trust_report = trust_report
    result.proof_term = proof_text
    result.patch = patch
    if validation["checked"]:
        result.status = "verified"
    elif validation["timed_out"]:
        result.status = "resource-exhausted"
        result.diagnostics.append(
            {"kind": "resource", "message": "fresh validation timed out"}
        )
    else:
        prefix_status = validation.get("prefix_validation", {}).get("status")
        result.status = (
            "toolchain-error"
            if prefix_status == "unavailable"
            else "resource-exhausted"
            if prefix_status == "resource-exhausted"
            else "unsolved"
            if prefix_status is not None
            else "internal-error"
        )
        result.diagnostics.append(
            {
                "kind": "validation-mismatch",
                "message": validation["diagnostic"]
                or "fresh Agda rejected guided proof",
            }
        )
