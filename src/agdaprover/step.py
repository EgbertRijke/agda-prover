"""Kernel-checked one-step refinement search for interactive use."""

from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Literal

from .actions import (
    RefinementAttempt,
    RefinementCandidate,
    action_result,
)
from .artifacts import optional_file_sha256
from .bridge.resources import current_process_rss
from .budget import SearchBudget
from .contracts import GoalInfo, StepResult, TaskSpec, task_identity
from .kernel.p0 import AgdaBridgeError, AgdaLoadError, AgdaSession
from .kernel.protocol import KernelSessionFactory
from .offline import assert_offline_configuration
from .presentation import reconstruct_case_split, reconstruct_intro_as_clause
from .project import attach_module_scope, choose_goal, require_agda_source_file
from .ranking.protocol import StepActionRanker
from .ranking.runtime import load_step_model
from .reasoning.providers import (
    ActionProvider,
    refinement_action_provider,
)
from .resource_budget import ResourceLimitError, ResourceScope
from .symbolic_ir import action_from_refinement
from .verification import (
    ValidationError,
    file_sha256,
    validate_partial_reconstruction,
)
from .verifier_budget import VerifierCallLimitExceeded, VerifierCallScope


@dataclass(frozen=True)
class RankedRefinement:
    candidate: RefinementCandidate
    symbolic_key: tuple[int, int, str]
    nnue_score: float | None


def _required_score(score: float | None) -> float:
    if score is None:
        raise ValueError("NNUE-ranked refinement has no score")
    return score


def rank_refinements(
    goal: GoalInfo,
    candidates: list[RefinementCandidate],
    *,
    ranker: str,
    model: StepActionRanker | None,
) -> list[RankedRefinement]:
    scores = (
        model.score_refinement_actions(goal, candidates)
        if ranker == "nnue" and model is not None
        else [None] * len(candidates)
    )
    ranked = [
        RankedRefinement(candidate, candidate.symbolic_key(goal), score)
        for candidate, score in zip(candidates, scores, strict=True)
    ]
    if ranker == "symbolic":
        return sorted(ranked, key=lambda item: item.symbolic_key)
    if ranker == "nnue":
        if model is None:
            raise ValueError("NNUE ranking requires a model")
        return sorted(
            ranked,
            key=lambda item: (-_required_score(item.nnue_score), item.symbolic_key),
        )
    raise ValueError(f"unsupported ranker: {ranker}")


def propose_step(
    task: TaskSpec,
    *,
    collect_all: bool = False,
    session_factory: KernelSessionFactory = AgdaSession,
    action_provider: ActionProvider[RefinementCandidate] = refinement_action_provider,
) -> StepResult:
    """Return the best ranked refinement that Agda accepts for the selected goal."""

    started = time.monotonic()
    source_file = task.source_file.resolve()
    result = StepResult(
        task_id=task_identity(
            task,
            "",
            mode="step",
            policy_profile="p0-step-v2",
            toolchain_id=None,
            model_ids={"step": None},
        ),
        status="internal-error",
        source_file=str(source_file),
        source_hash="",
        ranker=task.ranker,
    )
    call_scope = VerifierCallScope()
    resource_scope = ResourceScope(task.resources, memory_sample=current_process_rss)
    try:
        resource_scope.open()
        call_scope.open(task.max_verifier_calls)
        require_agda_source_file(source_file)
        if task.max_candidates <= 0 or (
            task.timeout_seconds is not None and task.timeout_seconds <= 0
        ):
            raise ValueError("budgets must be positive")
        budget = SearchBudget(
            task.max_candidates,
            task.timeout_seconds,
            started_at=started,
        )
        assert_offline_configuration(task, deadline=budget.deadline)
        result.source_hash = file_sha256(source_file, deadline=budget.deadline)
        result.task_id = task_identity(
            task,
            result.source_hash,
            mode="step",
            policy_profile=result.policy_profile,
            toolchain_id=None,
            model_ids={
                "step": optional_file_sha256(task.model_path, deadline=budget.deadline)
            },
        )

        model = load_step_model(task, deadline=budget.deadline)
        if model is not None:
            result.model_id = model.model_id

        with session_factory(
            timeout_seconds=budget.require_time("initial Agda load"),
            deadline=budget.deadline,
        ) as session:
            result.toolchain_id = session.toolchain_id
            result.task_id = task_identity(
                task,
                result.source_hash,
                mode="step",
                policy_profile=result.policy_profile,
                toolchain_id=result.toolchain_id,
                model_ids={"step": result.model_id},
            )
            load_started = time.monotonic()
            loaded = session.load_module(source_file)
            result.cost.add(
                kernel_loads=1,
                kernel_load_elapsed_ms=(time.monotonic() - load_started) * 1000.0,
            )
            selected = choose_goal(loaded, task.goal_id, task.goal_position)
            goal = attach_module_scope(
                session.inspect_goal(selected), source_file.read_text(), source_file
            )
            result.cost.add(goal_inspections=1)
            result.goal = goal.to_dict()
            candidates = list(action_provider.propose(goal).payloads)
            result.candidates_generated = len(candidates)
            result.cost.add(actions_generated=len(candidates))
            ranking_started = time.monotonic()
            ranked = rank_refinements(goal, candidates, ranker=task.ranker, model=model)
            if model is not None:
                result.model_calls = len(ranked)
                result.model_elapsed_ms = (time.monotonic() - ranking_started) * 1000.0
                result.cost.add(
                    actions_scored=len(ranked),
                    model_batches=1,
                    model_items_scored=len(ranked),
                )

            selected_action: (
                tuple[int, RankedRefinement, str, tuple[dict[str, object], ...]] | None
            ) = None
            for rank, item in enumerate(ranked, 1):
                if not budget.charge_action():
                    if selected_action is None:
                        result.status = "resource-exhausted"
                        result.diagnostics.append(
                            {
                                "kind": "resource",
                                "message": "candidate or wall-time budget exhausted",
                            }
                        )
                    break
                result.cost.add(actions_expanded=1)
                load_started = time.monotonic()
                loaded = session.load_module(source_file)
                result.cost.add(
                    kernel_loads=1,
                    kernel_load_elapsed_ms=(time.monotonic() - load_started) * 1000.0,
                )
                selected = choose_goal(loaded, task.goal_id, task.goal_position)
                if item.candidate.tag == "case-split":
                    case_checked = session.check_case_split(
                        selected.goal_id, item.candidate.expression
                    )
                    accepted = case_checked.accepted
                    preview = "\n".join(case_checked.clauses) or None
                    checked_goals: tuple[dict[str, object], ...] = ()
                    diagnostic = case_checked.diagnostic
                else:
                    checked = session.check_refinement(
                        selected.goal_id, item.candidate.expression
                    )
                    accepted = checked.accepted
                    preview = checked.preview
                    checked_goals = checked.generated_goals
                    diagnostic = checked.diagnostic
                result.verifier_calls += 1
                result.cost.add(
                    speculative_checks=1,
                    case_split_checks=int(item.candidate.tag == "case-split"),
                    refinement_checks=int(item.candidate.tag != "case-split"),
                    generated_subgoals=len(checked_goals),
                )
                outcome: Literal["accepted", "applicable", "invalid"] = "invalid"
                if accepted:
                    outcome = "accepted" if selected_action is None else "applicable"
                    if selected_action is None:
                        selected_action = (
                            rank,
                            item,
                            preview or item.candidate.expression,
                            checked_goals,
                        )
                result.attempts.append(
                    RefinementAttempt(
                        candidate=item.candidate,
                        outcome=outcome,
                        diagnostic=diagnostic[:2000],
                        nnue_score=item.nnue_score,
                        preview=preview,
                        generated_goals=checked_goals,
                    )
                )
                if accepted and not collect_all:
                    break

        if selected_action is not None:
            rank, item, preview, generated_goals = selected_action
            source_edit = None
            reconstruction_validation = None
            if item.candidate.tag == "introduce-lambda":
                source_edit = reconstruct_intro_as_clause(
                    source_file.read_text(), goal, preview
                )
                reconstruction_validation = validate_partial_reconstruction(
                    source_file,
                    source_edit,
                    timeout_seconds=budget.require_time(
                        "step reconstruction validation"
                    ),
                )
                result.verifier_calls += 1
                result.cost.add(fresh_validation_runs=1)
            elif item.candidate.tag == "case-split":
                source_edit = reconstruct_case_split(
                    source_file.read_text(), goal, preview.splitlines()
                )
                reconstruction_validation = validate_partial_reconstruction(
                    source_file,
                    source_edit,
                    timeout_seconds=budget.require_time(
                        "case reconstruction validation"
                    ),
                )
                generated_goals = tuple(
                    reconstruction_validation.get("generated_goals", [])
                )
                result.verifier_calls += 1
                result.cost.add(
                    fresh_validation_runs=1,
                    generated_subgoals=len(generated_goals),
                )
            result.action = action_result(
                item.candidate,
                preview=preview,
                generated_goals=generated_goals,
                rank=rank,
                nnue_score=item.nnue_score,
                source_edit=source_edit,
                reconstruction_validation=reconstruction_validation,
                elaboration_strategy=(
                    "Cmd_make_case"
                    if item.candidate.tag == "case-split"
                    else "Cmd_refine_or_intro"
                ),
                module_scope_id=(
                    goal.module_scope.scope_id
                    if goal.module_scope is not None
                    else None
                ),
            )
            result.action["symbolic_action"] = action_from_refinement(
                goal, item.candidate
            ).to_dict()
            result.status = "accepted-step"
        elif result.status != "resource-exhausted":
            result.status = "unsolved"
            result.diagnostics.append(
                {
                    "kind": "search",
                    "message": "finite P0 refinement action fragment was exhausted",
                }
            )
    except (ValueError, AgdaLoadError) as error:
        result.status = "invalid-task"
        result.diagnostics.append({"kind": "input", "message": str(error)})
    except AgdaBridgeError as error:
        result.status = "toolchain-error"
        result.diagnostics.append({"kind": "protocol", "message": str(error)})
    except ValidationError as error:
        result.status = "internal-error"
        result.diagnostics.append({"kind": "reconstruction", "message": str(error)})
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
    return result
