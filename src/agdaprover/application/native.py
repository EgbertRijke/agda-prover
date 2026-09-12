"""Opt-in native controllers through the shared application trust boundary.

Only setup/inspection and final validation use the Python kernel API. Every
intermediate application, argument choice and rollback stays inside Haskell.
Only coarse candidate boundaries cross into Python. Source acceptance remains
independently checked; user-facing default promotion is a separate milestone.
"""

from __future__ import annotations

import hashlib
import json
import time
from collections.abc import Generator
from contextlib import closing
from dataclasses import dataclass
from pathlib import Path
from typing import Any, ClassVar, Literal

from ..artifacts import executable_sha256, file_sha256
from ..bridge.agenda import search_agenda
from ..bridge.configuration import project_request
from ..bridge.contracts import BridgeBudget, BridgeError, BridgeFailure
from ..bridge.project import resolve_project
from ..bridge.resources import CancellationToken, current_process_rss
from ..bridge.symbolic import SymbolicProtocolError, search_evidence
from ..bridge.workspace import project_inputs
from ..budget import SearchBudget
from ..contracts import ProverResult, StepResult, TaskSpec, task_identity
from ..kernel.p0 import AgdaBridgeError, open_kernel_session
from ..kernel.protocol import KernelSessionFactory
from ..observability.policy_trace import validated_proof_evidence
from ..offline import assert_offline_configuration
from ..principal_variation import PrincipalVariationObserver
from ..project import choose_goal, choose_goal_prefix, require_agda_source_file
from ..reconstruction import reconstruct_native_batch
from ..resource_budget import ResourceLimitError, ResourceScope
from ..validation import (
    ValidationError,
    validate_reconstruction,
    validate_standalone_module,
)
from ..verifier_budget import VerifierCallLimitExceeded, VerifierCallScope
from .native_models import load_native_models
from .native_receipts import NativeReceipts
from .native_refutation import (
    CERTIFICATE_SCHEMA,
    FILENAME,
    replay_source,
)
from .native_step import NativeStepAttempt, accept_native_step
from .native_variation import native_principal_variation


@dataclass(frozen=True)
class NativeProofEngine:
    controller: ClassVar[str] = "agenda"
    executable: Path
    work_units: int | None = None
    policy_model: Path | None = None
    native_scorer: Path | None = None
    trace_bytes: int = 16 * 1024 * 1024
    focused_search: bool = True

    def prove(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None = None,
    ) -> ProverResult:
        return self._prove(
            task,
            session_factory=session_factory,
            cancellation=cancellation,
            prefix=False,
        )

    def prove_prefix(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None = None,
        progress_observer: PrincipalVariationObserver | None = None,
    ) -> ProverResult:
        return self._prove(
            task,
            session_factory=session_factory,
            cancellation=cancellation,
            prefix=True,
            progress_observer=progress_observer,
        )

    def _prove(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None,
        prefix: bool,
        progress_observer: PrincipalVariationObserver | None = None,
    ) -> ProverResult:
        result = self._run(
            task,
            session_factory=session_factory,
            cancellation=cancellation,
            prefix=prefix,
            progress_observer=progress_observer,
        )
        assert isinstance(result, ProverResult)
        return result

    def step(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        collect_all: bool = False,
    ) -> StepResult:
        result = self._run(
            task,
            session_factory=session_factory,
            cancellation=None,
            prefix=False,
            one_move=True,
            collect_all=collect_all,
        )
        assert isinstance(result, StepResult)
        return result

    def _run(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None,
        prefix: bool,
        progress_observer: PrincipalVariationObserver | None = None,
        one_move: bool = False,
        collect_all: bool = False,
    ) -> ProverResult | StepResult:
        started = time.monotonic()
        source = task.source_file.resolve()
        profile = "native-step-v1" if one_move else f"native-{self.controller}-v1"
        mode = f"native-{self.controller}-{'step' if one_move else 'prefix' if prefix else 'single'}"
        result: ProverResult | StepResult = (StepResult if one_move else ProverResult)(
            task_identity(
                task,
                "unavailable",
                mode=f"{mode}-preparation",
                policy_profile=profile,
                toolchain_id=None,
                model_ids={},
            ),
            "internal-error",
            str(source),
            "unavailable",
            task.ranker,
            policy_profile=profile,
        )
        scope = ResourceScope(task.resources, memory_sample=current_process_rss)
        calls = VerifierCallScope()
        value_error_status: Literal["invalid-task", "internal-error"] = "invalid-task"
        try:
            scope.open()
            calls.open(task.max_verifier_calls)
            budget = SearchBudget(
                task.max_candidates, task.timeout_seconds, started_at=started
            )
            if self.work_units is not None and (
                type(self.work_units) is not int or self.work_units <= 0
            ):
                raise ValueError("native work_units must be positive or None")
            if type(self.trace_bytes) is not int or self.trace_bytes < 0:
                raise ValueError("trace_bytes must be nonnegative")
            if type(self.focused_search) is not bool:
                raise ValueError("focused_search must be a boolean")
            if task.max_depth is not None and (
                type(task.max_depth) is not int or task.max_depth < 0
            ):
                raise ValueError("native max_depth must be nonnegative or None")
            if task.max_depth is not None and self.controller != "agenda":
                raise ValueError(
                    "explicit depth limits require the native agenda controller"
                )
            if prefix and self.controller != "agenda":
                raise ValueError(
                    "the evidence-only controller does not implement joint solving"
                )
            if one_move and self.controller != "agenda":
                raise ValueError(
                    "the evidence-only controller does not implement one-step search"
                )
            work_units = self.work_units
            assert_offline_configuration(task, deadline=budget.deadline)
            require_agda_source_file(source)
            result.source_hash = file_sha256(source, deadline=budget.deadline)
            project, _ = resolve_project(
                project_request(source, task.project_configuration),
                BridgeBudget.for_run(budget.require_time("project resolution")),
            )
            if project.toolchain.version != "2.8.0":
                raise ValueError(
                    "native symbolic search requires the pinned Agda 2.8.0 toolchain"
                )
            inputs = project_inputs(project)
            result.toolchain_id = project.toolchain.executable_sha256[:20]
            binary_hash = executable_sha256(
                str(self.executable), deadline=budget.deadline
            )
            result.search_stats = {
                "algorithm": result.policy_profile,
                "engine": "haskell",
                "native_executable_sha256": binary_hash,
                "native_work_limit": work_units,
                "native_action_limit": task.max_candidates
                if self.controller == "agenda"
                else None,
                "native_work_unit": "scheduler-step-or-checking-attempt-or-symbolic-action",
                "completion_known": False,
                "final_search_cost": None,
            }
            models = load_native_models(
                task,
                one_move=one_move,
                policy_override=self.policy_model,
                deadline=budget.deadline,
            )
            result.action_model_id = models.or_id
            result.model_id = models.primary_id
            result.search_stats["primary_model_role"] = models.primary_role
            identity = task_identity(
                task,
                result.source_hash,
                mode=mode,
                policy_profile=result.policy_profile,
                toolchain_id=result.toolchain_id,
                model_ids={
                    role: identity for role, identity in models.identities.items()
                },
                project_inputs_id=inputs.identity,
            )
            result.task_id = hashlib.sha256(
                json.dumps(
                    [identity, binary_hash, work_units, self.focused_search]
                ).encode()
            ).hexdigest()
            with open_kernel_session(
                session_factory,
                timeout_seconds=budget.require_time("goal inspection"),
                deadline=budget.deadline,
                project_configuration=task.project_configuration,
            ) as session:
                goals = session.load_module(source)
                if prefix:
                    cutoff, targets = choose_goal_prefix(goals, task)
                    goal = session.inspect_goal(cutoff)
                else:
                    goal = session.inspect_goal(
                        choose_goal(goals, task.goal_id, task.goal_position)
                    )
                    targets = (goal,)
            result.goal = goal.to_dict()
            if isinstance(result, ProverResult):
                result.joint_goals = (
                    [target.to_dict() for target in targets] if prefix else []
                )
            result.cost.kernel_loads = 1
            result.cost.goal_inspections = 1
            value_error_status = "internal-error"
            inputs.assert_current(deadline=budget.deadline)
            recorder = NativeReceipts(result, self.trace_bytes)
            arguments: dict[str, Any] = dict(
                budget=BridgeBudget.for_run(budget.require_time("native search")),
                work_units=work_units,
                ranker=models.mode,
                model_path=models.or_path,
                focused_model_path=None,
                primary_model_path=models.primary_path,
                focused_search=self.focused_search,
                native_path=self.native_scorer,
                cancellation=cancellation or CancellationToken(),
                publish=recorder.publish,
            )

            def candidates() -> Generator[dict[str, Any], None, None]:
                if self.controller == "agenda":
                    yield from search_agenda(
                        self.executable,
                        project,
                        tuple(g.goal_id for g in targets),
                        action_limit=task.max_candidates,
                        depth_limit=task.max_depth,
                        principal_variations=progress_observer is not None,
                        one_move=one_move,
                        **arguments,
                    )
                else:
                    yield search_evidence(
                        self.executable, project, goal.goal_id, **arguments
                    )

            result.status = "unsolved"
            result.cost.kernel_loads += 1
            with closing(candidates()) as replies:
                for reply in replies:
                    inputs.assert_current(deadline=budget.deadline)
                    if (
                        executable_sha256(
                            str(self.executable), deadline=budget.deadline
                        )
                        != binary_hash
                    ):
                        raise SymbolicProtocolError(
                            "native executable changed during search"
                        )
                    outcome = reply["outcome"]
                    if outcome.get("failure", {}).get("reason") == "cancelled":
                        raise ResourceLimitError("native search was cancelled")
                    if "failure" in outcome:
                        raise SymbolicProtocolError(str(outcome["failure"]))
                    if self.controller == "evidence" and (
                        outcome.get("model_id") != result.action_model_id
                        or outcome.get("focused_model_id") != result.model_id
                        or outcome.get("primary_model_role") != models.primary_role
                    ):
                        raise SymbolicProtocolError(
                            "native evidence uses unpinned models"
                        )
                    status = outcome.get("status")
                    if status == "principal-variation":
                        if progress_observer is None:
                            raise SymbolicProtocolError(
                                "unexpected native principal variation"
                            )
                        progress_observer(
                            native_principal_variation(
                                outcome,
                                task_id=result.task_id,
                                source_file=source,
                                source_sha256=result.source_hash,
                                targets=targets,
                                original_source=source.read_bytes().decode("utf-8"),
                            )
                        )
                        continue
                    if status == "paused" and outcome.get("reason") in {
                        "allowance-spent",
                        "action-allowance-spent",
                        "depth-limit-reached",
                        "cancelled",
                    }:
                        if isinstance(result, StepResult) and result.action is not None:
                            result.search_stats["enumeration_censored"] = True
                            break
                        raise ResourceLimitError(f"native search {outcome['reason']}")
                    if status == "refutation-candidate":
                        if isinstance(result, StepResult):
                            raise SymbolicProtocolError(
                                "one-step search returned a refutation"
                            )
                        proposal = outcome.get("refutation")
                        if not isinstance(proposal, dict):
                            raise SymbolicProtocolError(
                                "invalid native refutation response"
                            )
                        certificate_source = replay_source(proposal, goal.goal_id)
                        result.search_stats["refutation"] = {
                            "status": proposal["status"],
                            "assignments_checked": proposal["assignments_checked"],
                        }
                        validation, trust = validate_standalone_module(
                            certificate_source,
                            filename=FILENAME,
                            agda_executable=str(project.toolchain.executable),
                            timeout_seconds=budget.require_time(
                                "fresh native refutation validation"
                            ),
                            policy_profile="native-implication-refutation-v1",
                        )
                        inputs.assert_current(deadline=budget.deadline)
                        result.validation, result.trust_report = validation, trust
                        if validation["checked"]:
                            result.impossibility_certificate = {
                                "schema_version": CERTIFICATE_SCHEMA,
                                "method": "agda-checked-implication-refutation",
                                "source_sha256": result.source_hash,
                                "task_id": result.task_id,
                                "native_executable_sha256": binary_hash,
                                "proposal": proposal,
                                "generated_module_sha256": hashlib.sha256(
                                    certificate_source.encode()
                                ).hexdigest(),
                                "agda_binary_sha256": trust["agda_binary_hash"],
                                "agda_version": trust["agda_version"],
                                "checker_output_sha256": validation[
                                    "checker_output_sha256"
                                ],
                            }
                            result.status = "impossible"
                            break
                        if validation["timed_out"]:
                            raise ResourceLimitError(
                                "fresh native refutation validation timed out"
                            )
                        result.diagnostics.append(
                            {
                                "kind": "refutation-rejection",
                                "message": validation.get(
                                    "diagnostic", "fresh checker rejected refutation"
                                ),
                            }
                        )
                        continue
                    if status in {"unsolved", "resource-exhausted"}:
                        if not isinstance(result, StepResult) or result.action is None:
                            result.status = status
                        break
                    if status != "candidate":
                        raise SymbolicProtocolError(
                            f"invalid native search outcome: {outcome}"
                        )
                    exported = reply.get("source_export", {})
                    if exported.get("reason") == "cancelled":
                        raise ResourceLimitError("native source export was cancelled")
                    if exported.get("reason") not in {
                        None,
                        "kernel-rejected",
                        "kernel-blocked",
                    }:
                        raise SymbolicProtocolError(
                            f"native source export failed: {exported}"
                        )
                    if exported.get("status") not in {
                        "apparently-closed",
                        "accepted-partial",
                    }:
                        result.diagnostics.append(
                            {"kind": "reconstruction", "message": str(exported)}
                        )
                        continue
                    entries = exported.get("entries", [])
                    if isinstance(result, StepResult):
                        try:
                            action = accept_native_step(
                                task,
                                goal,
                                entries,
                                timeout_seconds=budget.require_time(
                                    "fresh native step validation"
                                ),
                            )
                        except (ValueError, ValidationError) as error:
                            result.diagnostics.append(
                                {"kind": "step-rejection", "message": str(error)}
                            )
                            continue
                        inputs.assert_current(deadline=budget.deadline)
                        result.attempts.append(
                            NativeStepAttempt(
                                action,
                                "accepted" if result.action is None else "applicable",
                            )
                        )
                        result.cost.generated_subgoals += len(
                            action["expected_state_effect"]["subgoals"]
                        )
                        if result.action is None:
                            result.action = action
                        result.status = "accepted-step"
                        if not collect_all:
                            break
                        continue
                    patch = reconstruct_native_batch(
                        source.read_text(), targets, entries
                    )
                    validation, trust = validate_reconstruction(
                        source,
                        patch,
                        agda_executable=str(project.toolchain.executable),
                        agda_version=project.toolchain.version,
                        timeout_seconds=budget.require_time(
                            "fresh native proof validation"
                        ),
                        project_configuration=task.project_configuration,
                        expected_inputs=inputs,
                    )
                    result.validation, result.trust_report = validation, trust
                    if validation["checked"]:
                        result.proof_term = "\n".join(
                            e["evidence"]["display"] for e in entries
                        )
                        result.patch, result.status = patch, "verified"
                        witness = validated_proof_evidence(
                            task_id=result.task_id,
                            source_sha256=result.source_hash,
                            patch=patch,
                            validation=validation,
                            trust_report=trust,
                        )
                        if witness is not None and outcome.get("selected_choices"):
                            # Do not invent proof credits from visited branches.
                            result.search_stats["validated_native_choices"] = {
                                "choices": outcome["selected_choices"],
                                "evidence": witness,
                            }
                        break
                    result.diagnostics.append(
                        {
                            "kind": "validation-rejection",
                            "message": validation.get(
                                "diagnostic", "fresh validation rejected candidate"
                            ),
                        }
                    )
                    if validation["timed_out"]:
                        raise ResourceLimitError(
                            "fresh native proof validation exhausted its allowance"
                        )
        except (TimeoutError, ResourceLimitError, VerifierCallLimitExceeded) as error:
            result.status = "resource-exhausted"
            result.diagnostics.append({"kind": "resource", "message": str(error)})
        except BridgeError as error:
            result.status = (
                "resource-exhausted"
                if error.failure
                in {
                    BridgeFailure.TIMEOUT,
                    BridgeFailure.RESOURCE_EXHAUSTED,
                    BridgeFailure.CANCELLED,
                }
                else "toolchain-error"
            )
            result.diagnostics.append({"kind": "bridge", "message": str(error)})
        except (
            OSError,
            ValueError,
            ValidationError,
            SymbolicProtocolError,
            AgdaBridgeError,
        ) as error:
            result.status = (
                "internal-error"
                if isinstance(error, (SymbolicProtocolError, ValidationError))
                else value_error_status
                if isinstance(error, ValueError)
                else "toolchain-error"
            )
            result.diagnostics.append({"kind": "native-search", "message": str(error)})
        finally:
            exhaustion = scope.finish()
            if exhaustion is not None:
                result.status = "resource-exhausted"
                if isinstance(result, ProverResult):
                    result.proof_term = result.patch = None
                    result.impossibility_certificate = None
                else:
                    result.action = None
                if result.search_stats is not None:
                    result.search_stats.pop("validated_native_choices", None)
                result.diagnostics.append(
                    {"kind": "resource", "message": str(exhaustion)}
                )
            result.resource_budget = scope.ledger.report()
            result.verifier_budget = calls.report()
            result.verifier_calls = int((result.verifier_budget or {}).get("used") or 0)
            result.cost.fresh_validation_runs = calls.fresh_validation_runs
            calls.close()
            result.elapsed_ms = (time.monotonic() - started) * 1000
            if isinstance(result, StepResult) and result.status != "accepted-step":
                result.action = None
        return result


class NativeEvidenceEngine(NativeProofEngine):
    """Compatibility entry point for the first, finite evidence-only slice."""

    controller = "evidence"


class NativeAgendaEngine(NativeProofEngine):
    """Explicit opt-in autonomous controller; no Python symbolic callbacks."""
