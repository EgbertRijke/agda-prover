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
from typing import Any, ClassVar

from ..artifacts import executable_sha256, file_sha256
from ..bridge.agenda import search_agenda
from ..bridge.configuration import project_request
from ..bridge.contracts import BridgeBudget, BridgeError, BridgeFailure
from ..bridge.project import resolve_project
from ..bridge.resources import CancellationToken, current_process_rss
from ..bridge.symbolic import SymbolicProtocolError, search_evidence
from ..bridge.workspace import project_inputs
from ..budget import SearchBudget
from ..contracts import ProverResult, Status, TaskSpec, task_identity
from ..kernel.p0 import AgdaBridgeError, open_kernel_session
from ..kernel.protocol import KernelSessionFactory
from ..nnue import NNUEModel
from ..observability.policy_trace import validated_proof_evidence
from ..offline import assert_offline_configuration
from ..project import choose_goal, choose_goal_prefix, require_agda_source_file
from ..ranking.bundled import FOCUSED_MODEL, OR_MODEL
from ..reconstruction import reconstruct_native_batch
from ..resource_budget import ResourceLimitError, ResourceScope
from ..validation import ValidationError, validate_reconstruction
from ..verifier_budget import VerifierCallLimitExceeded, VerifierCallScope
from .native_receipts import NativeReceipts


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
    ) -> ProverResult:
        return self._prove(
            task,
            session_factory=session_factory,
            cancellation=cancellation,
            prefix=True,
        )

    def _prove(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None,
        prefix: bool,
    ) -> ProverResult:
        started = time.monotonic()
        source = task.source_file.resolve()
        result = ProverResult(
            "",
            "internal-error",
            str(source),
            "",
            task.ranker,
            policy_profile=f"native-{self.controller}-v1",
        )
        scope = ResourceScope(task.resources, memory_sample=current_process_rss)
        calls = VerifierCallScope()
        value_error_status: Status = "invalid-task"
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
            if task.max_depth is not None:
                raise ValueError(
                    "native search does not yet implement an explicit legacy max_depth"
                )
            if task.action_model_path is not None:
                raise ValueError(
                    "native search does not yet consume the legacy refinement model; "
                    "use policy_model for an OR-decision model"
                )
            if prefix and self.controller != "agenda":
                raise ValueError(
                    "the evidence-only controller does not implement joint solving"
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
            model_path = None
            focused_model_path = None
            if task.ranker == "nnue":
                policy_model = self.policy_model
                model_path = policy_model or OR_MODEL.path
                model = (
                    NNUEModel.load(
                        model_path,
                        expected_role="or-decision-ranking",
                        deadline=budget.deadline,
                    )
                    if policy_model
                    else OR_MODEL.load(deadline=budget.deadline)
                )
                result.action_model_id = model.model_id
                focused_model_path = task.model_path or FOCUSED_MODEL.path
                focused_model = (
                    NNUEModel.load(
                        focused_model_path,
                        expected_role="focused-search-branch-policy",
                        deadline=budget.deadline,
                    )
                    if task.model_path
                    else FOCUSED_MODEL.load(deadline=budget.deadline)
                )
                result.model_id = focused_model.model_id
            identity = task_identity(
                task,
                result.source_hash,
                mode=f"native-{self.controller}-{'prefix' if prefix else 'single'}",
                policy_profile=result.policy_profile,
                toolchain_id=result.toolchain_id,
                model_ids={"or": result.action_model_id, "focused": result.model_id},
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
                ranker=task.ranker,
                model_path=model_path,
                focused_model_path=focused_model_path,
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
                    ):
                        raise SymbolicProtocolError(
                            "native evidence uses unpinned models"
                        )
                    status = outcome.get("status")
                    if status == "paused" and outcome.get("reason") in {
                        "allowance-spent",
                        "action-allowance-spent",
                        "cancelled",
                    }:
                        raise ResourceLimitError(f"native search {outcome['reason']}")
                    if status in {"unsolved", "resource-exhausted"}:
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
                result.proof_term = result.patch = None
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
        return result


class NativeEvidenceEngine(NativeProofEngine):
    """Compatibility entry point for the first, finite evidence-only slice."""

    controller = "evidence"


class NativeAgendaEngine(NativeProofEngine):
    """Explicit opt-in autonomous controller; no Python symbolic callbacks."""
