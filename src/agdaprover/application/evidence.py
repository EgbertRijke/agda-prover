"""Opt-in Haskell evidence path through the existing application trust boundary.

Only setup/inspection and final validation use the Python kernel API. Every
intermediate application, argument choice and rollback stays inside Haskell.
Full structural/joint engine selection remains a later qualification milestone.
"""

from __future__ import annotations

import hashlib
import json
import time
from dataclasses import dataclass
from pathlib import Path

from ..artifacts import executable_sha256, file_sha256
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
from ..project import choose_goal, require_agda_source_file
from ..ranking.bundled import OR_MODEL
from ..reconstruction import reconstruct_hole_completion
from ..resource_budget import ResourceLimitError, ResourceScope
from ..validation import validate_reconstruction
from ..verifier_budget import VerifierCallLimitExceeded, VerifierCallScope


@dataclass(frozen=True)
class NativeEvidenceEngine:
    executable: Path
    work_units: int | None = None
    policy_model: Path | None = None
    native_scorer: Path | None = None
    trace_bytes: int = 16 * 1024 * 1024

    def prove(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        cancellation: CancellationToken | None = None,
    ) -> ProverResult:
        started = time.monotonic()
        source = task.source_file.resolve()
        result = ProverResult(
            "",
            "internal-error",
            str(source),
            "",
            task.ranker,
            policy_profile="native-evidence-v1",
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
            assert_offline_configuration(task, deadline=budget.deadline)
            require_agda_source_file(source)
            result.source_hash = file_sha256(source, deadline=budget.deadline)
            project, _ = resolve_project(
                project_request(source, task.project_configuration),
                BridgeBudget.for_run(budget.require_time("project resolution")),
            )
            inputs = project_inputs(project)
            result.toolchain_id = project.toolchain.executable_sha256[:20]
            binary_hash = executable_sha256(
                str(self.executable), deadline=budget.deadline
            )
            result.search_stats = {
                "algorithm": "native-evidence-v1",
                "engine": "haskell",
                "native_executable_sha256": binary_hash,
            }
            model_path = None
            if task.ranker == "nnue":
                model_path = self.policy_model or OR_MODEL.path
                model = (
                    NNUEModel.load(
                        model_path,
                        expected_role="or-decision-ranking",
                        deadline=budget.deadline,
                    )
                    if self.policy_model
                    else OR_MODEL.load(deadline=budget.deadline)
                )
                result.action_model_id = model.model_id
            identity = task_identity(
                task,
                result.source_hash,
                mode="native-evidence",
                policy_profile=result.policy_profile,
                toolchain_id=result.toolchain_id,
                model_ids={"or": result.action_model_id},
                project_inputs_id=inputs.identity,
            )
            result.task_id = hashlib.sha256(
                json.dumps([identity, binary_hash, self.work_units]).encode()
            ).hexdigest()
            with open_kernel_session(
                session_factory,
                timeout_seconds=budget.require_time("goal inspection"),
                deadline=budget.deadline,
                project_configuration=task.project_configuration,
            ) as session:
                goals = session.load_module(source)
                goal = session.inspect_goal(
                    choose_goal(goals, task.goal_id, task.goal_position)
                )
            result.goal = goal.to_dict()
            result.cost.kernel_loads = 1
            result.cost.goal_inspections = 1
            value_error_status = "internal-error"
            inputs.assert_current(deadline=budget.deadline)
            trace_size = 0
            omitted = 0

            def publish(event: dict) -> None:
                nonlocal trace_size, omitted
                if event["event"] == "operation-start":
                    result.search_stats = {
                        **(result.search_stats or {}),
                        "algorithm": "native-evidence-v1",
                        "native_dispatch": event,
                        "completion_known": False,
                        "final_search_cost": None,
                    }
                if event["event"] == "search-policy":
                    trace = event["trace"]
                    if trace.get("model_id") not in {None, result.action_model_id}:
                        raise SymbolicProtocolError(
                            "native trace uses an unpinned NNUE"
                        )
                    result.model_calls += trace.get("model_items_scored", 0)
                    result.cost.model_items_scored = result.model_calls
                    result.model_elapsed_ms += trace.get("model_elapsed_ns", 0) / 1e6
                    size = len(json.dumps(trace).encode())
                    if size <= self.trace_bytes - trace_size:
                        result.policy_trace.append(trace)
                        trace_size += size
                    else:
                        omitted += 1

            reply = search_evidence(
                self.executable,
                project,
                goal.goal_id,
                budget=BridgeBudget.for_run(
                    budget.require_time("native evidence search")
                ),
                work_units=self.work_units,
                ranker=task.ranker,
                model_path=model_path,
                native_path=self.native_scorer,
                cancellation=cancellation or CancellationToken(),
                publish=publish,
            )
            inputs.assert_current(deadline=budget.deadline)
            if (
                executable_sha256(str(self.executable), deadline=budget.deadline)
                != binary_hash
            ):
                raise SymbolicProtocolError("native executable changed during search")
            outcome = reply["outcome"]
            stats = outcome.get("search_cost", {})
            result.search_stats = {
                **(result.search_stats or {}),
                "algorithm": "native-evidence-v1",
                **stats,
                "completion_known": True,
                "final_search_cost": stats,
                "native_session_cost": reply["cost"],
                "policy_decisions_omitted": omitted,
            }
            result.model_calls = result.cost.actions_scored = (
                result.cost.model_items_scored
            ) = stats.get("model_items_scored", 0)
            result.model_elapsed_ms = stats.get("model_elapsed_ns", 0) / 1e6
            result.cost.kernel_loads += 1
            result.cost.speculative_checks = stats.get("work_units", 0)
            result.cost.candidate_terms_checked = stats.get("checker_queries", 0)
            result.candidates_generated = result.cost.actions_generated = stats.get(
                "application_proposals", 0
            ) + stats.get("lambda_proposals", 0)
            if "failure" in outcome:
                raise SymbolicProtocolError(str(outcome["failure"]))
            if outcome.get("model_id") != result.action_model_id:
                raise SymbolicProtocolError("native model differs from the pinned NNUE")
            if outcome.get("status") in {"unsolved", "resource-exhausted"}:
                result.status = outcome["status"]
                return result
            if outcome.get("status") != "candidate":
                raise SymbolicProtocolError(f"invalid native search outcome: {outcome}")
            candidate = outcome["candidate"]
            if candidate.get("status") not in {"apparently-closed", "accepted-partial"}:
                result.status = "unsolved"
                result.diagnostics.append(
                    {
                        "kind": "search",
                        "message": "native candidate retains internal obligations",
                    }
                )
                return result
            display = candidate["evidence"]["display"]
            patch = reconstruct_hole_completion(source.read_text(), goal, display)
            validation, trust = validate_reconstruction(
                source,
                patch,
                agda_executable=str(project.toolchain.executable),
                agda_version=project.toolchain.version,
                timeout_seconds=budget.require_time("fresh native proof validation"),
                project_configuration=task.project_configuration,
                expected_inputs=inputs,
            )
            result.validation, result.trust_report = validation, trust
            if validation["checked"]:
                result.proof_term, result.patch, result.status = (
                    display,
                    patch,
                    "verified",
                )
                witness = validated_proof_evidence(
                    task_id=result.task_id,
                    source_sha256=result.source_hash,
                    patch=patch,
                    validation=validation,
                    trust_report=trust,
                )
                if witness is not None:
                    # Native traces remain a separate versioned format. Credit
                    # only selected edges and bind them to fresh checking; do
                    # not mislabel these as legacy training examples.
                    result.search_stats["validated_native_choices"] = {
                        "choices": outcome["selected_choices"],
                        "evidence": witness,
                    }
            else:
                result.status = (
                    "resource-exhausted" if validation["timed_out"] else "unsolved"
                )
                result.diagnostics.append(
                    {
                        "kind": "validation-rejection",
                        "message": validation.get(
                            "diagnostic", "fresh validation rejected candidate"
                        ),
                    }
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
        except (OSError, ValueError, SymbolicProtocolError, AgdaBridgeError) as error:
            result.status = (
                "internal-error"
                if isinstance(error, SymbolicProtocolError)
                else value_error_status
                if isinstance(error, ValueError)
                else "toolchain-error"
            )
            result.diagnostics.append(
                {"kind": "native-evidence", "message": str(error)}
            )
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
