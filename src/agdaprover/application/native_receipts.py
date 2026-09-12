"""Native progress/cost provenance at the application boundary, not search policy."""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any

from ..bridge.contracts import MAX_DIAGNOSTIC_BYTES
from ..bridge.symbolic import SymbolicProtocolError
from ..contracts import ProverResult, StepResult


def reconstruction_failure(outcome: dict[str, Any]) -> str:
    """Describe a rejected export without serializing its proof payload again."""
    fields = ["native source export"]
    for key in ("status", "reason"):
        value = outcome.get(key)
        if isinstance(value, str):
            fields.append(value[:MAX_DIAGNOSTIC_BYTES])
    pending = outcome.get("pending")
    if isinstance(pending, dict):
        goals = pending.get("goals")
        if isinstance(goals, list):
            fields.append(f"open goals={len(goals)}")
        for key in ("metas", "constraints"):
            value = pending.get(key)
            if type(value) is int and value >= 0:
                fields.append(f"{key}={value}")
    detail = outcome.get("detail")
    if isinstance(detail, str):
        fields.append(detail[:MAX_DIAGNOSTIC_BYTES])
    # This existing presentation limit never truncates proof terms or search.
    message = "; ".join(fields).encode("utf-8")
    if len(message) > MAX_DIAGNOSTIC_BYTES:
        suffix = b" [diagnostic truncated]"
        message = message[: MAX_DIAGNOSTIC_BYTES - len(suffix)]
        return message.decode("utf-8", errors="ignore") + suffix.decode()
    return message.decode("utf-8")


@dataclass
class NativeReceipts:
    result: ProverResult | StepResult
    trace_bytes: int
    retained_bytes: int = 0
    omitted: int = 0

    def models(self) -> dict[str, str]:
        primary_role = (self.result.search_stats or {}).get(
            "primary_model_role", "focused-search-branch-policy"
        )
        return {
            role: identity
            for role, identity in (
                ("or-decision-ranking", self.result.action_model_id),
                (primary_role, self.result.model_id),
            )
            if role is not None and identity is not None
        }

    def publish(self, event: dict[str, Any]) -> None:
        result = self.result
        stats = result.search_stats = dict(result.search_stats or {})
        kind = event["event"]
        if kind == "operation-start":
            stats.update(native_dispatch=event, completion_known=False)
        if kind == "operation-result":
            stats.update(completion_known=True, native_session_cost=event["cost"])
            outcome = event["outcome"]
            cost = outcome.get("search_cost", outcome.get("cost"))
            if cost is not None:
                self.cost(cost)
            if result.policy_profile in {"native-agenda-v1", "native-step-v1"}:
                # Export/reconstruction is checked too, after the last advance.
                result.cost.speculative_checks = event["cost"]["checking_attempts"]
                result.cost.case_split_checks = event["cost"]["clause_queries"]
        trace = event.get("trace") if kind == "search-policy" else event.get("payload")
        if isinstance(trace, dict) and "model_items_scored" in trace:
            role = trace.get("role")
            if role not in {
                "proof-term-ranking",
                "one-step-refinement-ranking",
                "focused-search-branch-policy",
                "or-decision-ranking",
            }:
                raise SymbolicProtocolError("native trace has an unknown model role")
            expected_model = self.models().get(str(role))
            identity = trace.get("model_id")
            if identity not in {None, expected_model} or (
                trace.get("model_items_scored", 0) > 0
                and (expected_model is None or identity != expected_model)
            ):
                raise SymbolicProtocolError("native trace uses an unpinned NNUE")
            result.model_calls += trace.get("model_items_scored", 0)
            result.cost.model_items_scored = result.cost.actions_scored = (
                result.model_calls
            )
            result.model_elapsed_ms += trace.get("model_elapsed_ns", 0) / 1e6
            size = len(json.dumps(trace).encode())
            if size <= self.trace_bytes - self.retained_bytes:
                result.policy_trace.append(trace)
                self.retained_bytes += size
            else:
                self.omitted += 1
            stats["policy_decisions_omitted"] = self.omitted

    def cost(self, cost: dict[str, Any]) -> None:
        result = self.result
        schema = cost.get("schema_version")
        if schema == "agdaprover.symbolic-agenda-cost.v1":
            expected = self.models()
            if cost.get("models") != expected:
                raise SymbolicProtocolError(
                    "native agenda uses unpinned model identities"
                )
            result.cost.actions_expanded = cost["actions_attempted"]
            result.candidates_generated = result.cost.actions_generated = cost[
                "actions_generated"
            ]
            physical = cost["session_cost"]
            result.cost.speculative_checks = physical["checking_attempts"]
            result.cost.case_split_checks = physical["clause_queries"]
        elif schema == "agdaprover.symbolic-evidence-cost.v2":
            result.cost.speculative_checks = sum(
                cost.get(key, 0)
                for key in (
                    "inference_queries",
                    "checker_queries",
                    "recursive_context_queries",
                )
            )
            result.cost.candidate_terms_checked = cost.get("checker_queries", 0)
            result.candidates_generated = result.cost.actions_generated = sum(
                cost.get(key, 0)
                for key in (
                    "application_proposals",
                    "lambda_proposals",
                    "record_proposals",
                    "absurd_proposals",
                    "recursive_proposals",
                    "focused_candidates",
                    "algebra_candidates",
                )
            )
            result.cost.actions_expanded = (
                cost.get("nodes", 0)
                + cost.get("focused_nodes", 0)
                + cost.get("algebra_actions", 0)
            )
        else:
            raise SymbolicProtocolError("unsupported native search cost schema")
        result.model_calls = result.cost.actions_scored = (
            result.cost.model_items_scored
        ) = cost["model_items_scored"]
        result.model_elapsed_ms = cost["model_elapsed_ns"] / 1e6
        assert result.search_stats is not None
        result.search_stats.update(
            cost, final_search_cost=cost, policy_decisions_omitted=self.omitted
        )
