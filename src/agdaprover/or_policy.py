"""Typed, bounded policy routing for genuine solver OR decisions.

The symbolic engines own candidate generation and Agda owns applicability.
This module has only two responsibilities: expose a complete already-generated
candidate batch to a role-checked ranker, and retain enough conservative trace
data to train that ranker later.  A missing or malformed model therefore
changes neither the candidate set nor the symbolic fallback order.
"""

from __future__ import annotations

import math
import time
from collections.abc import Sequence
from dataclasses import dataclass

from agdaprover.observability.policy_trace import (
    POLICY_CANDIDATE_SCHEMA_VERSION,
    POLICY_DECISION_SCHEMA_VERSION,
    CandidateOutcome,
    DecisionFamily,
    PolicyCandidate,
    PolicyChoice,
    PolicyTraceRecorder,
)

from .contracts import GoalInfo
from .focused import Assumption, FocusedAction, TypeExpr
from .ranking.features import (
    hash_features,
    policy_state_feature_tokens,
)
from .ranking.focused_policy import FocusedPolicy
from .ranking.protocol import SparsePolicyRanker
from .reasoning.classifications import StructuralClassification
from .type_syntax import normalize_type_text, result_head, top_level_arrow_count


def _bucket(value: int, boundaries: tuple[int, ...]) -> str:
    for boundary in boundaries:
        if value <= boundary:
            return str(boundary)
    return "large"


def policy_candidate_feature_tokens(
    goal: GoalInfo, candidate: PolicyCandidate
) -> tuple[str, ...]:
    """Representation-neutral structural features for one action proposal."""

    normalized_goal = normalize_type_text(goal.target)
    normalized_type = normalize_type_text(candidate.type_text)
    try:
        local_arrows = top_level_arrow_count(candidate.type_text)
    except ValueError:
        local_arrows = 1_000_000
    try:
        local_head = result_head(candidate.type_text)
    except ValueError:
        local_head = "unknown"
    try:
        goal_head = result_head(goal.target)
    except ValueError:
        goal_head = "unknown"
    tokens = [
        f"policy-family:{candidate.family}",
        f"policy-action-tag:{candidate.tag}",
        f"policy-type-arrows:{_bucket(local_arrows, (0, 1, 2, 3, 5, 8))}",
        f"policy-result-head:{local_head}",
        f"policy-result-head-match:{local_head == goal_head}",
        f"policy-exact-type:{normalized_type == normalized_goal}",
        f"policy-expression-bytes:{_bucket(len(candidate.expression.encode('utf-8')), (4, 8, 16, 32, 64, 128))}",
        f"policy-symbolic-key-width:{_bucket(len(candidate.symbolic_key), (0, 1, 2, 4, 8))}",
    ]
    tokens.extend(
        f"policy-metadata:{name}={value}" for name, value in candidate.metadata
    )
    return tuple(tokens)


@dataclass(frozen=True)
class RankedPolicyBatch:
    candidates: tuple[PolicyCandidate, ...]
    decision_id: str | None


class ORPolicyRouter:
    """Central optional ranker for the solver's current OR-decision families."""

    def __init__(
        self,
        *,
        focused_model: SparsePolicyRanker | None = None,
        refinement_model: SparsePolicyRanker | None = None,
        recorder: PolicyTraceRecorder | None = None,
        budget_envelope: dict[str, int | float | None] | None = None,
        provenance: dict[str, object] | None = None,
    ) -> None:
        self.focused_policy = (
            FocusedPolicy(focused_model) if focused_model is not None else None
        )
        if refinement_model is not None:
            refinement_model.require_role("or-decision-ranking")
        self.refinement_model = refinement_model
        self.recorder = recorder or PolicyTraceRecorder()
        self.budget_envelope = dict(budget_envelope or {})
        self.provenance = dict(provenance or {})
        self.model_batches = 0
        self.model_items_scored = 0
        self.model_elapsed_ms = 0.0
        self.symbolic_fallbacks = 0
        self.unsupported_family_fallbacks = 0
        self.family_counts: dict[str, int] = {}
        self._latest: dict[DecisionFamily, tuple[str | None, dict[str, str]]] = {}
        self._latest_goals: dict[DecisionFamily, GoalInfo] = {}

    @staticmethod
    def _goal_state(
        goal: GoalInfo, classification: StructuralClassification
    ) -> dict[str, object]:
        return {
            "goal": goal.to_dict(),
            "module_scope_id": (
                goal.module_scope.scope_id if goal.module_scope is not None else None
            ),
            "structural_classification": classification.to_dict(),
        }

    def rank(
        self,
        goal: GoalInfo,
        candidates: tuple[PolicyCandidate, ...],
        *,
        classification: StructuralClassification | None = None,
        priority_tiers: tuple[int, ...] | None = None,
    ) -> RankedPolicyBatch:
        if priority_tiers is not None and (
            len(priority_tiers) != len(candidates)
            or any(type(tier) is not int or tier < 0 for tier in priority_tiers)
            or tuple(sorted(priority_tiers)) != priority_tiers
        ):
            raise ValueError(
                "policy priority tiers must follow the complete symbolic order"
            )
        if not candidates:
            return RankedPolicyBatch((), None)
        active_classification = classification or StructuralClassification()
        families = {candidate.family for candidate in candidates}
        if len(families) != 1:
            raise ValueError("one policy batch must contain one decision family")
        if len({candidate.candidate_id for candidate in candidates}) != len(candidates):
            raise ValueError("one policy batch cannot contain duplicate candidates")
        if len({candidate.expression for candidate in candidates}) != len(candidates):
            raise ValueError("policy candidate expressions must be unique in one batch")
        # Callers own the symbolic order, including any hard structural tiers.
        # Preserve it exactly when no matching model is available.
        symbolic = tuple(candidates)
        ordered = symbolic
        scores_by_id: dict[str, float] = {}
        family = symbolic[0].family
        self.family_counts[family] = self.family_counts.get(family, 0) + int(
            len(symbolic) > 1
        )
        model = self.refinement_model
        provenance = self.provenance
        if priority_tiers is not None:
            provenance = {
                **provenance,
                "ranking_policy": "structural-tiers-v1",
                "priority_tiers": list(priority_tiers),
            }
        if model is not None and not model.supports_policy_family(family):
            model = None
            if len(symbolic) > 1:
                self.symbolic_fallbacks += 1
                self.unsupported_family_fallbacks += 1
            provenance = {
                **provenance,
                "policy_fallback_reason": "unsupported-decision-family",
            }
        if model is not None and len(symbolic) > 1:
            started = time.monotonic()
            try:
                state_tokens = policy_state_feature_tokens(goal, active_classification)
                state_features = hash_features(state_tokens, model.input_size)
                accumulator = model.accumulator(state_features)
                scores = model.score_feature_batches(
                    accumulator,
                    tuple(
                        hash_features(
                            policy_candidate_feature_tokens(goal, candidate),
                            model.input_size,
                        )
                        for candidate in symbolic
                    ),
                )
                if not all(math.isfinite(score) for score in scores):
                    raise ValueError("policy returned a non-finite score")
                scores_by_id = {
                    candidate.candidate_id: float(score)
                    for candidate, score in zip(symbolic, scores, strict=True)
                }
                symbolic_position = {
                    candidate.candidate_id: index
                    for index, candidate in enumerate(symbolic)
                }
                ordered = tuple(
                    sorted(
                        symbolic,
                        key=lambda candidate: (
                            priority_tiers[symbolic_position[candidate.candidate_id]]
                            if priority_tiers is not None
                            else 0,
                            -scores_by_id[candidate.candidate_id],
                            symbolic_position[candidate.candidate_id],
                        ),
                    )
                )
                self.model_batches += 1
                self.model_items_scored += len(symbolic)
            except (ArithmeticError, ValueError):
                ordered = symbolic
                scores_by_id = {}
                self.symbolic_fallbacks += 1
            finally:
                self.model_elapsed_ms += (time.monotonic() - started) * 1000.0
        decision_id = self.recorder.record(
            family=family,
            state=self._goal_state(goal, active_classification),
            candidates=symbolic,
            symbolic_order=tuple(item.candidate_id for item in symbolic),
            model_order=tuple(item.candidate_id for item in ordered),
            model_scores=scores_by_id,
            model_id=model.model_id if model is not None else None,
            budget_envelope=self.budget_envelope,
            provenance=provenance,
        )
        self._latest[family] = (
            decision_id,
            {candidate.expression: candidate.candidate_id for candidate in symbolic},
        )
        self._latest_goals[family] = goal
        return RankedPolicyBatch(ordered, decision_id)

    def snapshot_choices(
        self, family: DecisionFamily, goal: GoalInfo
    ) -> dict[str, PolicyChoice]:
        """Capture immediately after ranking, before descending into children."""

        if self._latest_goals.get(family) != goal:
            return {}
        decision_id, candidates = self._latest.get(family, (None, {}))
        if decision_id is None:
            return {}
        return {
            expression: PolicyChoice(decision_id, candidate_id)
            for expression, candidate_id in candidates.items()
        }

    def mark(
        self,
        family: DecisionFamily,
        expression: str,
        *,
        outcome: CandidateOutcome | None = None,
    ) -> None:
        """Record an explored candidate without inventing a success label."""

        latest = self._latest.get(family)
        if latest is None:
            return
        decision_id, candidates = latest
        candidate_id = candidates.get(expression)
        if candidate_id is not None:
            self.recorder.mark(decision_id, candidate_id, outcome=outcome)

    def score_focused(
        self,
        goal: TypeExpr,
        assumptions: tuple[Assumption, ...],
        actions: Sequence[FocusedAction],
    ) -> list[float]:
        if self.focused_policy is None:
            raise ValueError("focused NNUE policy is unavailable")
        scores = self.focused_policy.score_actions(goal, assumptions, actions)
        candidates = tuple(
            policy_candidate(
                family="focused-hypothesis",
                tag="focus-assumption",
                expression=(
                    action.assumption.local_name
                    or f"assumption[{action.assumption.order}]"
                ),
                type_text=action.assumption.type_expr.canonical(),
                symbolic_key=action.symbolic_key,
                metadata=(("domains", str(len(action.domains))),),
            )
            for action in actions
        )
        if candidates:
            score_by_id = {
                candidate.candidate_id: float(score)
                for candidate, score in zip(candidates, scores, strict=True)
            }
            symbolic_position = {
                candidate.candidate_id: index
                for index, candidate in enumerate(candidates)
            }
            ordered = tuple(
                sorted(
                    candidates,
                    key=lambda candidate: (
                        -score_by_id[candidate.candidate_id],
                        symbolic_position[candidate.candidate_id],
                    ),
                )
            )
            decision_id = self.recorder.record(
                family="focused-hypothesis",
                state={
                    "goal_type": goal.canonical(),
                    "module_scope_id": self.provenance.get("module_scope_id"),
                    "assumptions": [
                        {
                            "order": assumption.order,
                            "type": assumption.type_expr.canonical(),
                        }
                        for assumption in assumptions
                    ],
                },
                candidates=candidates,
                symbolic_order=tuple(item.candidate_id for item in candidates),
                model_order=tuple(item.candidate_id for item in ordered),
                model_scores=score_by_id,
                model_id=self.focused_policy.model.model_id,
                budget_envelope=self.budget_envelope,
                provenance=self.provenance,
            )
            self.family_counts["focused-hypothesis"] = self.family_counts.get(
                "focused-hypothesis", 0
            ) + int(len(candidates) > 1)
            self._latest["focused-hypothesis"] = (
                decision_id,
                {
                    candidate.expression: candidate.candidate_id
                    for candidate in candidates
                },
            )
        return scores

    def metrics(self) -> dict[str, object]:
        result: dict[str, object] = {
            "model_batches": self.model_batches,
            "model_items_scored": self.model_items_scored,
            "model_elapsed_ms": self.model_elapsed_ms,
            "symbolic_fallbacks": self.symbolic_fallbacks,
            "unsupported_family_fallbacks": self.unsupported_family_fallbacks,
            "decision_families": dict(sorted(self.family_counts.items())),
            "trace_decisions": self.recorder.recorded_decisions,
            "trace_decisions_omitted": self.recorder.omitted,
            "trace_retention": self.recorder.metrics(),
        }
        if self.focused_policy is not None:
            result["focused_accumulator"] = self.focused_policy.metrics()
        return result


def policy_candidate(
    *,
    family: DecisionFamily,
    tag: str,
    expression: str,
    type_text: str,
    symbolic_key: tuple[object, ...],
    metadata: tuple[tuple[str, str], ...] = (),
) -> PolicyCandidate:
    """Normalize heterogeneous symbolic keys at the typed policy boundary."""

    return PolicyCandidate(
        family=family,
        tag=tag,
        expression=expression,
        type_text=type_text or "unknown",
        symbolic_key=tuple(str(item) for item in symbolic_key),
        metadata=tuple(sorted(metadata)),
    )


__all__ = [
    "CandidateOutcome",
    "DecisionFamily",
    "ORPolicyRouter",
    "POLICY_CANDIDATE_SCHEMA_VERSION",
    "POLICY_DECISION_SCHEMA_VERSION",
    "PolicyCandidate",
    "PolicyTraceRecorder",
    "RankedPolicyBatch",
    "policy_candidate",
    "policy_candidate_feature_tokens",
]
