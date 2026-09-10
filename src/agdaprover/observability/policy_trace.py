"""Versioned, bounded observability records for solver OR decisions."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Literal, cast

POLICY_DECISION_SCHEMA_VERSION = "agdaprover.policy-decision.v1"
POLICY_CANDIDATE_SCHEMA_VERSION = "agdaprover.policy-candidate.v1"

DecisionFamily = Literal[
    "focused-hypothesis",
    "constructor-choice",
    "case-variable",
    "visible-premise",
    "recursive-call",
]
CandidateOutcome = Literal[
    "invalid",
    "valid-unproductive",
    "budget-censored",
    "dominated",
    "unsafe",
    "on-validated-proof",
]

_MAX_TRACE_DECISIONS = 4096
_MAX_CANDIDATES_PER_DECISION = 256
_MAX_TEXT_BYTES = 1 << 20


def _bounded_text(value: str, label: str) -> str:
    if not value or len(value.encode("utf-8")) > _MAX_TEXT_BYTES:
        raise ValueError(f"{label} must be nonempty bounded text")
    return value


def _stable_hash(value: object) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def validated_proof_evidence(
    *,
    task_id: str,
    source_sha256: str,
    patch: object,
    validation: dict[str, object] | None,
    trust_report: dict[str, object] | None,
) -> dict[str, object] | None:
    """Bind trace credit to an independently checked result, never a preview."""

    if (
        not patch
        or not validation
        or not trust_report
        or validation.get("checked") is not True
        or validation.get("fresh_process") is not True
        or validation.get("timed_out") is not False
        or type(validation.get("exit_status")) is not int
        or validation.get("exit_status") != 0
        or trust_report.get("fresh_process") is not True
        or trust_report.get("offline") is not True
        or type(trust_report.get("checker_exit_status")) is not int
        or trust_report.get("checker_exit_status") != 0
    ):
        return None
    return {
        "schema_version": "agdaprover.validated-policy-proof.v1",
        "task_id": task_id,
        "source_sha256": source_sha256,
        "patch_sha256": _stable_hash(patch),
        "validation_sha256": _stable_hash(validation),
        "trust_report_sha256": _stable_hash(trust_report),
    }


@dataclass(frozen=True)
class PolicyChoice:
    """Exact OR provenance carried by a proposed proof, not proof authority."""

    decision_id: str
    candidate_id: str


@dataclass(frozen=True)
class PolicyCandidate:
    """One already-generated action offered at a genuine OR boundary."""

    family: DecisionFamily
    tag: str
    expression: str
    type_text: str = "unknown"
    symbolic_key: tuple[str, ...] = ()
    metadata: tuple[tuple[str, str], ...] = ()
    schema_version: str = POLICY_CANDIDATE_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != POLICY_CANDIDATE_SCHEMA_VERSION:
            raise ValueError("unsupported policy-candidate schema")
        if self.family not in {
            "focused-hypothesis",
            "constructor-choice",
            "case-variable",
            "visible-premise",
            "recursive-call",
        }:
            raise ValueError("unsupported policy decision family")
        _bounded_text(self.tag, "policy candidate tag")
        _bounded_text(self.expression, "policy candidate expression")
        _bounded_text(self.type_text, "policy candidate type")
        if len(self.symbolic_key) > 32 or any(
            len(item.encode("utf-8")) > 4096 for item in self.symbolic_key
        ):
            raise ValueError("policy candidate symbolic key is malformed")
        if (
            len(self.metadata) > 32
            or tuple(sorted(self.metadata)) != self.metadata
            or len({name for name, _value in self.metadata}) != len(self.metadata)
        ):
            raise ValueError("policy candidate metadata must be sorted and unique")
        for name, value in self.metadata:
            _bounded_text(name, "policy metadata name")
            _bounded_text(value, "policy metadata value")

    def semantic_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "family": self.family,
            "tag": self.tag,
            "expression": self.expression,
            "type": self.type_text,
            "symbolic_key": list(self.symbolic_key),
            "metadata": {name: value for name, value in self.metadata},
        }

    @property
    def candidate_id(self) -> str:
        return _stable_hash(self.semantic_dict())

    def to_dict(self) -> dict[str, object]:
        value = self.semantic_dict()
        value["candidate_id"] = self.candidate_id
        return value

    @classmethod
    def from_dict(cls, value: object) -> PolicyCandidate:
        if not isinstance(value, dict) or set(value) != {
            "schema_version",
            "family",
            "tag",
            "expression",
            "type",
            "symbolic_key",
            "metadata",
            "candidate_id",
        }:
            raise ValueError("malformed policy candidate")
        symbolic_key = value["symbolic_key"]
        metadata = value["metadata"]
        if not isinstance(symbolic_key, list) or not all(
            isinstance(item, str) for item in symbolic_key
        ):
            raise ValueError("policy candidate symbolic key must be text")
        if not isinstance(metadata, dict) or not all(
            isinstance(name, str) and isinstance(item, str)
            for name, item in metadata.items()
        ):
            raise ValueError("policy candidate metadata must be text")
        for key in ("schema_version", "family", "tag", "expression", "type"):
            if not isinstance(value[key], str):
                raise ValueError("policy candidate fields must be text")
        candidate = cls(
            family=cast(DecisionFamily, value["family"]),
            tag=value["tag"],
            expression=value["expression"],
            type_text=value["type"],
            symbolic_key=tuple(symbolic_key),
            metadata=tuple(sorted(metadata.items())),
            schema_version=value["schema_version"],
        )
        if value["candidate_id"] != candidate.candidate_id:
            raise ValueError("policy candidate identity mismatch")
        return candidate


@dataclass
class _RecordedDecision:
    decision_id: str
    family: DecisionFamily
    state: dict[str, object]
    candidates: tuple[PolicyCandidate, ...]
    symbolic_order: tuple[str, ...]
    model_order: tuple[str, ...]
    model_scores: dict[str, float]
    model_id: str | None
    budget_envelope: dict[str, int | float | None]
    provenance: dict[str, object]
    outcomes: dict[str, CandidateOutcome] = field(default_factory=dict)
    explored: set[str] = field(default_factory=set)

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": POLICY_DECISION_SCHEMA_VERSION,
            "decision_id": self.decision_id,
            "family": self.family,
            "state": self.state,
            "candidate_set": [
                {
                    **candidate.to_dict(),
                    "model_score": self.model_scores.get(candidate.candidate_id),
                    "explored": candidate.candidate_id in self.explored,
                    "outcome": self.outcomes.get(
                        candidate.candidate_id, "budget-censored"
                    ),
                }
                for candidate in self.candidates
            ],
            "symbolic_order": list(self.symbolic_order),
            "model_order": list(self.model_order),
            "model_id": self.model_id,
            "budget_envelope": self.budget_envelope,
            "provenance": self.provenance,
            "label_policy": "unvisited-and-unfinished-branches-are-budget-censored",
            "kernel_authority": "agda",
        }


@dataclass
class PolicyTraceRecorder:
    """Bounded in-memory trace for later provenance-safe dataset extraction."""

    max_decisions: int = _MAX_TRACE_DECISIONS
    _decisions: list[_RecordedDecision] = field(default_factory=list, init=False)
    _by_id: dict[str, _RecordedDecision] = field(default_factory=dict, init=False)
    omitted: int = 0

    def __post_init__(self) -> None:
        if not 1 <= self.max_decisions <= _MAX_TRACE_DECISIONS:
            raise ValueError("policy trace capacity is outside its safety bound")

    def record(
        self,
        *,
        family: DecisionFamily,
        state: dict[str, object],
        candidates: tuple[PolicyCandidate, ...],
        symbolic_order: tuple[str, ...],
        model_order: tuple[str, ...],
        model_scores: dict[str, float],
        model_id: str | None,
        budget_envelope: dict[str, int | float | None],
        provenance: dict[str, object],
    ) -> str | None:
        if len(candidates) <= 1:
            return None
        if len(candidates) > _MAX_CANDIDATES_PER_DECISION:
            self.omitted += 1
            return None
        if len(self._decisions) >= self.max_decisions:
            self.omitted += 1
            return None
        payload = {
            "family": family,
            "state": state,
            "candidate_ids": [candidate.candidate_id for candidate in candidates],
            "ordinal": len(self._decisions),
        }
        decision_id = _stable_hash(payload)
        decision = _RecordedDecision(
            decision_id=decision_id,
            family=family,
            state=state,
            candidates=candidates,
            symbolic_order=symbolic_order,
            model_order=model_order,
            model_scores=model_scores,
            model_id=model_id,
            budget_envelope=dict(budget_envelope),
            provenance=dict(provenance),
        )
        self._decisions.append(decision)
        self._by_id[decision_id] = decision
        return decision_id

    def mark(
        self,
        decision_id: str | None,
        candidate_id: str,
        *,
        outcome: CandidateOutcome | None = None,
    ) -> None:
        if decision_id is None or (decision := self._by_id.get(decision_id)) is None:
            return
        if candidate_id not in {
            candidate.candidate_id for candidate in decision.candidates
        }:
            raise ValueError("policy outcome refers to a candidate outside its batch")
        decision.explored.add(candidate_id)
        if outcome is not None:
            decision.outcomes[candidate_id] = outcome

    def to_list(self) -> list[dict[str, object]]:
        return [decision.to_dict() for decision in self._decisions]

    def mark_validated_proof(
        self, choices: tuple[PolicyChoice, ...], *, evidence: dict[str, object]
    ) -> None:
        """Label only a selected proof's choices after external fresh validation.

        Validate the complete selection before mutating any record. Merely
        accepted refinements and choices on abandoned branches stay censored.
        """

        selected: dict[str, str] = {}
        for choice in choices:
            decision = self._by_id.get(choice.decision_id)
            if decision is None or choice.candidate_id not in decision.explored:
                raise ValueError("validated choice lacks recorded exploration")
            if decision.outcomes.get(choice.candidate_id) in {"invalid", "unsafe"}:
                raise ValueError("validated choice conflicts with kernel rejection")
            if any(
                candidate_id != choice.candidate_id and outcome == "on-validated-proof"
                for candidate_id, outcome in decision.outcomes.items()
            ):
                raise ValueError("decision already belongs to a different proof choice")
            if (
                selected.setdefault(choice.decision_id, choice.candidate_id)
                != choice.candidate_id
            ):
                raise ValueError("a proof selects conflicting arms of one decision")
        for decision_id, candidate_id in selected.items():
            decision = self._by_id[decision_id]
            decision.outcomes[candidate_id] = "on-validated-proof"
            decision.provenance = {
                **decision.provenance,
                "validated_result": dict(evidence),
            }


__all__ = [
    "CandidateOutcome",
    "DecisionFamily",
    "POLICY_CANDIDATE_SCHEMA_VERSION",
    "POLICY_DECISION_SCHEMA_VERSION",
    "PolicyCandidate",
    "PolicyChoice",
    "PolicyTraceRecorder",
    "validated_proof_evidence",
]
