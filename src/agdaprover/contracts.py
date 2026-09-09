"""Versioned P0 contracts shared by the CLI, bridge, search, and trainer.

The compatibility counters on result objects are retained for the editor and
existing traces.  New code should use :class:`CostMetrics`, whose fields each
have one deliberately narrow unit.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Literal

from .module_scope import ModuleScope
from .resource_budget import ResourceLimits

SCHEMA_VERSION = "agdaprover.p0.v1"
Status = Literal[
    "verified",
    "impossible",
    "needs-clarification",
    "unsolved",
    "resource-exhausted",
    "invalid-task",
    "policy-rejected",
    "toolchain-error",
    "internal-error",
]
StepStatus = Literal[
    "accepted-step",
    "unsolved",
    "resource-exhausted",
    "invalid-task",
    "toolchain-error",
    "internal-error",
]


@dataclass(frozen=True)
class ContextEntry:
    name: str
    type: str
    in_scope: bool

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class GoalInfo:
    goal_id: int
    target: str
    context: tuple[ContextEntry, ...]
    source_range: tuple[int, int]
    module_scope: ModuleScope | None = None

    def to_dict(self) -> dict[str, Any]:
        result: dict[str, Any] = {
            "goal_id": self.goal_id,
            "target": self.target,
            "context": [entry.to_dict() for entry in self.context],
            "source_range": list(self.source_range),
        }
        if self.module_scope is not None:
            result["module_scope"] = self.module_scope.to_dict()
        return result


@dataclass(frozen=True)
class CandidateCheck:
    accepted: bool
    elaborated_term: str | None
    diagnostic: str
    events: tuple[dict[str, Any], ...]


@dataclass(frozen=True)
class RefinementCheck:
    accepted: bool
    preview: str | None
    generated_goals: tuple[dict[str, Any], ...]
    diagnostic: str
    events: tuple[dict[str, Any], ...]


@dataclass(frozen=True)
class CaseSplitCheck:
    accepted: bool
    clauses: tuple[str, ...]
    variant: str | None
    diagnostic: str
    events: tuple[dict[str, Any], ...]


@dataclass(frozen=True)
class TaskSpec:
    source_file: Path
    goal_id: int | None = None
    max_candidates: int = 500
    max_term_size: int = 8
    max_depth: int | None = None
    timeout_seconds: float | None = None
    ranker: Literal["symbolic", "nnue"] = "symbolic"
    model_path: Path | None = None
    action_model_path: Path | None = None
    goal_position: int | None = None
    offline: bool = True
    schema_version: str = SCHEMA_VERSION
    max_verifier_calls: int | None = None
    resources: ResourceLimits = field(default_factory=ResourceLimits)


@dataclass
class CostMetrics:
    """Additive work counters; every field counts exactly one kind of work."""

    actions_generated: int = 0
    actions_scored: int = 0
    actions_expanded: int = 0
    kernel_loads: int = 0
    goal_inspections: int = 0
    speculative_checks: int = 0
    candidate_terms_checked: int = 0
    refinement_checks: int = 0
    case_split_checks: int = 0
    fresh_validation_runs: int = 0
    model_batches: int = 0
    model_items_scored: int = 0
    generated_subgoals: int = 0
    source_bytes_materialized: int = 0
    source_bytes_written: int = 0
    kernel_load_elapsed_ms: float = 0.0

    def add(self, **increments: int | float) -> None:
        for name, increment in increments.items():
            if name not in self.__dataclass_fields__:
                raise ValueError(f"unknown cost field: {name}")
            if increment < 0:
                raise ValueError(f"cost increment cannot be negative: {name}")
            setattr(self, name, getattr(self, name) + increment)

    def to_dict(self) -> dict[str, int | float]:
        return asdict(self)


def task_identity(
    task: TaskSpec,
    source_hash: str,
    *,
    mode: str,
    policy_profile: str,
    toolchain_id: str | None,
    model_ids: dict[str, str | None],
) -> str:
    """Hash every P0 input that can affect a search or step outcome."""

    budget: dict[str, int | float | None] = {
        "max_candidates": task.max_candidates,
        "max_term_size": task.max_term_size,
        "max_depth": task.max_depth,
        "timeout_seconds": task.timeout_seconds,
    }
    if task.max_verifier_calls is not None:
        budget["max_verifier_calls"] = task.max_verifier_calls
    payload = {
        "schema_version": task.schema_version,
        "mode": mode,
        "source_file": str(task.source_file.resolve()),
        "source_hash": source_hash,
        "goal_id": task.goal_id,
        "goal_position": task.goal_position,
        "budget": budget,
        "resources": task.resources.to_dict(),
        "ranker": task.ranker,
        "model_paths": {
            "primary": str(task.model_path.resolve()) if task.model_path else None,
            "refinement": (
                str(task.action_model_path.resolve())
                if task.action_model_path
                else None
            ),
        },
        "models": model_ids,
        "policy_profile": policy_profile,
        "toolchain_id": toolchain_id,
        "offline": task.offline,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()[:20]


def search_budget_envelope(task: TaskSpec) -> dict[str, int | float | None]:
    """Replayable search limits, retaining the historical uncapped trace shape."""

    envelope: dict[str, int | float | None] = {
        "max_actions": task.max_candidates,
        "max_depth": task.max_depth,
        "timeout_seconds": task.timeout_seconds,
    }
    if task.max_verifier_calls is not None:
        envelope["max_verifier_calls"] = task.max_verifier_calls
    return envelope


@dataclass(frozen=True)
class CandidateAttempt:
    term: dict[str, Any]
    rendered: str
    outcome: Literal["accepted", "invalid", "budget-censored"]
    diagnostic: str = ""
    nnue_score: float | None = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ProverResult:
    task_id: str
    status: Status
    source_file: str
    source_hash: str
    ranker: str
    goal: dict[str, Any] | None = None
    joint_goals: list[dict[str, Any]] = field(default_factory=list)
    proof_term: str | None = None
    patch: dict[str, Any] | None = None
    candidates_generated: int = 0
    verifier_calls: int = 0
    model_calls: int = 0
    model_elapsed_ms: float = 0.0
    elapsed_ms: float = 0.0
    attempts: list[CandidateAttempt] = field(default_factory=list)
    validation: dict[str, Any] | None = None
    trust_report: dict[str, Any] | None = None
    model_id: str | None = None
    action_model_id: str | None = None
    toolchain_id: str | None = None
    policy_profile: str = "p0-search-v2"
    cost: CostMetrics = field(default_factory=CostMetrics)
    impossibility_certificate: dict[str, Any] | None = None
    search_stats: dict[str, Any] | None = None
    policy_trace: list[dict[str, Any]] = field(default_factory=list)
    diagnostics: list[dict[str, str]] = field(default_factory=list)
    schema_version: str = SCHEMA_VERSION
    verifier_budget: dict[str, str | int] | None = None
    resource_budget: dict[str, Any] | None = None

    def to_dict(self, *, include_attempts: bool = False) -> dict[str, Any]:
        if self.status not in EXIT_CODES:
            raise ValueError(f"unsupported prover terminal status: {self.status!r}")
        if self.status == "verified" and not (
            self.proof_term
            and self.patch
            and self.validation
            and self.validation.get("checked")
            and self.trust_report
        ):
            raise ValueError("verified result lacks proof, patch, or clean validation")
        if self.status == "impossible" and not (
            self.impossibility_certificate
            and self.validation
            and self.validation.get("checked")
            and self.trust_report
        ):
            raise ValueError("impossible result lacks a checked certificate")
        result = asdict(self)
        if self.verifier_budget is None:
            result.pop("verifier_budget")
        if self.resource_budget is None:
            result.pop("resource_budget")
        if not include_attempts:
            result.pop("attempts", None)
            result.pop("policy_trace", None)
        return result


@dataclass
class StepResult:
    """Public one-step result contract, kept separate from the action IR."""

    task_id: str
    status: StepStatus
    source_file: str
    source_hash: str
    ranker: str
    goal: dict[str, Any] | None = None
    action: dict[str, Any] | None = None
    candidates_generated: int = 0
    verifier_calls: int = 0
    model_calls: int = 0
    model_elapsed_ms: float = 0.0
    elapsed_ms: float = 0.0
    model_id: str | None = None
    toolchain_id: str | None = None
    policy_profile: str = "p0-step-v2"
    cost: CostMetrics = field(default_factory=CostMetrics)
    attempts: list[Any] = field(default_factory=list)
    diagnostics: list[dict[str, str]] = field(default_factory=list)
    schema_version: str = "agdaprover.step.p0.v1"
    verifier_budget: dict[str, str | int] | None = None
    resource_budget: dict[str, Any] | None = None

    def to_dict(self, *, include_attempts: bool = False) -> dict[str, Any]:
        allowed = {
            "accepted-step",
            "unsolved",
            "resource-exhausted",
            "invalid-task",
            "toolchain-error",
            "internal-error",
        }
        if self.status not in allowed:
            raise ValueError(f"unsupported step terminal status: {self.status!r}")
        if self.status == "accepted-step" and self.action is None:
            raise ValueError("accepted-step result lacks an action")
        value = {
            "schema_version": self.schema_version,
            "task_id": self.task_id,
            "status": self.status,
            "source_file": self.source_file,
            "source_hash": self.source_hash,
            "ranker": self.ranker,
            "goal": self.goal,
            "action": self.action,
            "candidates_generated": self.candidates_generated,
            "verifier_calls": self.verifier_calls,
            "model_calls": self.model_calls,
            "model_elapsed_ms": self.model_elapsed_ms,
            "elapsed_ms": self.elapsed_ms,
            "model_id": self.model_id,
            "toolchain_id": self.toolchain_id,
            "policy_profile": self.policy_profile,
            "cost": self.cost.to_dict(),
            "diagnostics": self.diagnostics,
        }
        if self.verifier_budget is not None:
            value["verifier_budget"] = self.verifier_budget
        if self.resource_budget is not None:
            value["resource_budget"] = self.resource_budget
        if include_attempts:
            value["attempts"] = [attempt.to_dict() for attempt in self.attempts]
        return value


EXIT_CODES: dict[Status, int] = {
    "verified": 0,
    # Both outcomes mean that no proof was produced.  The JSON status retains
    # the logical distinction without changing the stable P0 shell interface.
    "impossible": 2,
    "unsolved": 2,
    "needs-clarification": 3,
    "invalid-task": 4,
    "policy-rejected": 5,
    "resource-exhausted": 6,
    "toolchain-error": 7,
    "internal-error": 8,
}
