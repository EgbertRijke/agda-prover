"""Versioned one-step refinement actions for the P0 interactive prover."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal

from .contracts import GoalInfo
from .type_syntax import normalize_type_text, result_head, top_level_arrow_count

ACTION_SCHEMA_VERSION = "agdaprover.action.p0.v1"

RefinementTag = Literal[
    "introduce-lambda",
    "introduce-constructor",
    "select-constructor",
    "use-local",
    "reflexivity",
    "case-split",
]


def _normalized_type(value: str) -> str:
    return normalize_type_text(value)


def _result_head(value: str) -> str:
    try:
        return result_head(value)
    except ValueError:
        return "unknown"


def _arrow_count(value: str) -> int:
    try:
        return top_level_arrow_count(value)
    except ValueError:
        # Agda's pretty-printer can expose syntax outside the small P0 parser.
        # Keep such an action available, but rank it after structurally known
        # types and let Agda decide whether it applies.
        return 1_000_000


@dataclass(frozen=True)
class RefinementCandidate:
    """A closed set of expressions that may be passed to Agda's refine command."""

    tag: RefinementTag
    local_name: str | None = None
    local_type: str | None = None

    @staticmethod
    def introduce_lambda() -> RefinementCandidate:
        return RefinementCandidate("introduce-lambda")

    @staticmethod
    def use_local(name: str, type_text: str) -> RefinementCandidate:
        if not name:
            raise ValueError("a local refinement requires a name")
        return RefinementCandidate("use-local", local_name=name, local_type=type_text)

    @staticmethod
    def reflexivity() -> RefinementCandidate:
        """Decode the historical P0 action; active generators never call it."""

        return RefinementCandidate("reflexivity")

    @staticmethod
    def introduce_constructor() -> RefinementCandidate:
        return RefinementCandidate("introduce-constructor")

    @staticmethod
    def select_constructor(name: str) -> RefinementCandidate:
        if not name:
            raise ValueError("a constructor selection requires a name")
        return RefinementCandidate("select-constructor", local_name=name)

    @staticmethod
    def case_split(name: str, type_text: str) -> RefinementCandidate:
        if not name:
            raise ValueError("a case split requires a local name")
        return RefinementCandidate("case-split", local_name=name, local_type=type_text)

    @property
    def expression(self) -> str:
        if self.tag in {"introduce-lambda", "introduce-constructor"}:
            return ""
        if self.tag == "select-constructor" and self.local_name:
            return self.local_name
        if self.tag == "reflexivity":
            return "refl"
        if self.tag == "use-local" and self.local_name:
            return self.local_name
        if self.tag == "case-split" and self.local_name:
            return self.local_name
        raise ValueError(f"malformed refinement candidate: {self.tag}")

    def symbolic_key(self, goal: GoalInfo) -> tuple[int, int, str]:
        target = _normalized_type(goal.target)
        if self.tag == "reflexivity":
            return (8, 0, self.expression)
        if self.tag == "use-local":
            local_type = _normalized_type(self.local_type or "")
            if local_type == target:
                return (0, 1, self.expression)
            same_result = _result_head(local_type) == _result_head(target)
            return (
                2 if same_result else 4,
                _arrow_count(local_type),
                self.expression,
            )
        if self.tag == "introduce-lambda":
            return (1 if _arrow_count(target) else 8, 0, self.expression)
        if self.tag == "introduce-constructor":
            return (1 if not _arrow_count(target) else 8, 0, self.expression)
        if self.tag == "select-constructor":
            return (1 if not _arrow_count(target) else 8, 0, self.expression)
        if self.tag == "case-split":
            return (3, _arrow_count(self.local_type or ""), self.expression)
        raise ValueError(f"unsupported refinement tag: {self.tag}")

    def to_dict(self) -> dict[str, Any]:
        operands: dict[str, str] = {}
        if self.local_name is not None:
            operands["name"] = self.local_name
        if self.local_type is not None:
            operands["type"] = self.local_type
        return {
            "schema_version": ACTION_SCHEMA_VERSION,
            "tag": self.tag,
            "operands": operands,
            "expression": self.expression,
        }

    @staticmethod
    def from_dict(value: dict[str, Any]) -> RefinementCandidate:
        if value.get("schema_version") != ACTION_SCHEMA_VERSION:
            raise ValueError("unsupported action schema version")
        tag = value.get("tag")
        operands = value.get("operands", {})
        if not isinstance(operands, dict):
            raise ValueError("action operands must be an object")
        if tag == "introduce-lambda":
            return RefinementCandidate.introduce_lambda()
        if tag == "introduce-constructor":
            return RefinementCandidate.introduce_constructor()
        if tag == "select-constructor":
            return RefinementCandidate.select_constructor(str(operands.get("name", "")))
        if tag == "reflexivity":
            return RefinementCandidate.reflexivity()
        if tag == "use-local":
            return RefinementCandidate.use_local(
                str(operands.get("name", "")), str(operands.get("type", ""))
            )
        if tag == "case-split":
            return RefinementCandidate.case_split(
                str(operands.get("name", "")), str(operands.get("type", ""))
            )
        raise ValueError(f"unsupported refinement action tag: {tag!r}")


def generate_refinement_candidates(goal: GoalInfo) -> list[RefinementCandidate]:
    candidates: list[RefinementCandidate] = []
    candidates.extend(
        RefinementCandidate.use_local(entry.name, entry.type)
        for entry in goal.context
        if entry.in_scope and entry.name
    )
    if top_level_arrow_count(goal.target):
        candidates.append(RefinementCandidate.introduce_lambda())
    else:
        candidates.append(RefinementCandidate.introduce_constructor())
    candidates.extend(
        RefinementCandidate.case_split(entry.name, entry.type)
        for entry in goal.context
        if entry.in_scope and entry.name
    )
    return list(dict.fromkeys(candidates))


@dataclass(frozen=True)
class RefinementAttempt:
    candidate: RefinementCandidate
    outcome: Literal["accepted", "applicable", "invalid"]
    diagnostic: str = ""
    nnue_score: float | None = None
    preview: str | None = None
    generated_goals: tuple[dict[str, Any], ...] = ()

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate": self.candidate.to_dict(),
            "outcome": self.outcome,
            "diagnostic": self.diagnostic,
            "nnue_score": self.nnue_score,
            "preview": self.preview,
            "generated_goals": list(self.generated_goals),
        }


def action_result(
    candidate: RefinementCandidate,
    *,
    preview: str,
    generated_goals: tuple[dict[str, Any], ...],
    rank: int,
    nnue_score: float | None,
    source_edit: dict[str, Any] | None = None,
    reconstruction_validation: dict[str, Any] | None = None,
    elaboration_strategy: str = "Cmd_refine_or_intro",
    module_scope_id: str | None = None,
) -> dict[str, Any]:
    value = candidate.to_dict()
    value.update(
        {
            "applicability": "accepted-by-agda-refine",
            "expected_state_effect": {
                "closes_goal": not generated_goals,
                "subgoals": list(generated_goals),
            },
            "elaboration_strategy": elaboration_strategy,
            "cost_estimate": {
                "verifier_calls": 1 + int(reconstruction_validation is not None)
            },
            "provenance": {
                "generator": "p0-refinement-actions",
                "rank": rank,
                "nnue_score": nnue_score,
                "module_scope_id": module_scope_id,
            },
            "reconstruction_hint": preview,
            "source_edit": source_edit,
            "reconstruction_validation": reconstruction_validation,
        }
    )
    return value
