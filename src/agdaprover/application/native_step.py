"""Fresh partial-source acceptance for one native transition, not search policy."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from ..bridge.symbolic import SymbolicProtocolError
from ..contracts import GoalInfo, TaskSpec
from ..reconstruction import reconstruct_native_step
from ..validation import validate_partial_reconstruction


@dataclass(frozen=True)
class NativeStepAttempt:
    action: dict[str, Any]
    outcome: str

    def to_dict(self) -> dict[str, Any]:
        return {"candidate": self.action, "outcome": self.outcome}


def accept_native_step(
    task: TaskSpec, goal: GoalInfo, entries: object, *, timeout_seconds: float
) -> dict[str, Any]:
    if (
        not isinstance(entries, list)
        or len(entries) != 1
        or not isinstance(entries[0], dict)
        or type(entries[0].get("goal_id")) is not int
        or entries[0]["goal_id"] != goal.goal_id
        or not isinstance(entries[0].get("source"), dict)
    ):
        raise SymbolicProtocolError(
            "native step export changed its selected source goal"
        )
    source = entries[0]["source"]
    edit = reconstruct_native_step(task.source_file.read_text(), goal, source)
    checked = validate_partial_reconstruction(
        task.source_file,
        edit,
        timeout_seconds=timeout_seconds,
        project_configuration=task.project_configuration,
    )
    return {
        "schema_version": "agdaprover.native-step.v1",
        "tag": "native-refinement",
        "expression": source["body"],
        "applicability": "accepted-by-fresh-agda-load",
        "expected_state_effect": {
            "closes_goal": not checked["generated_goals"],
            "subgoals": checked["generated_goals"],
        },
        "elaboration_strategy": "native-typed-transition",
        "source_edit": edit,
        "reconstruction_hint": source["body"],
        "reconstruction_validation": checked,
        "complete_proof": False,
    }
