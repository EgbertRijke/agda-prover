"""Structured goal inspection application operation.

This is deliberately outside the CLI: editor, daemon, and command-line
adapters must observe identical selection and bridge failure semantics.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ..bridge.configuration import project_request
from ..bridge.contracts import BridgeBudget, BridgeError, BridgeFailure
from ..bridge.session import ConformingKernelSession
from ..project import analyze_module_scope
from ..project_configuration import ProjectConfiguration
from ..resource_budget import ResourceLimitError


@dataclass(frozen=True)
class CommandResult:
    """One adapter-neutral operation result and its stable process exit code."""

    exit_code: int
    payload: dict[str, Any]


def inspect_source(
    source: Path,
    *,
    goal_id: int | None = None,
    goal_position: int | None = None,
    timeout_seconds: float | None = None,
    project_configuration: ProjectConfiguration | None = None,
) -> CommandResult:
    """Inspect selected goals through the conforming bridge."""

    try:
        wall = timeout_seconds if timeout_seconds is not None else float("inf")
        if wall <= 0:
            raise ValueError("timeout must be positive")
        budget = BridgeBudget.for_run(wall)
        with ConformingKernelSession() as session:
            opened = session.open_project(
                project_request(source, project_configuration), budget
            )
            loaded = session.load_module(
                opened.project,
                opened.root_module,
                opened.source_revision,
                budget,
            )
            state_token = loaded.transition.child_state
            if state_token is None:
                raise RuntimeError("successful module load returned no state token")
            inspected_state = session.inspect_goals(state_token, budget).state
            selected = inspected_state.goals
            if goal_id is not None:
                selected = tuple(
                    goal for goal in selected if goal.interaction_id.value == goal_id
                )
                if not selected:
                    raise ValueError(f"goal {goal_id} does not exist")
            elif goal_position is not None:
                selected = tuple(
                    goal
                    for goal in selected
                    if goal.source_range.start <= goal_position < goal.source_range.end
                )
                if not selected:
                    raise ValueError(
                        f"no goal contains source position {goal_position}"
                    )
            inspected_source = source.read_text()
            inspected = [
                {
                    "goal_id": goal.interaction_id.value,
                    "target": goal.target.text,
                    "context": [
                        {
                            "name": binder.suggested_name,
                            "type": binder.type.text,
                            "in_scope": binder.in_scope,
                        }
                        for binder in goal.telescope
                    ],
                    "source_range": [goal.source_range.start, goal.source_range.end],
                    "module_scope": analyze_module_scope(
                        inspected_source,
                        max(0, goal.source_range.start - 1),
                        source,
                    ).to_dict(),
                }
                for goal in selected
            ]
            payload = {
                "schema_version": "agdaprover.p0.v1",
                "bridge_schema_version": "agdaprover.bridge.v1",
                "environment_id": opened.environment_id.value,
                "source_revision": opened.source_revision.value,
                "project": opened.project.to_dict(),
                "module": opened.root_module.to_dict(),
                "capabilities": opened.capabilities.to_dict(),
                "state_token": state_token.to_dict(),
                "proof_state_hash": inspected_state.structural_hash,
                "proof_state": inspected_state.to_dict(),
                "goals": inspected,
            }
        return CommandResult(0, payload)
    except ResourceLimitError as error:
        return CommandResult(
            6, {"status": "resource-exhausted", "diagnostic": str(error)}
        )
    except ValueError as error:
        return CommandResult(4, {"status": "invalid-task", "diagnostic": str(error)})
    except BridgeError as error:
        exit_code = (
            4
            if error.failure
            in {BridgeFailure.INVALID_REQUEST, BridgeFailure.LOAD_FAILURE}
            else 6
            if error.failure
            in {
                BridgeFailure.TIMEOUT,
                BridgeFailure.CANCELLED,
                BridgeFailure.RESOURCE_EXHAUSTED,
            }
            else 7
        )
        return CommandResult(
            exit_code,
            {
                "status": (
                    "invalid-task"
                    if exit_code == 4
                    else "resource-exhausted"
                    if exit_code == 6
                    else "toolchain-error"
                ),
                "diagnostic": error.diagnostic.message,
                "diagnostics": [error.diagnostic.to_dict()],
            },
        )
