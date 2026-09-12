"""Native frontier presentation through the existing provisional editor schema."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from ..bridge.symbolic import SymbolicProtocolError
from ..contracts import GoalInfo
from ..principal_variation import joint_principal_variation
from ..reconstruction import reconstruct_native_completion


def native_principal_variation(
    outcome: dict[str, Any],
    *,
    task_id: str,
    source_file: Path,
    source_sha256: str,
    targets: tuple[GoalInfo, ...],
    original_source: str,
) -> dict[str, Any]:
    """Offer original-source edits, not claims of independent proof validity.

    Each export was reconstructed from the observed native branch. Unfinished
    descendants have no completion entry. Accepting even a complete-looking
    entry still goes through the existing independent fresh validator.
    """
    snapshot = outcome.get("snapshot")
    entries = outcome.get("entries")
    if not isinstance(snapshot, dict) or not isinstance(entries, list):
        raise SymbolicProtocolError("malformed native variation")
    size = snapshot.get("frontier_size")
    if type(size) is not int or size < 0:
        raise SymbolicProtocolError("invalid native frontier size")
    principal = snapshot.get("principal")
    priority: list[int] = []
    depth = 0
    if principal is not None:
        if not isinstance(principal, dict) or any(
            type(principal.get(field)) is not int or principal[field] < 0
            for field in ("priority", "depth")
        ):
            raise SymbolicProtocolError("invalid native frontier position")
        priority, depth = [principal["priority"]], principal["depth"]
        obligations = principal.get("pending")
        if not isinstance(obligations, dict):
            raise SymbolicProtocolError("invalid native frontier obligations")
        pending = obligations.get("goals")
        if not isinstance(pending, list) or any(
            type(g) is not int or g < 0 for g in pending
        ):
            raise SymbolicProtocolError("invalid native frontier obligations")
    goals = {goal.goal_id: goal for goal in targets}
    completed: set[int] = set()
    seen: set[int] = set()
    steps = []
    for entry in entries:
        if (
            not isinstance(entry, dict)
            or type(entry.get("goal_id")) is not int
            or entry["goal_id"] not in goals
            or entry["goal_id"] in seen
            or not isinstance(entry.get("source"), dict)
        ):
            raise SymbolicProtocolError("native variation changed its selected goals")
        if principal is None:
            raise SymbolicProtocolError("native variation has no source branch")
        goal = goals[entry["goal_id"]]
        seen.add(goal.goal_id)
        try:
            step = reconstruct_native_completion(original_source, goal, entry["source"])
        except ValueError:
            # A presentation unavailable under the lexical edit policy is not
            # an accepted goal, nor grounds to discard the native search queue.
            continue
        completed.add(goal.goal_id)
        steps.append(step)
    remaining = tuple(goal for goal in targets if goal.goal_id not in completed)
    # Raw pending interaction order is not the scheduled action order (new
    # children are appended by Agda). This snapshot does not expose the next
    # action's goal, so retain "unknown" instead of reporting a later source
    # goal while the native controller is still working on generated children.
    cost = snapshot.get("cost", {})
    expanded = cost.get("scheduler_steps", 0)
    if type(expanded) is not int or expanded < 0:
        raise SymbolicProtocolError("invalid native scheduling cost")
    return joint_principal_variation(
        task_id=task_id,
        source_file=source_file,
        source_sha256=source_sha256,
        target_goals=targets,
        remaining_goals=remaining,
        active_goal=None,
        priority=priority,
        depth=depth,
        steps=steps,
        states_expanded=expanded,
        frontier_size=size,
        original_source=original_source,
    )
