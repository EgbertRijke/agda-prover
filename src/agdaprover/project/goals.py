"""Deterministic goal and joint-prefix selection policies."""

from __future__ import annotations

from ..contracts import GoalInfo, TaskSpec


def choose_goal(
    goals: tuple[GoalInfo, ...],
    requested: int | None,
    position: int | None = None,
) -> GoalInfo:
    """Choose exactly one interaction goal for a single-goal operation."""

    if requested is not None and position is not None:
        raise ValueError("--goal and --goal-position are mutually exclusive")
    if requested is not None:
        for goal in goals:
            if goal.goal_id == requested:
                return goal
        raise ValueError(f"goal {requested} does not exist")
    if position is not None:
        for goal in goals:
            start, end = goal.source_range
            if start <= position < end:
                return goal
        raise ValueError(f"no goal contains source position {position}")
    if len(goals) != 1:
        raise ValueError(f"P0 requires exactly one goal, found {len(goals)}")
    return goals[0]


def choose_goal_prefix(
    goals: tuple[GoalInfo, ...], task: TaskSpec
) -> tuple[GoalInfo, tuple[GoalInfo, ...]]:
    """Select the source-ordered joint prefix through the requested cutoff.

    A cursor inside a hole selects that hole. A cursor elsewhere in the file,
    or an omitted selector, requests every open goal. Keeping this operation
    pure prevents command-line and editor prefix semantics from drifting.
    """

    ordered = tuple(sorted(goals, key=lambda goal: goal.source_range))
    if not ordered:
        raise ValueError("the source file has no open goals")
    if task.goal_id is not None and task.goal_position is not None:
        raise ValueError("--goal and --goal-position are mutually exclusive")
    if task.goal_id is not None:
        cutoff = next((goal for goal in ordered if goal.goal_id == task.goal_id), None)
        if cutoff is None:
            raise ValueError(f"goal {task.goal_id} does not exist")
    elif task.goal_position is not None:
        position = task.goal_position
        if position < 1:
            raise ValueError("goal position must be positive")
        cutoff = next(
            (
                goal
                for goal in ordered
                if goal.source_range[0] <= position < goal.source_range[1]
            ),
            None,
        )
        if cutoff is None:
            cutoff = ordered[-1]
    else:
        cutoff = ordered[-1]
    cutoff_index = ordered.index(cutoff)
    return cutoff, ordered[: cutoff_index + 1]


__all__ = ["choose_goal", "choose_goal_prefix"]
