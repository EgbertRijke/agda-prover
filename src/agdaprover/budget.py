"""One shared wall/action budget for a P0 controller invocation."""

from __future__ import annotations

import math
import time
from collections.abc import Callable
from dataclasses import dataclass, field

from .resource_budget import checkpoint

Clock = Callable[[], float]


def action_limit_view(allowance: float) -> int | None:
    """Encode an internal unbounded allowance as null, never JSON Infinity.

    Finite allowances retain integer arithmetic. Infinity is only the absence
    of an action bound, not a replacement numeric ceiling or a work counter.
    The result also has the intended semantics as an itertools.islice stop.
    """

    if allowance == math.inf:
        return None
    if not math.isfinite(allowance) or allowance < 0:
        raise ValueError("action allowance must be nonnegative or unbounded")
    return int(allowance)


@dataclass
class SearchBudget:
    """Small concrete budget object; no work is hidden behind this boundary."""

    action_limit: int | None
    timeout_seconds: float | None
    clock: Clock = time.monotonic
    started_at: float | None = None
    started: float = field(init=False)
    actions_used: int = 0

    def __post_init__(self) -> None:
        if self.action_limit is not None and (
            type(self.action_limit) is not int or self.action_limit <= 0
        ):
            raise ValueError("action budget must be null or a positive integer")
        if self.timeout_seconds is not None and (
            not math.isfinite(self.timeout_seconds) or self.timeout_seconds <= 0
        ):
            raise ValueError("wall-time budget must be null or finite and positive")
        self.started = self.clock() if self.started_at is None else self.started_at

    @property
    def deadline(self) -> float:
        if self.timeout_seconds is None:
            return math.inf
        return self.started + self.timeout_seconds

    def remaining_seconds(self) -> float:
        checkpoint()
        return max(0.0, self.deadline - self.clock())

    def remaining_actions(self) -> float:
        checkpoint()
        return (
            math.inf
            if self.action_limit is None
            else max(0, self.action_limit - self.actions_used)
        )

    def wall_exhausted(self) -> bool:
        checkpoint()
        return self.clock() >= self.deadline

    def exhausted(self) -> bool:
        return self.wall_exhausted() or (
            self.action_limit is not None and self.actions_used >= self.action_limit
        )

    def charge_action(self, count: int = 1) -> bool:
        if count < 0:
            raise ValueError("action charge cannot be negative")
        if self.wall_exhausted() or count > self.remaining_actions():
            return False
        self.actions_used += count
        return True

    def account_actions(self, count: int) -> None:
        """Account work performed by a child given a pre-bounded allowance."""

        if count < 0 or count > self.remaining_actions():
            raise ValueError("child exceeded its assigned action budget")
        self.actions_used += count

    def require_time(self, operation: str) -> float:
        remaining = self.remaining_seconds()
        if remaining <= 0:
            raise TimeoutError(f"wall-time budget exhausted before {operation}")
        return remaining
