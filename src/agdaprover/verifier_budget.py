"""Invocation-local accounting and optional quotas for physical verifier requests.

The bridge charges immediately before interaction writes or fresh checker
launches. Nested scopes charge every enclosing quota atomically. Context copies
share the same counters; a future threaded scheduler must propagate that context
explicitly. This module owns no processes, search policy, or acceptance decisions.
"""

from __future__ import annotations

from contextvars import ContextVar, Token
from dataclasses import dataclass
from threading import Lock
from typing import Literal

VERIFIER_BUDGET_SCHEMA = "agdaprover.verifier-budget.v2"
LEGACY_VERIFIER_BUDGET_SCHEMA = "agdaprover.verifier-budget.v1"
VerifierRequest = Literal["interaction", "fresh-validation"]


class VerifierCallLimitExceeded(RuntimeError):
    """Run-global exhaustion, deliberately distinct from recoverable timeouts."""


@dataclass
class _Meter:
    limit: int | None
    interaction_commands: int = 0
    fresh_validations: int = 0
    denied_calls: int = 0
    fresh_validation_runs: int = 0

    @property
    def used(self) -> int:
        return self.interaction_commands + self.fresh_validations


_meters: ContextVar[tuple[_Meter, ...]] = ContextVar("verifier_budgets", default=())
_charge_lock = Lock()


def charge_verifier_request(kind: VerifierRequest) -> None:
    """Reserve one call before performing it; failures do not refund work."""

    if kind not in {"interaction", "fresh-validation"}:
        raise ValueError(f"unknown verifier request kind: {kind}")
    meters = _meters.get()
    if not meters:
        return
    with _charge_lock:
        for index, meter in enumerate(meters):
            if meter.limit is not None and meter.used >= meter.limit:
                # A child's smaller allowance does not exhaust its parent;
                # an exhausted ancestor does prevent every descendant's work.
                for affected in meters[index:]:
                    affected.denied_calls += 1
                raise VerifierCallLimitExceeded(
                    f"verifier-call budget exhausted before {kind} "
                    f"({meter.used}/{meter.limit} physical requests)"
                )
        for meter in meters:
            if kind == "interaction":
                meter.interaction_commands += 1
            else:
                meter.fresh_validations += 1


def record_fresh_validation_start() -> None:
    """Observe a successful launch, separately from its already reserved request.

    This is called by the checker boundary, before any supervision can interrupt
    the run. Failed launches retain their request charge but are not runs.
    Recording work neither polls resources nor confers proof acceptance.
    """
    with _charge_lock:
        for meter in _meters.get():
            meter.fresh_validation_runs += 1


class VerifierCallScope:
    """Always observe work; bind an optional cap and restore the caller on exit."""

    def __init__(self) -> None:
        self._meter: _Meter | None = None
        self._token: Token[tuple[_Meter, ...]] | None = None

    def open(self, limit: int | None) -> None:
        if self._token is not None:
            raise RuntimeError("verifier budget scope is already open")
        self._meter = None
        if limit is not None and (type(limit) is not int or limit <= 0):
            raise ValueError("max_verifier_calls must be null or a positive integer")
        self._meter = _Meter(limit)
        self._token = _meters.set((*_meters.get(), self._meter))

    def close(self) -> None:
        if self._token is not None:
            _meters.reset(self._token)
            self._token = None

    @property
    def fresh_validation_runs(self) -> int:
        with _charge_lock:
            return self._meter.fresh_validation_runs if self._meter is not None else 0

    def report(self) -> dict[str, str | int | None] | None:
        meter = self._meter
        if meter is None:
            return None
        with _charge_lock:
            return {
                "schema_version": VERIFIER_BUDGET_SCHEMA,
                "limit": meter.limit,
                "used": meter.used,
                "interaction_commands": meter.interaction_commands,
                "fresh_validations": meter.fresh_validations,
                "denied_calls": meter.denied_calls,
            }
