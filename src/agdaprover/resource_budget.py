"""Shared physical-resource envelopes, independent of search and Agda syntax.

An envelope measures effort and live capacity, never mathematical depth/size.
Controllers bind scopes; process owners publish cumulative samples under unique
leases; codecs and symbolic work poll checkpoints. Nested scopes cannot refund
work or reset an ancestor's allowance. Samples are explicitly not exact peaks.
"""

from __future__ import annotations

import math
import threading
import time
from collections.abc import Callable
from contextvars import ContextVar, Token
from dataclasses import asdict, dataclass
from types import TracebackType
from typing import Any

RESOURCE_SCHEMA = "agdaprover.resource-budget.v1"


class ResourceLimitError(RuntimeError):
    """An operational allowance, not a malformed task or logical failure."""


class ResourceExhausted(ResourceLimitError):
    def __init__(self, resource: str, used: float | int, limit: float | int):
        self.resource, self.used, self.limit = resource, used, limit
        super().__init__(f"{resource} budget exhausted ({used:g}/{limit:g})")


@dataclass(frozen=True)
class ResourceLimits:
    cpu_seconds: float | None = None
    memory_bytes: int = 4 * 1024**3
    io_bytes: int = 1024**3
    temporary_bytes: int = 1024**3

    def __post_init__(self) -> None:
        if self.cpu_seconds is not None and (
            isinstance(self.cpu_seconds, bool)
            or not isinstance(self.cpu_seconds, (int, float))
            or not math.isfinite(self.cpu_seconds)
            or self.cpu_seconds <= 0
        ):
            raise ValueError("CPU seconds must be null or finite and positive")
        for key in ("memory_bytes", "io_bytes", "temporary_bytes"):
            if type(getattr(self, key)) is not int or getattr(self, key) <= 0:
                raise ValueError(f"{key} must be a positive integer")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_version": RESOURCE_SCHEMA, **asdict(self)}

    @classmethod
    def from_dict(cls, value: object) -> ResourceLimits:
        if (
            not isinstance(value, dict)
            or set(value)
            != {
                "schema_version",
                "cpu_seconds",
                "memory_bytes",
                "io_bytes",
                "temporary_bytes",
            }
            or value["schema_version"] != RESOURCE_SCHEMA
        ):
            raise ValueError("invalid resource budget schema")
        return cls(
            **{key: item for key, item in value.items() if key != "schema_version"}
        )


class ResourceLedger:
    """Thread-safe additive CPU/I/O and simultaneous live memory/disk ledger."""

    def __init__(self, limits: ResourceLimits) -> None:
        self.limits = limits
        self._lock = threading.RLock()
        self.cpu_seconds = 0.0
        self.io_bytes = 0
        self.peak_rss_bytes = 0
        self.peak_temporary_bytes = 0
        self._cpu: dict[object, float] = {}
        self._rss: dict[object, int] = {}
        self._disk: dict[object, int] = {}
        self.exhaustion: ResourceExhausted | None = None

    def _check(self) -> None:
        if self.exhaustion is not None:
            raise self.exhaustion
        for kind, used, limit in (
            ("cpu-seconds", self.cpu_seconds, self.limits.cpu_seconds),
            ("resident-bytes", sum(self._rss.values()), self.limits.memory_bytes),
            ("io-bytes", self.io_bytes, self.limits.io_bytes),
            ("temporary-bytes", sum(self._disk.values()), self.limits.temporary_bytes),
        ):
            if limit is not None and used > limit:
                self.exhaustion = ResourceExhausted(kind, used, limit)
                raise self.exhaustion

    def sample(
        self,
        owner: object,
        *,
        cpu_seconds: float,
        rss_bytes: int = 0,
        temporary_bytes: int = 0,
    ) -> None:
        if (
            isinstance(cpu_seconds, bool)
            or not isinstance(cpu_seconds, (int, float))
            or not math.isfinite(cpu_seconds)
            or cpu_seconds < 0
            or type(rss_bytes) is not int
            or rss_bytes < 0
            or type(temporary_bytes) is not int
            or temporary_bytes < 0
        ):
            raise ValueError("resource samples must be finite and nonnegative")
        with self._lock:
            # A process disappearing between poll and sample can report zero.
            # Never subtract cumulative work. Every process generation has a
            # new owner; a restarted child cannot inherit a previous baseline.
            previous = self._cpu.get(owner, 0.0)
            self.cpu_seconds += max(0.0, cpu_seconds - previous)
            self._cpu[owner] = max(previous, cpu_seconds)
            self._rss[owner] = rss_bytes
            self._disk[owner] = temporary_bytes
            self.peak_rss_bytes = max(self.peak_rss_bytes, sum(self._rss.values()))
            self.peak_temporary_bytes = max(
                self.peak_temporary_bytes, sum(self._disk.values())
            )
            self._check()

    def release(self, owner: object) -> None:
        with self._lock:
            self._rss.pop(owner, None)
            self._disk.pop(owner, None)
            self._cpu.pop(owner, None)
            # CPU remains charged in the aggregate after a child exits. Owners
            # are leases, never reused; retired sampling state needn't grow.

    def charge_io(self, count: int) -> None:
        if type(count) is not int or count < 0:
            raise ValueError("I/O charge must be a nonnegative integer")
        with self._lock:
            self.io_bytes += count
            self._check()

    def report(self) -> dict[str, Any]:
        with self._lock:
            return {
                "schema_version": RESOURCE_SCHEMA,
                "limits": self.limits.to_dict(),
                "cpu_seconds": self.cpu_seconds,
                "io_bytes": self.io_bytes,
                "peak_sampled_rss_bytes": self.peak_rss_bytes,
                "peak_sampled_temporary_bytes": self.peak_temporary_bytes,
                "exhausted_resource": self.exhaustion.resource
                if self.exhaustion
                else None,
                "accounting": "sampled-owned-processes-and-caller-thread-v1",
            }


_scopes: ContextVar[tuple[ResourceScope, ...]] = ContextVar(
    "resource_scopes", default=()
)


def current_ledgers() -> tuple[ResourceLedger, ...]:
    return tuple(scope.ledger for scope in _scopes.get())


def checkpoint() -> None:
    errors = []
    for scope in _scopes.get():
        try:
            scope.checkpoint()
        except ResourceLimitError as error:
            errors.append(error)
    if errors:
        raise errors[0]


def charge_io(count: int) -> None:
    errors = []
    for ledger in current_ledgers():
        try:
            ledger.charge_io(count)
        except ResourceExhausted as error:
            errors.append(error)
    if errors:
        raise errors[0]


class ResourceScope:
    def __init__(
        self, limits: ResourceLimits, *, memory_sample: Callable[[], int] | None = None
    ) -> None:
        self.ledger = ResourceLedger(limits)
        self.memory_sample = memory_sample
        self._token: Token[tuple[ResourceScope, ...]] | None = None
        self._opened = False
        self._started_cpu = time.thread_time()
        self._thread = threading.get_ident()
        self._last_sample = -math.inf
        self._owner = object()
        self._storage: set[StorageLease] = set()

    def open(self) -> None:
        if self._opened:
            raise RuntimeError("resource scopes cannot be reopened")
        self._opened = True
        self._started_cpu = time.thread_time()
        self._thread = threading.get_ident()
        self._token = _scopes.set((*_scopes.get(), self))

    def __enter__(self) -> ResourceScope:
        self.open()
        return self

    def __exit__(
        self,
        kind: type[BaseException] | None,
        error: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        exhausted = self.finish()
        if exhausted is not None and error is None:
            raise exhausted

    def checkpoint(self, *, force: bool = False) -> None:
        if self._token is None:
            return
        if self.ledger.exhaustion and not force:
            raise self.ledger.exhaustion
        # The invoking thread is counted here; child process samples have
        # separate owners. A monitoring thread must not reset this CPU clock.
        if threading.get_ident() != self._thread:
            return
        now = time.monotonic()
        if force or now - self._last_sample >= 0.05:
            self._last_sample = now
            errors: list[ResourceLimitError] = []
            for storage in tuple(self._storage):
                try:
                    storage.sample(force=force)
                except ResourceExhausted as error:
                    errors.append(error)
            rss = 0
            try:
                rss = self.memory_sample() if self.memory_sample else 0
            except ResourceLimitError as error:
                errors.append(error)
            try:
                self.ledger.sample(
                    self._owner,
                    cpu_seconds=time.thread_time() - self._started_cpu,
                    rss_bytes=rss,
                )
            except ResourceExhausted as error:
                errors.append(error)
            if errors:
                raise errors[0]

    def close(self) -> None:
        if self._token is not None:
            _scopes.reset(self._token)
            self._token = None
        self.ledger.release(self._owner)
        for storage in self._storage:
            self.ledger.release(storage)
        self._storage.clear()

    def finish(self) -> ResourceLimitError | None:
        """Account the last CPU interval before a controller publishes a result."""
        if self._token is None:
            return self.ledger.exhaustion
        try:
            self.checkpoint(force=True)
        except ResourceLimitError as error:
            return error
        finally:
            self.close()
        return None


class StorageLease:
    """One owned temporary area's live bytes, shared across enclosing scopes.

    The owner supplies an exact filesystem meter and closes the lease when the
    area is removed. Checkpoints sample it while processes/codecs do their work.
    No mathematical property or filesystem naming convention enters allocation.
    """

    def __init__(self, meter: Callable[[], int]) -> None:
        self._scopes = _scopes.get()
        self._meter = meter
        self._sampled_at = -math.inf
        self._closed = False
        for scope in self._scopes:
            scope._storage.add(self)

    def sample(self, *, force: bool = False) -> None:
        if self._closed or not self._scopes:
            return
        now = time.monotonic()
        if not force and now - self._sampled_at < 0.05:
            return
        self._sampled_at = now
        used = self._meter()
        errors = []
        for scope in self._scopes:
            if self not in scope._storage:
                continue
            try:
                scope.ledger.sample(self, cpu_seconds=0, temporary_bytes=used)
            except ResourceExhausted as error:
                errors.append(error)
        if errors:
            raise errors[0]

    def close(self) -> None:
        if self._closed:
            return
        try:
            self.sample(force=True)
        except ResourceExhausted:
            # Sticky exhaustion is surfaced by the controller's final check;
            # releasing one lease must not interrupt cleanup of its siblings.
            pass
        finally:
            self._closed = True
            for scope in self._scopes:
                scope._storage.discard(self)
                scope.ledger.release(self)

    def __enter__(self) -> StorageLease:
        return self

    def __exit__(self, *error: object) -> None:
        self.close()
