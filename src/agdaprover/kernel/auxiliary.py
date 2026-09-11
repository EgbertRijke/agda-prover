"""One serial speculative worker, never a final proof validator.

Each lease has independently prepared source/configuration inputs. Optional
project rebinding invalidates old proof state; only the kernel owns import
reuse. Unsupported factories keep their ordinary throwaway lifecycle.
"""

from __future__ import annotations

import math
import os
import threading
import time
from collections.abc import Iterator
from contextlib import ExitStack, contextmanager
from pathlib import Path
from types import TracebackType

from ..contracts import GoalInfo
from ..project_configuration import ProjectConfiguration
from ..resource_budget import ResourceLimitError
from ..verifier_budget import VerifierCallLimitExceeded
from .p0 import open_kernel_session
from .protocol import KernelSession, KernelSessionFactory, ProjectRevisionSession


def load_kernel_project(
    session: KernelSession,
    source: Path,
    configuration: ProjectConfiguration | None,
) -> tuple[GoalInfo, ...]:
    if isinstance(session, ProjectRevisionSession):
        return session.load_project(source, configuration)
    return session.load_module(source)


class AuxiliarySessions:
    """Invocation-owned, bounded to one idle auxiliary session.

    The caller must finish using a session inside its lease; tokens and queries
    cannot escape into later probes. Nested/concurrent leases are rejected.
    Exceptions discard the worker; cancellation and resource refusal take
    precedence over recoverable cleanup/probe errors. Budgets are invocation-wide
    and never renewed when the worker is reused.
    """

    def __init__(
        self,
        factory: KernelSessionFactory,
        *,
        deadline: float,
        reuse: bool | None = None,
    ) -> None:
        if math.isnan(deadline):
            raise ValueError("auxiliary checking deadline must not be NaN")
        self._factory = factory
        self._deadline = deadline
        self._reuse = (
            os.environ.get("AGDAPROVER_REUSE_AUXILIARY_SESSION") == "1"
            if reuse is None
            else reuse
        )
        self._owner = ExitStack()
        self._session: KernelSession | None = None
        self._lock = threading.Lock()
        self._closed = False

    def __enter__(self) -> AuxiliarySessions:
        if self._closed:
            raise RuntimeError("auxiliary sessions are closed")
        return self

    def __exit__(
        self,
        _kind: type[BaseException] | None,
        _error: BaseException | None,
        _traceback: TracebackType | None,
    ) -> None:
        if not self._lock.acquire(blocking=False):
            raise RuntimeError("cannot close a leased auxiliary session")
        try:
            self._closed = True
            self._discard(_error)
        finally:
            self._lock.release()

    def _discard(self, error: BaseException | None = None) -> None:
        self._session = None
        try:
            self._owner.close()
        except BaseException as cleanup_error:
            resource_errors = (
                ResourceLimitError,
                VerifierCallLimitExceeded,
                TimeoutError,
            )
            if (
                error is None
                or not isinstance(cleanup_error, Exception)
                or (
                    isinstance(cleanup_error, resource_errors)
                    and isinstance(error, Exception)
                    and not isinstance(error, resource_errors)
                )
            ):
                raise
            # Cleanup must not turn cancellation or a resource refusal into a
            # recoverable load failure. Do not include possibly private paths.
            error.add_note(
                f"auxiliary session cleanup also raised {type(cleanup_error).__name__}"
            )

    @contextmanager
    def open(
        self, *, project_configuration: ProjectConfiguration | None
    ) -> Iterator[KernelSession]:
        if not self._lock.acquire(blocking=False):
            raise RuntimeError("auxiliary session leases must be serial")
        try:
            if self._closed:
                raise RuntimeError("auxiliary sessions are closed")
            remaining = self._deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("auxiliary checking deadline exhausted")
            if self._session is None:
                self._session = self._owner.enter_context(
                    open_kernel_session(
                        self._factory,
                        timeout_seconds=remaining,
                        deadline=self._deadline,
                        project_configuration=project_configuration,
                    )
                )
            yield self._session
            if not self._reuse or not isinstance(self._session, ProjectRevisionSession):
                self._discard()
        except BaseException as error:
            self._discard(error)
            raise
        finally:
            self._lock.release()
