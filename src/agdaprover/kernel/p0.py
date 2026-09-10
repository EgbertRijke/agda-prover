"""Current P0 Agda adapter hidden behind the solver-facing kernel boundary."""

from contextlib import AbstractContextManager

from ..bridge.compat_p0 import AgdaBridgeError, AgdaLoadError, AgdaSession
from ..bridge.workspace import ProjectInputs
from ..project_configuration import ProjectConfiguration
from .protocol import KernelSession, KernelSessionFactory

default_session_factory = AgdaSession


def session_project_inputs(session: KernelSession) -> ProjectInputs | None:
    observe = getattr(session, "project_inputs", None)
    return observe() if callable(observe) else None


def open_kernel_session(
    factory: KernelSessionFactory,
    *,
    timeout_seconds: float,
    deadline: float | None = None,
    project_configuration: ProjectConfiguration | None = None,
) -> AbstractContextManager[KernelSession]:
    """Keep legacy injected factories usable for unconfigured tasks."""
    if project_configuration is None:
        return factory(timeout_seconds=timeout_seconds, deadline=deadline)
    return factory(
        timeout_seconds=timeout_seconds,
        deadline=deadline,
        project_configuration=project_configuration,
    )


__all__ = [
    "AgdaBridgeError",
    "AgdaLoadError",
    "AgdaSession",
    "default_session_factory",
    "open_kernel_session",
    "session_project_inputs",
    "ProjectInputs",
]
