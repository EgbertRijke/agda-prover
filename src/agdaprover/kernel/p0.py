"""Current P0 Agda adapter hidden behind the solver-facing kernel boundary."""

from ..bridge.compat_p0 import AgdaBridgeError, AgdaLoadError, AgdaSession

default_session_factory = AgdaSession

__all__ = [
    "AgdaBridgeError",
    "AgdaLoadError",
    "AgdaSession",
    "default_session_factory",
]
