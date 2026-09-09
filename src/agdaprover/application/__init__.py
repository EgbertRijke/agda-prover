"""Application use cases shared by every user-facing adapter."""

from .inspection import CommandResult, inspect_source
from .service import ProverApplication, default_application

__all__ = [
    "CommandResult",
    "ProverApplication",
    "default_application",
    "inspect_source",
]
