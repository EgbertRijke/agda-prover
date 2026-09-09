"""Deprecated P0 import facade.

New production code imports :mod:`agdaprover.bridge`; this module remains for
one compatibility window for external prototype users.
"""

from .bridge.compat_p0 import (
    SUPPORTED_AGDA_VERSION,
    AgdaBridgeError,
    AgdaLoadError,
    AgdaSession,
)

__all__ = [
    "SUPPORTED_AGDA_VERSION",
    "AgdaBridgeError",
    "AgdaLoadError",
    "AgdaSession",
]
