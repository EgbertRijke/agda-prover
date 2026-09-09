"""Registry of exact Agda interaction protocol adapters."""

from __future__ import annotations

from functools import lru_cache

from ..contracts import (
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    DiagnosticPhase,
)
from ..version_matrix import load_version_matrix
from .agda_2_8 import Agda28Adapter


@lru_cache(maxsize=8)
def adapter_for_version(version: str) -> Agda28Adapter:
    """Select and validate one immutable adapter per process/version epoch."""

    row = load_version_matrix().get(version)
    if row is not None and row.adapter == Agda28Adapter.name:
        adapter = Agda28Adapter()
        capabilities = adapter.capabilities()
        if capabilities.operations != row.operations:
            raise BridgeError(
                BridgeFailure.INTERNAL_INVARIANT,
                BridgeDiagnostic(
                    code="toolchain-capability-drift",
                    phase=DiagnosticPhase.TOOLCHAIN,
                    severity="error",
                    message="runtime capabilities differ from the toolchain matrix",
                ),
            )
        return adapter
    raise BridgeError(
        BridgeFailure.TOOLCHAIN_ERROR,
        BridgeDiagnostic(
            code="unsupported-agda-version",
            phase=DiagnosticPhase.TOOLCHAIN,
            severity="error",
            message=(
                f"unsupported Agda version {version!r}; install exactly "
                f"{Agda28Adapter.version} for Stage 1"
            ),
        ),
    )


__all__ = ["Agda28Adapter", "adapter_for_version"]
