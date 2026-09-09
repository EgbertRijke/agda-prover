"""Version-neutral Stage 1 boundary around Agda's kernel services."""

from .contracts import (
    BRIDGE_SCHEMA_VERSION,
    BridgeBudget,
    BridgeCost,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    CapabilityManifest,
    CommandId,
    EnvironmentId,
    ModuleId,
    ProjectHandle,
    SourceRange,
    SourceRevision,
    StateToken,
)
from .session import ConformingKernelSession, KernelSessionV1

__all__ = [
    "BRIDGE_SCHEMA_VERSION",
    "BridgeBudget",
    "BridgeCost",
    "BridgeDiagnostic",
    "BridgeError",
    "BridgeFailure",
    "CapabilityManifest",
    "CommandId",
    "ConformingKernelSession",
    "EnvironmentId",
    "KernelSessionV1",
    "ModuleId",
    "ProjectHandle",
    "SourceRange",
    "SourceRevision",
    "StateToken",
]
