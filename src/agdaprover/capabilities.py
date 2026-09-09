"""Compatibility facade for the solver-facing kernel protocol.

New code imports :mod:`agdaprover.kernel.protocol`. This module remains for
the documented P0 transition window and external prototype callers.
"""

from .kernel.protocol import (
    CommittedProofAction,
    InternalObligationSession,
    KernelSession,
    KernelSessionFactory,
    PreciseSearchGoalSession,
    ScopeDeclarationSession,
    TermInferenceSession,
    TransactionalKernelSession,
)

__all__ = [
    "CommittedProofAction",
    "InternalObligationSession",
    "KernelSession",
    "KernelSessionFactory",
    "PreciseSearchGoalSession",
    "ScopeDeclarationSession",
    "TermInferenceSession",
    "TransactionalKernelSession",
]
