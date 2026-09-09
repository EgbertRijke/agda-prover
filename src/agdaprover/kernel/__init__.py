"""Solver-facing kernel boundary.

Only this package may expose concrete Agda bridge adapters to proof-search
code. The protocol remains version-neutral; :mod:`agdaprover.kernel.p0` is
the temporary compatibility composition root for the current prototype.
"""

from .protocol import (
    CommittedProofAction,
    InternalObligationSession,
    KernelSession,
    KernelSessionFactory,
    PreciseSearchGoalSession,
    ScopeDeclarationSession,
    ScopedRetrievalSession,
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
    "ScopedRetrievalSession",
    "TermInferenceSession",
    "TransactionalKernelSession",
]
