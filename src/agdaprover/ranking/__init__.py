"""Replaceable ranking contracts.

Runtime model loading lives in :mod:`agdaprover.ranking.runtime` so importing
the protocol never imports the concrete NNUE implementation.
"""

from .protocol import (
    ModelRole,
    ProofTermRanker,
    SparsePolicyRanker,
    StepActionRanker,
)

__all__ = [
    "ModelRole",
    "ProofTermRanker",
    "SparsePolicyRanker",
    "StepActionRanker",
]
