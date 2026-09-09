"""Hot-path ranking ports implemented by NNUE or future local rankers."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import Literal, Protocol, TypeAlias

from ..actions import RefinementCandidate
from ..contracts import GoalInfo
from ..terms import Term

ModelRole: TypeAlias = Literal[
    "proof-term-ranking",
    "one-step-refinement-ranking",
    "focused-search-branch-policy",
    "or-decision-ranking",
]


class ProofTermRanker(Protocol):
    model_id: str

    def score_terms(self, goal: GoalInfo, terms: Sequence[Term]) -> list[float]: ...


class StepActionRanker(Protocol):
    model_id: str

    def score_refinement_actions(
        self, goal: GoalInfo, candidates: Sequence[RefinementCandidate]
    ) -> list[float]: ...


class SparsePolicyRanker(Protocol):
    """Sparse accumulator operations used by focused and shared OR policies."""

    role: ModelRole
    model_id: str
    input_size: int

    def require_role(self, expected: ModelRole) -> None: ...

    def accumulator(self, features: Mapping[int, float]) -> list[float]: ...

    def update_accumulator(
        self,
        accumulator: list[float],
        *,
        add: Mapping[int, float] | None = None,
        remove: Mapping[int, float] | None = None,
    ) -> list[float]: ...

    def score_feature_batches(
        self,
        base_accumulator: list[float],
        feature_batches: Sequence[Mapping[int, float]],
    ) -> list[float]: ...


__all__ = [
    "ModelRole",
    "ProofTermRanker",
    "SparsePolicyRanker",
    "StepActionRanker",
]
