"""Common proposal envelope for deterministic symbolic action providers.

Providers enumerate possible actions; rankers may reorder them and Agda alone
decides applicability. The envelope gives search, tracing, and future native
generators one boundary without adding dispatch inside provider hot loops.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Protocol, TypeVar

from ..actions import RefinementCandidate, generate_refinement_candidates
from ..contracts import GoalInfo

PayloadT = TypeVar("PayloadT", covariant=True)


@dataclass(frozen=True)
class ActionProposal(Generic[PayloadT]):
    """One provider-owned candidate before ranking or kernel checking."""

    family: str
    expression: str
    symbolic_key: tuple[object, ...]
    payload: PayloadT


@dataclass(frozen=True)
class ProposalBatch(Generic[PayloadT]):
    """A deterministic candidate sequence from exactly one provider call."""

    provider_id: str
    proposals: tuple[ActionProposal[PayloadT], ...]

    def __post_init__(self) -> None:
        if not self.provider_id or len(self.provider_id.encode()) > 256:
            raise ValueError("proposal provider id must be bounded nonempty text")
        if any(not proposal.family for proposal in self.proposals):
            raise ValueError("every action proposal requires a family")

    @property
    def payloads(self) -> tuple[PayloadT, ...]:
        return tuple(proposal.payload for proposal in self.proposals)


class ActionProvider(Protocol[PayloadT]):
    @property
    def provider_id(self) -> str: ...

    def propose(self, goal: GoalInfo) -> ProposalBatch[PayloadT]: ...


@dataclass(frozen=True)
class RefinementActionProvider:
    """Adapter for the current deterministic one-step action generator."""

    provider_id: str = "p0-refinement-actions-v1"

    def propose(self, goal: GoalInfo) -> ProposalBatch[RefinementCandidate]:
        candidates = generate_refinement_candidates(goal)
        return ProposalBatch(
            self.provider_id,
            tuple(
                ActionProposal(
                    family="one-step-refinement",
                    expression=candidate.expression,
                    symbolic_key=candidate.symbolic_key(goal),
                    payload=candidate,
                )
                for candidate in candidates
            ),
        )


refinement_action_provider = RefinementActionProvider()
