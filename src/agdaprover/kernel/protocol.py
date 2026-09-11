"""Narrow structural interfaces between search and the Agda kernel gateway.

The search package depends on these capabilities rather than a transport,
Agda version, or compatibility implementation. Keeping this interface small
also makes persistent/clean differential testing and future native adapters
possible without changing symbolic reasoning code.
"""

from __future__ import annotations

from contextlib import AbstractContextManager
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Protocol, runtime_checkable

from ..bridge.contracts import StateToken
from ..contracts import CandidateCheck, CaseSplitCheck, GoalInfo, RefinementCheck
from ..project_configuration import ProjectConfiguration
from ..retrieval import ScopedPremises


@dataclass(frozen=True)
class CommittedProofAction:
    """One Agda-accepted transition used by in-session proof search."""

    accepted: bool
    child_state: StateToken | None
    preview: str | None
    generated_goals: tuple[GoalInfo, ...]
    alternatives: tuple[str, ...] = ()
    rejection_code: str | None = None


class KernelSession(Protocol):
    """Minimum compatibility surface required by complete search."""

    executable: str
    version: str

    @property
    def toolchain_id(self) -> str: ...

    def load_module(self, source_file: Path) -> tuple[GoalInfo, ...]: ...

    def inspect_goal(self, goal: GoalInfo) -> GoalInfo: ...

    def check_candidate(self, goal_id: int, rendered_term: str) -> CandidateCheck: ...

    def check_refinement(self, goal_id: int, expression: str) -> RefinementCheck: ...

    def check_case_split(self, goal_id: int, variable: str) -> CaseSplitCheck: ...


@runtime_checkable
class ResultSplittingSession(Protocol):
    """Optional kernel-owned clause introduction, including copatterns.

    This observes clauses for an open goal without applying them. It neither
    classifies a record as coinductive nor certifies a recursive call as guarded.
    Reconstruction must reload the changed source and freshly validate a
    completed definition, including Agda's coverage/productivity checks.
    """

    def check_result_split(
        self, state: StateToken, *, goal_id: int
    ) -> CaseSplitCheck: ...


@runtime_checkable
class ProjectRevisionSession(Protocol):
    """Optional new-epoch loading with explicitly rebound project routing.

    No state token from the previous project may be used after rebinding.
    The kernel, not the caller, decides whether checked imports can be reused.
    """

    def load_project(
        self,
        source_file: Path,
        project_configuration: ProjectConfiguration | None,
    ) -> tuple[GoalInfo, ...]: ...


@runtime_checkable
class TransactionalKernelSession(Protocol):
    """Optional replayable-state capability used by structural search."""

    def current_state(self) -> StateToken: ...

    def inspect_state(self, state: StateToken) -> tuple[GoalInfo, ...]: ...

    def commit_proof_action(
        self,
        state: StateToken,
        *,
        kind: Literal["give", "refine"],
        goal_id: int,
        expression: str,
    ) -> CommittedProofAction: ...

    def constructor_candidates(
        self,
        state: StateToken,
        *,
        goal_id: int,
        type_head: str,
    ) -> tuple[tuple[str, str], ...]: ...


@runtime_checkable
class ScopedRetrievalSession(Protocol):
    """Optional live kernel scope, filtered before types/features are queried.

    None means disabled/unavailable, not an empty allowed set. Once enabled,
    malformed or failed observations must raise, never widen to a lossy scope.
    """

    def scoped_retrieval(
        self,
        state: StateToken,
        *,
        goal_id: int,
        excluded_names: frozenset[str] = frozenset(),
    ) -> ScopedPremises | None: ...


@runtime_checkable
class ScopeDeclarationSession(Protocol):
    """Optional typed catalogue of declarations visible at an interaction."""

    def scope_declarations(
        self,
        state: StateToken,
        *,
        goal_id: int,
    ) -> tuple[tuple[str, str], ...]: ...


@runtime_checkable
class UniverseScopeSession(Protocol):
    """Goal-local primitive identities, resolved through Agda's import scope."""

    def universe_names(
        self, state: StateToken, *, goal_id: int, type_texts: tuple[str, ...]
    ) -> frozenset[str]: ...


@runtime_checkable
class InternalObligationSession(Protocol):
    """Optional observation of hidden metas and constraints in a state."""

    def internal_obligation_counts(self, state: StateToken) -> tuple[int, int]: ...


@runtime_checkable
class PreciseSearchGoalSession(Protocol):
    """Optional normalized goal inspection after dependent substitutions."""

    def inspect_search_goal(
        self, state: StateToken, *, goal_id: int
    ) -> GoalInfo | None: ...


@runtime_checkable
class InstantiatedGoalSession(Protocol):
    """Observe a scoped term already assigned by Agda, without proof search.

    None means the registered interaction has no observable assignment. A
    rendering is not proof acceptance: it may still contain nested metas, and
    callers must use ordinary checked actions and independent final validation.
    """

    def instantiated_goal(self, state: StateToken, *, goal_id: int) -> str | None: ...


@runtime_checkable
class TermInferenceSession(Protocol):
    """Observational type inference for bounded synthesized expressions."""

    def infer_type(
        self,
        state: StateToken,
        *,
        goal_id: int,
        expression: str,
    ) -> str | None: ...


class KernelSessionFactory(Protocol):
    """Construct one bounded kernel session for a search operation."""

    def __call__(
        self,
        *,
        timeout_seconds: float,
        deadline: float | None = None,
        project_configuration: ProjectConfiguration | None = None,
    ) -> AbstractContextManager[KernelSession]: ...


__all__ = [
    "CommittedProofAction",
    "InstantiatedGoalSession",
    "InternalObligationSession",
    "KernelSession",
    "KernelSessionFactory",
    "PreciseSearchGoalSession",
    "ProjectRevisionSession",
    "ScopeDeclarationSession",
    "ScopedRetrievalSession",
    "TermInferenceSession",
    "TransactionalKernelSession",
]
