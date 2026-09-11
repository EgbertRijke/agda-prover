"""One-window adapter from the P0 session surface to ``KernelSessionV1``."""

from __future__ import annotations

import hashlib
import math
import time
from collections import OrderedDict
from dataclasses import replace
from pathlib import Path
from typing import Any, Literal

from ..contracts import (
    CandidateCheck,
    CaseSplitCheck,
    ContextEntry,
    GoalInfo,
    RefinementCheck,
)
from ..kernel.protocol import CommittedProofAction
from ..project_configuration import ProjectConfiguration
from ..resource_budget import ResourceLimitError
from ..retrieval import ScopedPremises
from ..type_syntax import (
    DEFAULT_UNIVERSE_NAMES,
    is_universe_head,
    split_top_level_arrows,
    telescope_introduction,
    top_level_arrow_count,
    type_heads,
)
from .configuration import project_request
from .contracts import (
    BridgeBudget,
    BridgeError,
    BridgeFailure,
    CommandId,
    InteractionId,
    StateToken,
)
from .interaction import ClauseAction, RewriteMode
from .operations import ActionInput, OpenProjectResult, TermInput, TryActionResult
from .project import detect_toolchain
from .proof_state import Goal
from .session import ConformingKernelSession
from .workspace import ProjectInputs, project_inputs

SUPPORTED_AGDA_VERSION = "2.8.0"
AGDA_REFINE_META_LIMIT = 10


class AgdaBridgeError(RuntimeError):
    pass


class AgdaLoadError(AgdaBridgeError):
    pass


def _p0_error(error: BridgeError, *, loading: bool = False) -> BaseException:
    if error.failure == BridgeFailure.TIMEOUT:
        return TimeoutError(error.diagnostic.message)
    if error.failure == BridgeFailure.RESOURCE_EXHAUSTED:
        return ResourceLimitError(
            f"{error.diagnostic.code}: {error.diagnostic.message}"
        )
    if loading or error.failure == BridgeFailure.LOAD_FAILURE:
        return AgdaLoadError(error.diagnostic.message)
    return AgdaBridgeError(f"{error.diagnostic.code}: {error.diagnostic.message}")


def _goal(goal: Goal) -> GoalInfo:
    return GoalInfo(
        goal_id=goal.interaction_id.value,
        target=goal.target.text,
        context=tuple(
            ContextEntry(
                name=binder.suggested_name,
                type=binder.type.text,
                in_scope=binder.in_scope,
            )
            for binder in goal.telescope
        ),
        source_range=(goal.source_range.start, goal.source_range.end),
    )


def _diagnostic_events(error: BridgeError | None) -> tuple[dict[str, Any], ...]:
    return (
        ({"kind": "BridgeDiagnostic", "diagnostic": error.diagnostic.to_dict()},)
        if error is not None
        else ()
    )


class AgdaSession:
    """Deprecated P0 methods backed only by the Stage 1 session contract."""

    def __init__(
        self,
        executable: str = "agda",
        timeout_seconds: float = math.inf,
        *,
        deadline: float | None = None,
        project_configuration: ProjectConfiguration | None = None,
    ) -> None:
        if math.isnan(timeout_seconds) or timeout_seconds <= 0:
            raise TimeoutError("no wall-time remains for an Agda session")
        now = time.monotonic()
        wall = (
            min(timeout_seconds, deadline - now)
            if deadline is not None
            else timeout_seconds
        )
        if wall <= 0:
            raise TimeoutError("Agda task wall-time budget exhausted")
        self._budget = BridgeBudget.for_run(wall)
        self._project_configuration = project_configuration
        if project_configuration is not None:
            executable = project_configuration.executable
        try:
            self._toolchain = detect_toolchain(executable, self._budget)
        except BridgeError as error:
            raise _p0_error(error) from error
        self.executable = str(self._toolchain.executable)
        self.version = self._toolchain.version
        self.timeout_seconds = timeout_seconds
        self.deadline = self._budget.deadline
        self._session = ConformingKernelSession()
        self._open_result: OpenProjectResult | None = None
        self._state: StateToken | None = None
        self._source_file: Path | None = None
        self._source_sha256: str | None = None
        self._search_contexts: dict[int, tuple[ContextEntry, ...]] = {}
        self._sort_names: OrderedDict[tuple[StateToken, int, str], bool] = OrderedDict()

    @property
    def toolchain_id(self) -> str:
        return self._toolchain.executable_sha256[:20]

    def project_inputs(self) -> ProjectInputs:
        return project_inputs(self._session.project)

    @property
    def active_command(self) -> CommandId | None:
        return self._session.active_command

    def __enter__(self) -> AgdaSession:
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        self.close()

    def open(self) -> None:
        """Retained for API compatibility; project resolution is source-bound."""

    def close(self) -> None:
        try:
            self._session.close()
        except BridgeError as error:
            raise _p0_error(error) from error

    def cancel(self) -> bool:
        command = self.active_command
        return bool(command is not None and self._session.cancel(command))

    def _ensure_project(
        self,
        source_file: Path,
        configuration: ProjectConfiguration | None,
        *,
        force_revision: bool = False,
    ) -> None:
        path = source_file.resolve()
        try:
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError as error:
            raise AgdaLoadError(f"source file not found: {path}") from error
        if (
            not force_revision
            and self._source_file == path
            and self._source_sha256 == digest
            and self._project_configuration == configuration
        ):
            return
        request = project_request(path, configuration, executable=self.executable)
        try:
            if self._open_result is None:
                self._open_result = self._session.open_project(request, self._budget)
            else:
                self._open_result = self._session.reset_project(request, self._budget)
        except BridgeError as error:
            raise _p0_error(error, loading=True) from error
        self._source_file = path
        self._source_sha256 = digest
        self._project_configuration = configuration
        self._state = None
        self._search_contexts.clear()
        self._sort_names.clear()

    def load_module(self, source_file: Path) -> tuple[GoalInfo, ...]:
        self._ensure_project(source_file, self._project_configuration)
        return self._load_module()

    def load_project(
        self,
        source_file: Path,
        project_configuration: ProjectConfiguration | None,
    ) -> tuple[GoalInfo, ...]:
        self._ensure_project(source_file, project_configuration, force_revision=True)
        return self._load_module()

    def _load_module(self) -> tuple[GoalInfo, ...]:
        if self._open_result is None:
            raise AgdaLoadError("project resolution produced no environment")
        try:
            loaded = self._session.load_search_module(
                self._open_result.project,
                self._open_result.root_module,
                self._open_result.source_revision,
                self._budget,
            )
        except BridgeError as error:
            raise _p0_error(error, loading=True) from error
        self._state = loaded.transition.child_state
        goals = tuple(_goal(goal) for goal in loaded.state.goals)
        self._search_contexts.update((goal.goal_id, goal.context) for goal in goals)
        return goals

    def inspect_goal(self, goal: GoalInfo) -> GoalInfo:
        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        try:
            inspected = self._session.inspect_selected_goals(
                self._state, (InteractionId(goal.goal_id),), self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        selected = next(iter(inspected), None)
        if selected is None:
            raise AgdaBridgeError(f"goal {goal.goal_id} is not open")
        result = self._observe_universes(self._state, _goal(selected))
        self._search_contexts[result.goal_id] = result.context
        return result

    def auto_one(self, goal_id: int) -> str | None:
        """Return Agda Auto's proposal for baseline comparison, if any."""

        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        try:
            return self._session.auto_one(
                self._state, InteractionId(goal_id), self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error

    def check_candidate(self, goal_id: int, rendered_term: str) -> CandidateCheck:
        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        try:
            checked = self._session.try_action(
                self._state,
                ActionInput("check-term", InteractionId(goal_id), rendered_term),
                self._budget,
            )
        except BridgeError as error:
            if error.failure == BridgeFailure.AGDA_REJECTION:
                return CandidateCheck(
                    False,
                    None,
                    error.diagnostic.message,
                    _diagnostic_events(error),
                )
            raise _p0_error(error) from error
        diagnostic = next(
            (
                item.message
                for item in checked.transition.diagnostics
                if item.severity == "error"
            ),
            "",
        )
        return CandidateCheck(
            checked.accepted,
            checked.preview if checked.accepted else None,
            diagnostic,
            tuple(
                {"kind": "BridgeDiagnostic", "diagnostic": item.to_dict()}
                for item in checked.transition.diagnostics
            ),
        )

    def check_refinement(self, goal_id: int, expression: str) -> RefinementCheck:
        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        try:
            checked = self._session.try_action(
                self._state,
                ActionInput("refine", InteractionId(goal_id), expression),
                self._budget,
            )
            if not expression:
                checked = self._recover_empty_introduction(
                    self._state, goal_id, checked, commit=False
                )
            if (
                not checked.accepted
                and expression
                and checked.rejection_code == "agda-interaction-cannot-refine"
            ):
                expanded = self._expanded_refinement(
                    self._state, goal_id=goal_id, expression=expression
                )
                if expanded is not None:
                    checked = self._session.try_action(
                        self._state,
                        ActionInput("refine", InteractionId(goal_id), expanded),
                        self._budget,
                    )
        except BridgeError as error:
            raise _p0_error(error) from error
        diagnostic = next(
            (
                item.message
                for item in checked.transition.diagnostics
                if item.severity == "error"
            ),
            "",
        )
        return RefinementCheck(
            checked.accepted,
            checked.preview,
            tuple(_goal(goal).to_dict() for goal in checked.generated_goals),
            diagnostic,
            tuple(
                {"kind": "BridgeDiagnostic", "diagnostic": item.to_dict()}
                for item in checked.transition.diagnostics
            ),
        )

    def check_case_split(self, goal_id: int, variable: str) -> CaseSplitCheck:
        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        try:
            checked = self._session.case_split(
                self._state,
                variable,
                InteractionId(goal_id),
                self._budget,
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        diagnostic = next(
            (
                item.message
                for item in checked.transition.diagnostics
                if item.severity == "error"
            ),
            "",
        )
        return CaseSplitCheck(
            checked.accepted,
            checked.clauses,
            checked.variant,
            diagnostic,
            tuple(
                {"kind": "BridgeDiagnostic", "diagnostic": item.to_dict()}
                for item in checked.transition.diagnostics
            ),
        )

    def check_complete_candidate(self, goal_id: int, expression: str) -> CandidateCheck:
        """Distinguish elaboration success from a locally closed completion.

        This remains search evidence, never a replacement for fresh validation.
        The committed probe belongs to its own child; the caller's parent token
        stays unchanged, including after an incomplete or rejected probe.
        """
        candidate = self.check_candidate(goal_id, expression)
        if not candidate.accepted:
            return candidate
        state = self.current_state()
        baseline = self.internal_obligation_counts(state)
        checked = self.commit_proof_action(
            state, kind="give", goal_id=goal_id, expression=expression
        )
        if (
            checked.accepted
            and checked.child_state is not None
            and not checked.generated_goals
        ):
            obligations = self.internal_obligation_counts(checked.child_state)
            if all(
                current <= previous
                for current, previous in zip(obligations, baseline, strict=True)
            ):
                return candidate
        return CandidateCheck(
            False, None, "candidate leaves unresolved internal obligations", ()
        )

    def check_result_split(self, state: StateToken, *, goal_id: int) -> CaseSplitCheck:
        """Observe source clauses for a result, preserving the explicit parent."""
        return self.check_clause_action(
            state, goal_id=goal_id, action=ClauseAction("result")
        )

    def check_clause_action(
        self, state: StateToken, *, goal_id: int, action: ClauseAction
    ) -> CaseSplitCheck:
        try:
            checked = self._session.make_clause(
                state, InteractionId(goal_id), action, self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        return CaseSplitCheck(
            checked.accepted,
            checked.clauses,
            checked.variant,
            next(
                (
                    item.message
                    for item in checked.transition.diagnostics
                    if item.severity == "error"
                ),
                "",
            ),
            tuple(
                {"kind": "BridgeDiagnostic", "diagnostic": item.to_dict()}
                for item in checked.transition.diagnostics
            ),
        )

    def helper_signature(
        self,
        state: StateToken,
        *,
        goal_id: int,
        application: str,
        mode: RewriteMode = RewriteMode.NORMAL,
    ) -> str | None:
        try:
            return self._session.helper_signature(
                state,
                InteractionId(goal_id),
                TermInput(application),
                self._budget,
                mode=mode,
            )
        except BridgeError as error:
            raise _p0_error(error) from error

    def inspect_goal_view(
        self, state: StateToken, *, goal_id: int, mode: RewriteMode
    ) -> GoalInfo | None:
        """An observational view, not a replacement for cached canonical goals."""
        try:
            selected = self._session.inspect_selected_goals(
                state,
                (InteractionId(goal_id),),
                self._budget,
                mode=mode,
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        return self._observe_universes(state, _goal(selected[0])) if selected else None

    def current_state(self) -> StateToken:
        """Return the immutable token for the currently loaded source state."""

        if self._state is None:
            raise AgdaBridgeError("no module state is loaded")
        return self._state

    def inspect_state(self, state: StateToken) -> tuple[GoalInfo, ...]:
        """Read an internal search state without completing unrelated goals."""

        try:
            snapshot = self._session.search_state(state, self._budget)
        except BridgeError as error:
            raise _p0_error(error) from error
        return tuple(
            GoalInfo(
                goal_id=goal.interaction_id.value,
                target=goal.target.text,
                context=self._search_contexts.get(goal.interaction_id.value, ()),
                source_range=(goal.source_range.start, goal.source_range.end),
            )
            for goal in snapshot.goals
        )

    def inspect_search_goal(
        self, state: StateToken, *, goal_id: int
    ) -> GoalInfo | None:
        """Inspect one live goal after all substitutions made by its siblings."""

        try:
            selected = self._session.inspect_selected_goals(
                state, (InteractionId(goal_id),), self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        if not selected:
            return None
        goal = self._observe_universes(state, _goal(selected[0]))
        self._search_contexts[goal.goal_id] = goal.context
        return goal

    def universe_names(
        self, state: StateToken, *, goal_id: int, type_texts: tuple[str, ...]
    ) -> frozenset[str]:
        """Resolve possible universe spellings in this exact interaction scope.

        Imports, re-exports, qualification and shadowing are Agda's concern.
        The cache never crosses a branch, interaction or source revision.
        Rejected lookups are not evidence that any theorem is impossible.
        """
        candidates = frozenset().union(*(type_heads(ty) for ty in type_texts))
        pending = tuple(
            sorted(
                name
                for name in candidates
                if (state, goal_id, name) not in self._sort_names
            )
        )
        try:
            # Even a cache hit must reject stale states and changed sources.
            found = self._session.search_sort_names(
                state, InteractionId(goal_id), pending, self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error
        result = {
            name
            for name in candidates
            if self._sort_names.get((state, goal_id, name), False)
        } | set(found)
        for name in pending:
            self._sort_names[(state, goal_id, name)] = name in found
        # Eviction only loses an optimization, never admissible search work.
        while len(self._sort_names) > 2048:
            self._sort_names.popitem(last=False)
        return frozenset(result)

    def _observe_universes(self, state: StateToken, goal: GoalInfo) -> GoalInfo:
        type_texts = (goal.target, *(entry.type for entry in goal.context))
        names = self.universe_names(
            state,
            goal_id=goal.goal_id,
            type_texts=type_texts,
        )
        # Keep the legacy rendering unchanged when it already uses the
        # default spellings, unless a canonical spelling is itself shadowed.
        canonical_candidates = {
            name
            for ty in type_texts
            for name in type_heads(ty)
            if is_universe_head(name)
        }
        return (
            goal
            if names <= DEFAULT_UNIVERSE_NAMES and canonical_candidates <= names
            else replace(goal, universe_names=names)
        )

    def instantiated_goal(self, state: StateToken, *, goal_id: int) -> str | None:
        """Read an existing Agda assignment; no candidate is submitted."""
        try:
            return self._session.instantiated_goal(
                state, InteractionId(goal_id), self._budget
            )
        except BridgeError as error:
            raise _p0_error(error) from error

    def internal_obligation_counts(self, state: StateToken) -> tuple[int, int]:
        """Return hidden open-meta and constraint counts for completion checks."""

        try:
            return self._session.residual_obligation_counts(state, self._budget)
        except BridgeError as error:
            raise _p0_error(error) from error

    def commit_proof_action(
        self,
        state: StateToken,
        *,
        kind: Literal["give", "refine"],
        goal_id: int,
        expression: str,
    ) -> CommittedProofAction:
        """Apply one checked search action and retain its replayable child."""

        try:
            parent_goal = next(
                goal for goal in self.inspect_state(state) if goal.goal_id == goal_id
            )
            checked = self._session.try_search_action(
                state,
                ActionInput(
                    kind,
                    InteractionId(goal_id),
                    expression,
                    commit=True,
                ),
                self._budget,
            )
            if kind == "refine" and not expression:
                checked = self._recover_empty_introduction(
                    state, goal_id, checked, commit=True, parent_goal=parent_goal
                )
            if (
                not checked.accepted
                and kind == "refine"
                and not expression
                and checked.rejection_code == "agda-not-in-scope"
            ):
                literal = self._session.search_record_introduction(
                    state, InteractionId(goal_id), self._budget
                )
                if literal is not None:
                    checked = self._session.try_search_action(
                        state,
                        ActionInput(kind, InteractionId(goal_id), literal, commit=True),
                        self._budget,
                    )
            if (
                not checked.accepted
                and kind == "refine"
                and expression
                and checked.rejection_code == "agda-interaction-cannot-refine"
            ):
                expanded = self._expanded_refinement(
                    state, goal_id=goal_id, expression=expression
                )
                if expanded is not None:
                    checked = self._session.try_search_action(
                        state,
                        ActionInput(
                            kind,
                            InteractionId(goal_id),
                            expanded,
                            commit=True,
                        ),
                        self._budget,
                    )
        except BridgeError as error:
            raise _p0_error(error) from error
        alternatives = next(
            (
                item.causes
                for item in checked.transition.diagnostics
                if item.code == "agda-intro-constructor-unknown"
            ),
            (),
        )
        child_goals: tuple[GoalInfo, ...] = ()
        if checked.transition.child_state is not None:
            generated_ids = {
                goal.interaction_id.value for goal in checked.generated_goals
            }
            child_state = checked.transition.child_state
            if top_level_arrow_count(parent_goal.target) and generated_ids:
                try:
                    inspected = self._session.inspect_selected_goals(
                        child_state,
                        tuple(
                            InteractionId(identifier) for identifier in generated_ids
                        ),
                        self._budget,
                    )
                except BridgeError as error:
                    raise _p0_error(error) from error
                child_goals = tuple(_goal(goal) for goal in inspected)
            else:
                child_goals = tuple(
                    GoalInfo(
                        goal_id=goal.interaction_id.value,
                        target=goal.target.text,
                        context=parent_goal.context,
                        source_range=(
                            goal.source_range.start,
                            goal.source_range.end,
                        ),
                    )
                    for goal in checked.generated_goals
                )
            self._search_contexts.update(
                (goal.goal_id, goal.context) for goal in child_goals
            )
        return CommittedProofAction(
            accepted=checked.accepted,
            child_state=checked.transition.child_state,
            preview=checked.preview,
            generated_goals=child_goals,
            alternatives=alternatives,
            rejection_code=checked.rejection_code,
        )

    def _recover_empty_introduction(
        self,
        state: StateToken,
        goal_id: int,
        checked: TryActionResult,
        *,
        commit: bool,
        parent_goal: GoalInfo | None = None,
    ) -> TryActionResult:
        """Recover Agda's accepted-but-unrenderable automatic introduction.

        Some pattern telescopes produce only ``?`` plus dangling interaction
        metas. Retry once from the original parent, never from that child.
        The explicit checked action owns the returned lineage and preview;
        both physical calls remain charged by the transport budget.
        """
        if (
            not checked.accepted
            or checked.preview is None
            or checked.preview.strip() != "?"
        ):
            return checked
        if parent_goal is None:
            parent_goal = next(
                goal for goal in self.inspect_state(state) if goal.goal_id == goal_id
            )
        expression = telescope_introduction(
            parent_goal.target,
            frozenset(entry.name for entry in parent_goal.context if entry.name),
            implicit_only=False,
        )
        if expression is not None:
            operation = (
                self._session.try_search_action if commit else self._session.try_action
            )
            retried = operation(
                state,
                ActionInput(
                    "refine", InteractionId(goal_id), expression, commit=commit
                ),
                self._budget,
            )
            if (
                not retried.accepted
                or retried.preview is None
                or retried.preview.strip() != "?"
            ):
                return retried
            checked = retried
        # Unsupported/no-progress output is an unavailable action, not an
        # invalid input file or a completion. Do not publish its child/metas.
        return replace(
            checked,
            transition=replace(checked.transition, child_state=None, committed=False),
            accepted=False,
            preview=None,
            generated_goals=(),
            edge=None,
            rejection_code="agda-intro-no-progress",
        )

    def _expanded_refinement(
        self,
        state: StateToken,
        *,
        goal_id: int,
        expression: str,
    ) -> str | None:
        """Make Agda's bounded refine application explicit for wide functions."""

        try:
            inferred = self._session.infer(
                state,
                TermInput(expression),
                self._budget,
                interaction_id=InteractionId(goal_id),
            )
        except BridgeError as error:
            if error.failure != BridgeFailure.AGDA_REJECTION:
                raise _p0_error(error) from error
            return None
        if not inferred.accepted or inferred.inferred_type is None:
            return None
        try:
            domains = split_top_level_arrows(inferred.inferred_type.text)[:-1]
        except ValueError:
            return None
        visible_count = sum(
            1 for domain in domains if not domain.lstrip().startswith(("{", "⦃"))
        )
        if visible_count < AGDA_REFINE_META_LIMIT:
            return None
        return f"({expression})" + " ?" * visible_count

    def infer_type(
        self,
        state: StateToken,
        *,
        goal_id: int,
        expression: str,
        mode: RewriteMode = RewriteMode.NORMAL,
    ) -> str | None:
        """Infer an expression's type without changing the proof state."""

        try:
            inferred = self._session.infer(
                state,
                TermInput(expression),
                self._budget,
                interaction_id=InteractionId(goal_id),
                mode=mode,
            )
        except BridgeError as error:
            if error.failure != BridgeFailure.AGDA_REJECTION:
                raise _p0_error(error) from error
            return None
        if not inferred.accepted or inferred.inferred_type is None:
            return None
        return inferred.inferred_type.text

    def constructor_candidates(
        self,
        state: StateToken,
        *,
        goal_id: int,
        type_head: str,
    ) -> tuple[tuple[str, str], ...]:
        """Ask Agda for declarations exported by a datatype's module."""

        try:
            return self._session.search_constructor_candidates(
                state,
                InteractionId(goal_id),
                type_head,
                self._budget,
            )
        except BridgeError as error:
            raise _p0_error(error) from error

    def scoped_retrieval(
        self,
        state: StateToken,
        *,
        goal_id: int,
        excluded_names: frozenset[str] = frozenset(),
    ) -> ScopedPremises | None:
        try:
            return self._session.search_scoped_retrieval(
                state,
                InteractionId(goal_id),
                self._budget,
                excluded_names=excluded_names,
            )
        except BridgeError as error:
            raise _p0_error(error) from error

    def scope_declarations(
        self,
        state: StateToken,
        *,
        goal_id: int,
    ) -> tuple[tuple[str, str], ...]:
        """Ask Agda for every declaration visible at this interaction."""

        try:
            return self._session.search_constructor_candidates(
                state,
                InteractionId(goal_id),
                "",
                self._budget,
            )
        except BridgeError as error:
            raise _p0_error(error) from error
