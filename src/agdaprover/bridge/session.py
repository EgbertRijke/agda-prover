"""Transactional, version-neutral kernel session implemented by deterministic replay."""

from __future__ import annotations

import hashlib
import os
import tempfile
import time
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Protocol

from ..artifacts import executable_sha256
from ..resource_budget import StorageLease, charge_io
from ..retrieval import ScopedPremises
from ..source_files import agda_source_suffix
from .contracts import (
    BridgeBudget,
    BridgeCost,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    BridgeResourceSummary,
    CommandId,
    DiagnosticPhase,
    InteractionId,
    MetaId,
    ModuleId,
    ProjectHandle,
    SourceRange,
    SourceRevision,
    StateToken,
    stable_hash,
)
from .diagnostics import diagnostics_from_response, first_error
from .live_scope import decode_scope, exclusions_payload
from .operations import (
    ActionInput,
    CandidateDefinition,
    CaseSplitResult,
    CheckDefinitionResult,
    InferResult,
    InspectGoalsResult,
    LoadModuleResult,
    NormalizeResult,
    OpenProjectRequest,
    OpenProjectResult,
    PolicyProfile,
    ProofHyperedge,
    ReductionPolicy,
    SourceEdit,
    SourcePatch,
    StateTransition,
    TermInput,
    TryActionResult,
    ValidatePatchResult,
)
from .project import ResolvedProject, resolve_project
from .proof_state import (
    Binder,
    Constraint,
    DependencyEdge,
    Goal,
    Meta,
    ProofEdge,
    ProofState,
    TermView,
)
from .resources import CancellationToken, ProcessUsage, temporary_storage
from .transport import AgdaJsonTransport
from .validator import validate_patch as run_fresh_validation
from .versions import adapter_for_version
from .versions.agda_2_8 import GoalObservation


def _transactional_bridge_executable(version: str) -> Path | None:
    """Return the explicitly built Agda 2.8 adapter, never building at runtime."""

    if os.environ.get("AGDAPROVER_DISABLE_AGDA_BRIDGE") == "1":
        return None
    if not version.startswith("2.8"):
        return None
    configured = os.environ.get("AGDAPROVER_AGDA_BRIDGE")
    if not configured:
        return None
    candidate = Path(configured)
    return candidate if candidate.is_file() and os.access(candidate, os.X_OK) else None


class KernelSessionV1(Protocol):
    def open_project(
        self, request: OpenProjectRequest, budget: BridgeBudget
    ) -> OpenProjectResult: ...

    def load_module(
        self,
        project: ProjectHandle,
        module: ModuleId,
        expected_revision: SourceRevision,
        budget: BridgeBudget,
    ) -> LoadModuleResult: ...

    def inspect_goals(
        self, state: StateToken, budget: BridgeBudget
    ) -> InspectGoalsResult: ...

    def infer(
        self,
        state: StateToken,
        term: TermInput,
        budget: BridgeBudget,
        *,
        interaction_id: InteractionId | None = None,
    ) -> InferResult: ...

    def normalize(
        self,
        state: StateToken,
        term: TermInput,
        policy: ReductionPolicy,
        budget: BridgeBudget,
        *,
        interaction_id: InteractionId | None = None,
    ) -> NormalizeResult: ...

    def try_action(
        self, state: StateToken, action: ActionInput, budget: BridgeBudget
    ) -> TryActionResult: ...

    def case_split(
        self,
        state: StateToken,
        subject: str,
        interaction_id: InteractionId,
        budget: BridgeBudget,
        *,
        commit: bool = False,
    ) -> CaseSplitResult: ...

    def check_definition(
        self,
        state: StateToken,
        definition: CandidateDefinition,
        budget: BridgeBudget,
    ) -> CheckDefinitionResult: ...

    def validate_patch(
        self,
        project: ProjectHandle,
        patch: SourcePatch,
        policy: PolicyProfile,
        budget: BridgeBudget,
    ) -> ValidatePatchResult: ...

    def cancel(self, command: CommandId) -> bool: ...

    def close(self) -> BridgeResourceSummary: ...


@dataclass(frozen=True)
class _StateRecord:
    state: ProofState
    lineage: tuple[ActionInput, ...]


class ConformingKernelSession:
    """Own one resolved environment and a replay-isolated Agda process.

    Agda's public JSON protocol has no general TCM snapshot primitive.  This
    implementation therefore treats the source revision plus an accepted
    action lineage as the snapshot and deterministically reloads/replays it.
    A rollback failure poisons the process, making every old token stale.
    """

    def __init__(self) -> None:
        self._project: ResolvedProject | None = None
        self._transport: AgdaJsonTransport | None = None
        self._budget: BridgeBudget | None = None
        self._cancellation = CancellationToken()
        self._states: dict[int, _StateRecord] = {}
        self._state_sequence = 0
        self._active_state: StateToken | None = None
        self._closed = False
        self._last_resources: BridgeResourceSummary | None = None
        self._overlay: tempfile.TemporaryDirectory[str] | None = None
        self._runtime: tempfile.TemporaryDirectory[str] | None = None
        self._overlay_storage: StorageLease | None = None
        self._runtime_storage: StorageLease | None = None
        self._runtime_sources: dict[ModuleId, Path] = {}
        self._overlay_bytes = 0
        self._overlays_removed = 0
        self._live_scope_enabled = False
        self._scope_dependencies_enabled = False
        self._scope_adapter_hash: str | None = None

    def __enter__(self) -> ConformingKernelSession:
        return self

    def __exit__(self, _type: object, _value: object, _traceback: object) -> None:
        self.close()

    @property
    def project(self) -> ResolvedProject:
        if self._project is None:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "project-not-open",
                "open_project must succeed before this operation",
            )
        return self._project

    @property
    def transport(self) -> AgdaJsonTransport:
        if self._transport is None:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "transport-not-open",
                "load_module must succeed before this operation",
            )
        return self._transport

    @property
    def toolchain_id(self) -> str:
        return self.project.toolchain.executable_sha256[:20]

    @property
    def active_command(self) -> CommandId | None:
        return self._transport.active_command if self._transport is not None else None

    def current_usage(self) -> ProcessUsage:
        """Sample the complete Agda process tree for qualification tooling."""

        if self._transport is None:
            return ProcessUsage(0, 0.0, 0)
        return self._transport.current_usage()

    @property
    def state_count(self) -> int:
        return len(self._states)

    @property
    def buffered_bytes(self) -> int:
        return self._transport.buffered_bytes if self._transport is not None else 0

    def _prepare_overlay(self, project: ResolvedProject, budget: BridgeBudget) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="agdaprover-stage1-session-")
        root = Path(temporary.name)
        storage = temporary_storage(root)
        runtime_sources: dict[ModuleId, Path] = {}
        total_bytes = 0
        try:
            for index, source in enumerate(project.sources, 1):
                self._cancellation.raise_if_cancelled()
                if index > budget.artifact_count:
                    raise self._error(
                        BridgeFailure.RESOURCE_EXHAUSTED,
                        "session-overlay-artifact-exhausted",
                        "session overlay exceeded its artifact-count budget",
                    )
                if budget.deadline <= time.monotonic():
                    raise self._error(
                        BridgeFailure.TIMEOUT,
                        "session-overlay-timeout",
                        "session overlay materialization exceeded its deadline",
                    )
                suffix = agda_source_suffix(source.path)
                if suffix is None:
                    raise self._error(
                        BridgeFailure.INTERNAL_INVARIANT,
                        "session-overlay-source-kind-invalid",
                        "resolved project contains a non-Agda source",
                    )
                destination = root / Path(
                    str(Path(*source.module.name.split("."))) + suffix
                )
                destination.parent.mkdir(parents=True, exist_ok=True)
                content = source.path.read_bytes()
                charge_io(len(content))
                total_bytes += len(content)
                if total_bytes > budget.temporary_bytes:
                    raise self._error(
                        BridgeFailure.RESOURCE_EXHAUSTED,
                        "session-overlay-storage-exhausted",
                        "session overlay exceeded its temporary-storage budget",
                    )
                destination.write_bytes(content)
                charge_io(len(content))
                storage.sample()
                runtime_sources[source.module] = destination
            storage.sample(force=True)
        except OSError as error:
            try:
                storage.close()
            finally:
                temporary.cleanup()
            raise self._error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "session-overlay-materialization-failed",
                f"could not materialize the session overlay: {error}",
            ) from error
        except BaseException:
            try:
                storage.close()
            finally:
                temporary.cleanup()
            raise
        old_overlay = self._overlay
        old_storage = self._overlay_storage
        self._overlay = temporary
        self._overlay_storage = storage
        self._runtime_sources = runtime_sources
        self._overlay_bytes = total_bytes
        if old_overlay is not None:
            try:
                if old_storage is not None:
                    old_storage.close()
            finally:
                old_overlay.cleanup()
                self._overlays_removed += 1

    def _cleanup_overlay(self) -> None:
        overlay = self._overlay
        storage = self._overlay_storage
        self._overlay = None
        self._overlay_storage = None
        self._runtime_sources.clear()
        self._overlay_bytes = 0
        try:
            if storage is not None:
                storage.close()
        finally:
            if overlay is not None:
                overlay.cleanup()
                self._overlays_removed += 1

    def _source_for(self, module: ModuleId) -> Path:
        try:
            return self._runtime_sources[module]
        except KeyError as error:
            raise self._error(
                BridgeFailure.INTERNAL_INVARIANT,
                "session-overlay-module-missing",
                f"session overlay does not contain module {module.name}",
            ) from error

    def open_project(
        self, request: OpenProjectRequest, budget: BridgeBudget
    ) -> OpenProjectResult:
        if self._closed:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "session-closed",
                "cannot open a project on a closed session",
            )
        if self._project is not None:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "project-already-open",
                "one kernel session is bound to exactly one project",
            )
        live_scope = os.environ.get("AGDAPROVER_SCOPED_RETRIEVAL") == "1"
        scoped_dependencies = os.environ.get("AGDAPROVER_SCOPED_DEPENDENCIES") == "1"
        if scoped_dependencies and not live_scope:
            raise self._error(
                BridgeFailure.UNSUPPORTED_CAPABILITY,
                "scoped-dependencies-require-live-scope",
                "Scoped dependencies require AGDAPROVER_SCOPED_RETRIEVAL=1",
            )
        project, result = resolve_project(request, budget)
        self._prepare_overlay(project, budget)
        try:
            runtime = tempfile.TemporaryDirectory(prefix="agdaprover-stage1-runtime-")
        except OSError as error:
            self._cleanup_overlay()
            raise self._error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "session-runtime-directory-failed",
                f"could not create the isolated session runtime: {error}",
            ) from error
        self._runtime = runtime
        self._runtime_storage = temporary_storage(Path(runtime.name))
        self._project = project
        self._budget = budget
        bridge_executable = _transactional_bridge_executable(project.toolchain.version)
        self._live_scope_enabled = live_scope
        self._scope_dependencies_enabled = scoped_dependencies
        self._scope_adapter_hash = (
            executable_sha256(str(bridge_executable), deadline=budget.deadline)
            if self._live_scope_enabled and bridge_executable is not None
            else None
        )
        if self._scope_adapter_hash is not None:
            capabilities = replace(
                result.capabilities,
                adapter=result.capabilities.adapter
                + ("+live-scope-v3:" if scoped_dependencies else "+live-scope-v2:")
                + self._scope_adapter_hash,
                operations=tuple(
                    sorted(
                        (*result.capabilities.operations, "retrieve-scoped-premises")
                    )
                ),
                limitations=(
                    *result.capabilities.limitations,
                    "live retrieval is a ranking-only term-body feature projection; pattern synonyms and sorts are not indexed",
                    "live premise type views use contextual Agda normalization, not independently reconstructed type evidence",
                    "live scoped retrieval is opt-in and qualified only for Agda 2.8.0",
                ),
            )
            self._project = replace(project, capabilities=capabilities)
            result = replace(result, capabilities=capabilities)
        self._transport = AgdaJsonTransport(
            bridge_executable or project.toolchain.executable,
            adapter_for_version(project.toolchain.version),
            budget,
            cancellation=self._cancellation,
            runtime_root=Path(runtime.name),
            transactional_commands=bridge_executable is not None,
        )
        self._transport.cost.add(temporary_bytes=self._overlay_bytes)
        return replace(result, cost=BridgeCost(temporary_bytes=self._overlay_bytes))

    def reset_project(
        self, request: OpenProjectRequest, budget: BridgeBudget
    ) -> OpenProjectResult:
        """Start a new immutable environment epoch on the same worker.

        This is intentionally outside ``KernelSessionV1``.  It exists only for
        the P0 source-overlay compatibility adapter, whose historical API loads
        different candidate files through one process.  Every prior handle and
        token is discarded before the new environment becomes visible.
        """

        if self._project is None:
            return self.open_project(request, budget)
        self._check_budget_identity(budget)
        project, result = resolve_project(request, budget)
        if project.toolchain != self.project.toolchain:
            raise self._error(
                BridgeFailure.TOOLCHAIN_ERROR,
                "toolchain-changed-during-session",
                "compatibility reset cannot change the Agda executable",
            )
        # Materialize the replacement completely before releasing the current
        # immutable snapshot.  A copy/read/budget failure therefore leaves the
        # old project epoch usable by the compatibility caller.
        self._prepare_overlay(project, budget)
        self._project = project
        self._states.clear()
        self._active_state = None
        self.transport.cost.add(temporary_bytes=self._overlay_bytes)
        return replace(result, cost=BridgeCost(temporary_bytes=self._overlay_bytes))

    def load_module(
        self,
        project: ProjectHandle,
        module: ModuleId,
        expected_revision: SourceRevision,
        budget: BridgeBudget,
    ) -> LoadModuleResult:
        return self._load_module(
            project, module, expected_revision, budget, inspect_all=True
        )

    def load_search_module(
        self,
        project: ProjectHandle,
        module: ModuleId,
        expected_revision: SourceRevision,
        budget: BridgeBudget,
    ) -> LoadModuleResult:
        """Load a source state without eagerly inspecting every open goal.

        This internal compatibility path retains the same immutable state and
        transition contracts.  Search controllers inspect only the selected
        interaction, avoiding quadratic protocol traffic in files with many
        independent holes.
        """

        return self._load_module(
            project, module, expected_revision, budget, inspect_all=False
        )

    def _load_module(
        self,
        project: ProjectHandle,
        module: ModuleId,
        expected_revision: SourceRevision,
        budget: BridgeBudget,
        *,
        inspect_all: bool,
    ) -> LoadModuleResult:
        self._check_project(project, expected_revision)
        self._check_budget_identity(budget)
        self._ensure_sources_unchanged()
        source_file = self._source_for(module)
        before = self.transport.cost.copy()
        command_id, response = self.transport.command(
            source_file,
            adapter_for_version(self.project.toolchain.version).load(
                source_file, self.project.options
            ),
        )
        diagnostics = diagnostics_from_response(
            response,
            project_root=self.project.project_root,
        )
        error = first_error(diagnostics)
        if error is not None:
            raise BridgeError(BridgeFailure.LOAD_FAILURE, error, command_id=command_id)
        observations = adapter_for_version(
            self.project.toolchain.version
        ).interaction_points(response)
        shallow_state = self._state_from_observations(module, observations, cost={})
        provisional_token = self._register_state(shallow_state, ())
        self._active_state = provisional_token
        if inspect_all:
            inspected = self.inspect_goals(provisional_token, budget)
            state = inspected.state
            token = self._replace_state(provisional_token, state, ())
        else:
            state = shallow_state
            token = provisional_token
        self._active_state = token
        cost = self.transport.cost.delta(before)
        cost.add(module_loads=1)
        transition = self._transition(
            command_id,
            parent=None,
            child=token,
            diagnostics=diagnostics,
            cost=cost,
        )
        return LoadModuleResult(transition, module, (), state)

    def inspect_goals(
        self, state: StateToken, budget: BridgeBudget
    ) -> InspectGoalsResult:
        record = self._activate(state, budget)
        if "complete-json-observation" in record.state.extraction_capabilities:
            return InspectGoalsResult(
                self._transition(
                    self._synthetic_command_id(),
                    parent=state,
                    child=None,
                    diagnostics=(),
                    cost=BridgeCost(),
                ),
                record.state,
            )
        before = self.transport.cost.copy()
        goals: list[GoalObservation] = []
        last_command: CommandId | None = None
        all_diagnostics: list[BridgeDiagnostic] = []
        adapter = adapter_for_version(self.project.toolchain.version)
        for shallow in record.state.goals:
            command_id, response = self.transport.command(
                self._source_for(state.module_id),
                adapter.inspect_goal(shallow.interaction_id.value),
            )
            last_command = command_id
            diagnostics = diagnostics_from_response(
                response,
                primary_range=shallow.source_range,
                project_root=self.project.project_root,
            )
            all_diagnostics.extend(diagnostics)
            if first_error(diagnostics) is not None:
                continue
            observation = adapter.goal(response)
            if observation is not None:
                goals.append(observation)
        constraint_command, constraint_response = self.transport.command(
            self._source_for(state.module_id), adapter.constraints()
        )
        last_command = constraint_command
        all_diagnostics.extend(
            diagnostics_from_response(
                constraint_response, project_root=self.project.project_root
            )
        )
        constraints = tuple(
            Constraint(item.constraint_id, item.kind, item.rendered)
            for item in adapter.constraint_items(constraint_response)
        )
        meta_command, meta_response = self.transport.command(
            self._source_for(state.module_id), adapter.metas()
        )
        last_command = meta_command
        all_diagnostics.extend(
            diagnostics_from_response(
                meta_response, project_root=self.project.project_root
            )
        )
        visible_meta_ids = {f"interaction:{goal.interaction_id}" for goal in goals}
        additional_metas = tuple(
            Meta(
                meta_id=MetaId(item.meta_id),
                type=TermView(item.type_text),
                context=(),
                status="open",
                interaction_id=(
                    InteractionId(item.interaction_id)
                    if item.interaction_id is not None
                    else None
                ),
                source_range=SourceRange(
                    item.source_range.start,
                    item.source_range.end,
                    self._root_source_name(),
                ),
            )
            for item in adapter.meta_items(meta_response)
            if item.meta_id not in visible_meta_ids
        )
        complete_state = self._state_from_observations(
            state.module_id,
            tuple(goals),
            constraints=constraints,
            additional_metas=additional_metas,
            proof_dag=record.state.proof_dag,
            cost=self.transport.cost.delta(before).to_dict(),
            complete=True,
        )
        if last_command is None:
            raise self._error(
                BridgeFailure.INTERNAL_INVARIANT,
                "goal-inspection-command-invariant",
                "goal inspection completed without issuing a kernel command",
            )
        transition = self._transition(
            last_command,
            parent=state,
            child=None,
            diagnostics=tuple(all_diagnostics),
            cost=self.transport.cost.delta(before),
        )
        return InspectGoalsResult(transition, complete_state)

    def infer(
        self,
        state: StateToken,
        term: TermInput,
        budget: BridgeBudget,
        *,
        interaction_id: InteractionId | None = None,
    ) -> InferResult:
        self._activate(state, budget)
        before = self.transport.cost.copy()
        adapter = adapter_for_version(self.project.toolchain.version)
        command_id, response = self.transport.command(
            self._source_for(state.module_id),
            adapter.infer(
                interaction_id.value if interaction_id is not None else None,
                term.rendered,
            ),
        )
        diagnostics = diagnostics_from_response(
            response, project_root=self.project.project_root
        )
        observation = adapter.inferred(response)
        # Cmd_infer is observational: it does not modify Agda's proof state.
        self._active_state = state
        return InferResult(
            self._transition(
                command_id,
                parent=state,
                child=None,
                diagnostics=diagnostics,
                cost=self.transport.cost.delta(before),
            ),
            TermView(observation.inferred_type)
            if observation.inferred_type is not None
            else None,
            (),
            observation.accepted,
        )

    def normalize(
        self,
        state: StateToken,
        term: TermInput,
        policy: ReductionPolicy,
        budget: BridgeBudget,
        *,
        interaction_id: InteractionId | None = None,
    ) -> NormalizeResult:
        self._activate(state, budget)
        before = self.transport.cost.copy()
        adapter = adapter_for_version(self.project.toolchain.version)
        modes = {
            ReductionPolicy.AS_IS: "HeadCompute",
            ReductionPolicy.SIMPLIFIED: "HeadCompute",
            ReductionPolicy.NORMAL: "DefaultCompute",
            ReductionPolicy.HEAD_NORMAL: "HeadCompute",
            ReductionPolicy.IGNORE_ABSTRACT: "IgnoreAbstract",
        }
        command_id, response = self.transport.command(
            self._source_for(state.module_id),
            adapter.normalize(
                interaction_id.value if interaction_id is not None else None,
                term.rendered,
                modes[policy],
            ),
        )
        diagnostics = diagnostics_from_response(
            response, project_root=self.project.project_root
        )
        observation = adapter.normalized(response)
        # Cmd_compute is observational: it does not modify Agda's proof state.
        self._active_state = state
        return NormalizeResult(
            self._transition(
                command_id,
                parent=state,
                child=None,
                diagnostics=diagnostics,
                cost=self.transport.cost.delta(before),
            ),
            TermView(observation.normal_form)
            if observation.normal_form is not None
            else None,
            observation.complete,
            (),
        )

    def try_action(
        self, state: StateToken, action: ActionInput, budget: BridgeBudget
    ) -> TryActionResult:
        return self._try_action(state, action, budget, complete_child=True)

    def try_search_action(
        self, state: StateToken, action: ActionInput, budget: BridgeBudget
    ) -> TryActionResult:
        """Commit a lightweight child for the internal hot search loop.

        The token retains the exact action lineage and Agda's current open-goal
        observations, but deliberately omits the expensive complete Stage 1
        snapshot.  It is not part of ``KernelSessionV1`` and must not cross the
        bridge serialization boundary.
        """

        return self._try_action(state, action, budget, complete_child=False)

    def _try_action(
        self,
        state: StateToken,
        action: ActionInput,
        budget: BridgeBudget,
        *,
        complete_child: bool,
    ) -> TryActionResult:
        record = self._activate(state, budget)
        if action.commit and len(self._states) >= budget.artifact_count:
            raise self._error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "bridge-state-count-exhausted",
                "committed state count reached the task artifact budget",
            )
        before = self.transport.cost.copy()
        adapter = adapter_for_version(self.project.toolchain.version)
        source = self._source_for(state.module_id)
        if action.kind == "case-split":
            split = self.case_split(
                state,
                action.local_name or "",
                action.interaction_id,
                budget,
                commit=action.commit,
            )
            return TryActionResult(
                transition=split.transition,
                accepted=split.accepted,
                preview="\n".join(split.clauses) if split.clauses else None,
                generated_goals=split.generated_goals,
                edge=None,
                rejection_code=split.rejection_code,
            )

        preexisting = {goal.interaction_id.value for goal in record.state.goals}
        if action.kind == "check-term":
            command_text = adapter.check_term(
                action.interaction_id.value, action.expression
            )
        elif action.kind == "give":
            command_text = adapter.give(action.interaction_id.value, action.expression)
        else:
            command_text = adapter.refine(
                action.interaction_id.value, action.expression
            )
        speculative_transaction = (
            action.kind == "refine"
            and not action.commit
            and self.transport.transactional_commands
        )
        command_id, response = self.transport.command(
            source,
            command_text,
            transactional=speculative_transaction,
        )
        diagnostics = diagnostics_from_response(
            response,
            primary_range=self._goal_range(record.state, action.interaction_id),
            project_root=self.project.project_root,
        )
        if action.kind == "check-term":
            candidate = adapter.candidate(response)
            accepted = candidate.accepted
            preview = candidate.elaborated_term
            post_observations: tuple[GoalObservation, ...] = ()
            if accepted and action.commit:
                command_id, response = self.transport.command(
                    source,
                    adapter.give(action.interaction_id.value, action.expression),
                )
                diagnostics = diagnostics_from_response(
                    response,
                    primary_range=self._goal_range(record.state, action.interaction_id),
                    project_root=self.project.project_root,
                )
                accepted = first_error(diagnostics) is None
                post_observations = adapter.interaction_points(response)
        elif action.kind == "give":
            accepted = first_error(diagnostics) is None
            preview = action.expression if accepted else None
            post_observations = adapter.interaction_points(response)
        else:
            refinement = adapter.refinement(response)
            accepted = refinement.accepted
            preview = refinement.preview
            post_observations = refinement.goals

        generated_observations = tuple(
            goal
            for goal in post_observations
            if goal.interaction_id not in (preexisting - {action.interaction_id.value})
        )
        generated_goals = self._goals_from_observations(generated_observations)
        child: StateToken | None = None
        edge: ProofHyperedge | None = None
        if accepted and action.commit:
            state_goals = self._goals_from_observations(post_observations)
            response_hash = response.raw_sha256
            semantic_parent = record.state.structural_hash
            provisional = ProofState(
                environment_id=self.project.environment_id,
                source_revision=self.project.source_revision,
                module_id=state.module_id,
                focused_interaction=(
                    state_goals[0].interaction_id if state_goals else None
                ),
                goals=state_goals,
                metas=self._metas_for_goals(state_goals),
                constraints=(),
                dependency_graph=self._dependencies_for_goals(state_goals),
                proof_dag=record.state.proof_dag,
                cost=self.transport.cost.delta(before).to_dict(),
                extraction_capabilities=self._extraction_capabilities(),
            )
            committed_action = ActionInput(
                kind="give" if action.kind == "check-term" else action.kind,
                interaction_id=action.interaction_id,
                expression=action.expression,
                commit=True,
                local_name=action.local_name,
                action_id=action.identity,
            )
            lineage = (*record.lineage, committed_action)
            child = self._register_state(provisional, lineage)
            # The accepted Agda command has already advanced the live process
            # to this provisional child.  Mark it active before completing
            # its observations; otherwise ``inspect_goals`` needlessly reloads
            # the module and replays the entire lineage for every commit.
            self._active_state = child
            completed_state = (
                self.inspect_goals(child, budget).state
                if complete_child
                else provisional
            )
            proof_edge = ProofEdge(
                action_id=action.identity,
                parent_state_hash=semantic_parent,
                # The edge points at the complete child before the edge itself
                # is appended, avoiding a recursive hash while preserving all
                # bridge-observable state.
                child_state_hashes=(completed_state.structural_hash,),
                verifier_response_sha256=response_hash,
                cost=self.transport.cost.delta(before).to_dict(),
            )
            child_state = replace(
                completed_state,
                proof_dag=(*record.state.proof_dag, proof_edge),
                cost=self.transport.cost.delta(before).to_dict(),
            )
            corrected = self._replace_state(child, child_state, lineage)
            child = corrected
            edge = ProofHyperedge(
                action_id=action.identity,
                parent=state,
                children=(corrected,),
                generated_goals=generated_goals,
                verifier_response_sha256=response_hash,
            )
            self._active_state = child
        elif action.kind == "check-term" or speculative_transaction:
            # Cmd_goal_type_context Check is observational.  Preserve the
            # parent without paying for a module reload on every candidate.
            # The Agda 2.8 adapter gives speculative refinements the same
            # property by restoring both of Agda's interaction states.
            self._active_state = state
        else:
            non_mutating_intro = next(
                (
                    item
                    for item in diagnostics
                    if item.code
                    in {
                        "agda-intro-constructor-unknown",
                        "agda-intro-not-found",
                    }
                ),
                None,
            )
            if action.kind == "refine" and not action.expression and non_mutating_intro:
                # Agda's intro command only reports these two outcomes; it
                # does not call give/refine and therefore leaves the proof
                # state untouched.  Avoid an otherwise needless full replay.
                self._active_state = state
            else:
                self._rollback_to(state, budget)
        rejection = None
        if not accepted:
            diagnostic = first_error(diagnostics)
            if diagnostic is None:
                diagnostic = next(
                    (
                        item
                        for item in diagnostics
                        if item.code.startswith("agda-intro-")
                    ),
                    None,
                )
            rejection = diagnostic.code if diagnostic else "agda-no-acceptance-response"
        return TryActionResult(
            transition=self._transition(
                command_id,
                parent=state,
                child=child,
                diagnostics=diagnostics,
                cost=self.transport.cost.delta(before),
            ),
            accepted=accepted,
            preview=preview,
            generated_goals=generated_goals,
            edge=edge,
            rejection_code=rejection,
        )

    def search_state(self, state: StateToken, budget: BridgeBudget) -> ProofState:
        """Return an internal lightweight state, replaying its lineage if needed."""

        return self._activate(state, budget).state

    def inspect_selected_goals(
        self,
        state: StateToken,
        interaction_ids: tuple[InteractionId, ...],
        budget: BridgeBudget,
    ) -> tuple[Goal, ...]:
        """Inspect only selected interactions for the internal search loop."""

        record = self._activate(state, budget)
        available = {goal.interaction_id.value: goal for goal in record.state.goals}
        adapter = adapter_for_version(self.project.toolchain.version)
        source = self._source_for(state.module_id)
        result: list[Goal] = []
        for interaction_id in interaction_ids:
            shallow = available.get(interaction_id.value)
            if shallow is None:
                continue
            _command_id, response = self.transport.command(
                source, adapter.inspect_goal(interaction_id.value)
            )
            diagnostics = diagnostics_from_response(
                response,
                primary_range=shallow.source_range,
                project_root=self.project.project_root,
            )
            if first_error(diagnostics) is not None:
                continue
            observation = adapter.goal(response)
            if observation is not None:
                result.extend(self._goals_from_observations((observation,)))
        self._active_state = state
        return tuple(result)

    def auto_one(
        self,
        state: StateToken,
        interaction_id: InteractionId,
        budget: BridgeBudget,
    ) -> str | None:
        """Run Agda 2.8's built-in proof search as a measured baseline.

        ``Cmd_autoOne`` commits on success.  The active-state marker is cleared
        unconditionally so a later bridge operation must restore the immutable
        parent token before using it.
        """

        record = self._activate(state, budget)
        if all(goal.interaction_id != interaction_id for goal in record.state.goals):
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "auto-goal-not-open",
                "Agda Auto target is not an open interaction",
            )
        adapter = adapter_for_version(self.project.toolchain.version)
        source = self._source_for(state.module_id)
        try:
            _command_id, response = self.transport.command(
                source, adapter.auto(interaction_id.value)
            )
            diagnostics = diagnostics_from_response(
                response,
                project_root=self.project.project_root,
            )
            if first_error(diagnostics) is not None:
                return None
            return adapter.auto_term(response)
        finally:
            self._active_state = None

    def search_scoped_retrieval(
        self,
        state: StateToken,
        interaction_id: InteractionId,
        budget: BridgeBudget,
        *,
        excluded_names: frozenset[str] = frozenset(),
    ) -> ScopedPremises | None:
        """Read live scope through the explicitly enabled embedded capability.

        Failure with the feature enabled is not permission to fall back to
        exported module contents. The immutable parent is restored in native
        TCM even if resolution or contextual type lookup fails.
        """
        if not self._live_scope_enabled:
            return None
        if self._scope_adapter_hash is None:
            raise self._error(
                BridgeFailure.UNSUPPORTED_CAPABILITY,
                "live-scope-adapter-required",
                "Scoped retrieval requires the built Agda 2.8 embedded adapter",
            )
        record = self._activate(state, budget)
        if all(g.interaction_id != interaction_id for g in record.state.goals):
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "scope-goal-not-open",
                "Scoped retrieval requires an open interaction",
            )
        adapter = adapter_for_version(self.project.toolchain.version)
        _command, response = self.transport.command(
            self._source_for(state.module_id),
            adapter.module_contents(
                interaction_id.value,
                exclusions_payload(
                    excluded_names,
                    include_dependencies=self._scope_dependencies_enabled,
                ),
            ),
            transactional=True,
        )
        diagnostics = diagnostics_from_response(
            response, project_root=self.project.project_root
        )
        diagnostic = first_error(diagnostics)
        if diagnostic is not None:
            raise BridgeError(BridgeFailure.AGDA_REJECTION, diagnostic)
        rows = [e.value for e in response.events if e.kind == "AgdaProverScope"]
        try:
            if len(rows) != 1:
                raise ValueError("missing/duplicate live-scope response")
            return decode_scope(
                rows[0],
                state=state,
                goal_id=interaction_id.value,
                excluded_names=excluded_names,
                adapter_sha256=self._scope_adapter_hash,
                include_dependencies=self._scope_dependencies_enabled,
            )
        except ValueError as error:
            raise self._error(
                BridgeFailure.PROTOCOL_FAILURE,
                "invalid-live-scope-response",
                str(error),
            ) from error

    def search_constructor_candidates(
        self,
        state: StateToken,
        interaction_id: InteractionId,
        type_head: str,
        budget: BridgeBudget,
    ) -> tuple[tuple[str, str], ...]:
        """List a datatype module's constructor names and telescope views."""

        self._activate(state, budget)
        adapter = adapter_for_version(self.project.toolchain.version)
        source = self._source_for(state.module_id)
        _command_id, response = self.transport.command(
            source, adapter.module_contents(interaction_id.value, type_head)
        )
        diagnostics = diagnostics_from_response(
            response,
            project_root=self.project.project_root,
        )
        self._active_state = state
        return (
            ()
            if first_error(diagnostics) is not None
            else adapter.named_contents(response)
        )

    def case_split(
        self,
        state: StateToken,
        subject: str,
        interaction_id: InteractionId,
        budget: BridgeBudget,
        *,
        commit: bool = False,
    ) -> CaseSplitResult:
        if commit:
            raise self._error(
                BridgeFailure.UNSUPPORTED_CAPABILITY,
                "case-split-commit-unsupported",
                "Agda's JSON case response is a source patch and cannot be committed in-place",
            )
        record = self._activate(state, budget)
        if not subject or any(character.isspace() for character in subject):
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "invalid-case-subject",
                "case split subject must be one local name",
            )
        before = self.transport.cost.copy()
        adapter = adapter_for_version(self.project.toolchain.version)
        command_id, response = self.transport.command(
            self._source_for(state.module_id),
            adapter.case_split(interaction_id.value, subject),
        )
        diagnostics = diagnostics_from_response(
            response,
            primary_range=self._goal_range(record.state, interaction_id),
            project_root=self.project.project_root,
        )
        observation = adapter.case(response)
        # Cmd_make_case computes source clauses but does not apply them to the
        # current interaction state.  Keep the parent active so a search can
        # query several independent leaves without reloading and replaying the
        # module after every clause proposal.
        self._active_state = state
        rejection = None
        if not observation.accepted:
            diagnostic = first_error(diagnostics)
            rejection = diagnostic.code if diagnostic else "agda-no-case-response"
        return CaseSplitResult(
            transition=self._transition(
                command_id,
                parent=state,
                child=None,
                diagnostics=diagnostics,
                cost=self.transport.cost.delta(before),
            ),
            accepted=observation.accepted,
            clauses=observation.clauses,
            variant=observation.variant,
            generated_goals=(),
            rejection_code=rejection,
        )

    def check_definition(
        self,
        state: StateToken,
        definition: CandidateDefinition,
        budget: BridgeBudget,
    ) -> CheckDefinitionResult:
        self._activate(state, budget)
        source_path = self.project.source_for(definition.module_id)
        try:
            original = source_path.read_text()
        except (OSError, UnicodeError) as error:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "definition-source-unavailable",
                f"candidate-definition source is no longer readable: {error}",
            ) from error
        patch = SourcePatch(
            self.project.environment_id,
            self.project.source_revision,
            definition.module_id,
            (
                SourceEdit(
                    SourceRange(1, len(original) + 1), original, definition.source
                ),
            ),
        )
        validation = run_fresh_validation(
            self.project,
            patch,
            PolicyProfile("stage1-check-definition"),
            budget,
            cancellation=self._cancellation,
        )
        command_id = self._synthetic_command_id()
        return CheckDefinitionResult(
            self._transition(
                command_id,
                parent=state,
                child=None,
                diagnostics=validation.diagnostics,
                cost=validation.cost,
            ),
            validation.checks,
        )

    def validate_patch(
        self,
        project: ProjectHandle,
        patch: SourcePatch,
        policy: PolicyProfile,
        budget: BridgeBudget,
    ) -> ValidatePatchResult:
        self._check_budget_identity(budget)
        self._ensure_sources_unchanged()
        self._check_project(project, patch.source_revision)
        return run_fresh_validation(
            self.project,
            patch,
            policy,
            budget,
            cancellation=self._cancellation,
        )

    def cancel(self, command: CommandId) -> bool:
        if self._transport is None:
            return False
        cancelled = self._transport.cancel(command)
        if cancelled:
            self._active_state = None
        return cancelled

    def close(self) -> BridgeResourceSummary:
        if self._last_resources is not None:
            return self._last_resources
        self._closed = True
        self._states.clear()
        self._active_state = None
        try:
            if self._transport is None:
                resources = BridgeResourceSummary(
                    process_generation=0,
                    commands=0,
                    process_starts=0,
                    process_restarts=0,
                    cancellations=0,
                    bytes_read=0,
                    bytes_written=0,
                    peak_rss_bytes=0,
                    overlays_removed=0,
                    orphan_processes=0,
                    close_elapsed_ms=0.0,
                )
            else:
                resources = self._transport.close()
        finally:
            try:
                self._cleanup_overlay()
            finally:
                try:
                    if self._runtime_storage is not None:
                        self._runtime_storage.close()
                        self._runtime_storage = None
                finally:
                    if self._runtime is not None:
                        self._runtime.cleanup()
                        self._runtime = None
        self._last_resources = replace(
            resources, overlays_removed=self._overlays_removed
        )
        return self._last_resources

    def _check_project(self, handle: ProjectHandle, revision: SourceRevision) -> None:
        if handle != self.project.handle:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "project-handle-mismatch",
                "project handle is not owned by this session",
            )
        if revision != self.project.source_revision:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "source-revision-stale",
                "operation requested a stale source revision",
            )

    def _check_budget_identity(self, budget: BridgeBudget) -> None:
        if self._budget is not budget:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "budget-object-mismatch",
                "all operations in one Stage 1 session must share one budget object",
            )

    def _ensure_sources_unchanged(self) -> None:
        for source in self.project.sources:
            try:
                unchanged = source.path.is_file()
                if unchanged:
                    content = source.path.read_bytes()
                    charge_io(len(content))
                    unchanged = hashlib.sha256(content).hexdigest() == source.sha256
            except OSError:
                unchanged = False
            if not unchanged:
                self._active_state = None
                raise self._error(
                    BridgeFailure.STALE_TOKEN,
                    "source-snapshot-changed",
                    f"resolved source changed after OpenProject: {source.module.name}",
                )

    def _validate_token(self, token: StateToken) -> _StateRecord:
        if token.environment_id != self.project.environment_id:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "state-environment-stale",
                "state token belongs to another environment",
            )
        if token.source_revision != self.project.source_revision:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "state-revision-stale",
                "state token belongs to another source revision",
            )
        if (
            not self.transport.is_open
            or token.process_generation != self.transport.process_generation
        ):
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "state-generation-stale",
                "state token belongs to a terminated Agda process generation",
            )
        record = self._states.get(token.sequence)
        if record is None or record.state.structural_hash != token.structural_hash:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "state-token-unknown",
                "state token is unknown or structurally inconsistent",
            )
        return record

    def _activate(self, token: StateToken, budget: BridgeBudget) -> _StateRecord:
        self._check_budget_identity(budget)
        self._ensure_sources_unchanged()
        record = self._validate_token(token)
        if self._active_state == token:
            return record
        source = self._source_for(token.module_id)
        adapter = adapter_for_version(self.project.toolchain.version)
        _, loaded = self.transport.command(
            source, adapter.load(source, self.project.options)
        )
        diagnostics = diagnostics_from_response(
            loaded, project_root=self.project.project_root
        )
        if error := first_error(diagnostics):
            self.transport.close()
            raise BridgeError(BridgeFailure.LOAD_FAILURE, error)
        for action in record.lineage:
            if action.kind == "give":
                command = adapter.give(action.interaction_id.value, action.expression)
            elif action.kind == "refine":
                command = adapter.refine(action.interaction_id.value, action.expression)
            else:
                self.transport.close()
                raise self._error(
                    BridgeFailure.INTERNAL_INVARIANT,
                    "unreplayable-state-action",
                    f"committed state contains unreplayable action {action.kind}",
                )
            _, replay = self.transport.command(source, command)
            replay_diagnostics = diagnostics_from_response(
                replay, project_root=self.project.project_root
            )
            if first_error(replay_diagnostics) is not None:
                self.transport.close()
                raise self._error(
                    BridgeFailure.INTERNAL_INVARIANT,
                    "transaction-replay-failed",
                    "could not restore a committed parent state; session was poisoned",
                )
        self.transport.cost.add(rollback_replays=1, module_loads=1)
        self._active_state = token
        return record

    def _rollback_to(self, state: StateToken, budget: BridgeBudget) -> None:
        self._active_state = None
        try:
            self._activate(state, budget)
        except BaseException:
            if self._transport is not None:
                self._transport.close()
            self._active_state = None
            raise

    def _state_from_observations(
        self,
        module: ModuleId,
        observations: tuple[GoalObservation, ...],
        *,
        constraints: tuple[Constraint, ...] = (),
        additional_metas: tuple[Meta, ...] = (),
        proof_dag: tuple[ProofEdge, ...] = (),
        cost: dict[str, int | float],
        complete: bool = False,
    ) -> ProofState:
        goals = self._goals_from_observations(observations, constraints=constraints)
        return ProofState(
            environment_id=self.project.environment_id,
            source_revision=self.project.source_revision,
            module_id=module,
            focused_interaction=goals[0].interaction_id if goals else None,
            goals=goals,
            metas=(*self._metas_for_goals(goals), *additional_metas),
            constraints=constraints,
            dependency_graph=self._dependencies_for_goals(goals, constraints),
            proof_dag=proof_dag,
            cost=cost,
            extraction_capabilities=self._extraction_capabilities(complete=complete),
        )

    def _goals_from_observations(
        self,
        observations: tuple[GoalObservation, ...],
        *,
        constraints: tuple[Constraint, ...] = (),
    ) -> tuple[Goal, ...]:
        constraint_ids = tuple(item.constraint_id for item in constraints)
        goals: list[Goal] = []
        for observation in observations:
            binders = tuple(
                Binder(
                    binder_id=stable_hash(
                        {
                            "environment": self.project.environment_id.value,
                            "interaction": observation.interaction_id,
                            "position": position,
                            "name": entry.original_name,
                            "type": entry.type_text,
                        }
                    ),
                    debruijn_index=len(observation.context) - position - 1,
                    suggested_name=entry.reified_name,
                    type=TermView(entry.type_text),
                    hiding="unknown",
                    relevance="unknown",
                    quantity="unknown",
                    modality="unknown",
                    origin="agda-2.8-interaction-context",
                    instance_status="unknown",
                    in_scope=entry.in_scope,
                )
                for position, entry in enumerate(observation.context)
            )
            goals.append(
                Goal(
                    interaction_id=InteractionId(observation.interaction_id),
                    meta_id=MetaId(f"interaction:{observation.interaction_id}"),
                    telescope=binders,
                    target=TermView(observation.target),
                    constraint_ids=constraint_ids,
                    boundary=observation.boundary,
                    source_range=SourceRange(
                        observation.source_range.start,
                        observation.source_range.end,
                        self._root_source_name(),
                    ),
                )
            )
        return tuple(sorted(goals, key=lambda goal: goal.interaction_id.value))

    @staticmethod
    def _metas_for_goals(goals: tuple[Goal, ...]) -> tuple[Meta, ...]:
        return tuple(
            Meta(
                meta_id=goal.meta_id,
                type=goal.target,
                context=goal.telescope,
                status="open",
                blockers=goal.blockers,
                interaction_id=goal.interaction_id,
                source_range=goal.source_range,
            )
            for goal in goals
        )

    def _root_source_name(self) -> str:
        source = self.project.source_for(self.project.root_module)
        return (
            source.relative_to(self.project.project_root).as_posix()
            if source.is_relative_to(self.project.project_root)
            else self.project.root_source.name
        )

    @staticmethod
    def _dependencies_for_goals(
        goals: tuple[Goal, ...], constraints: tuple[Constraint, ...] = ()
    ) -> tuple[DependencyEdge, ...]:
        edges = [
            DependencyEdge(
                f"goal:{goal.interaction_id.value}",
                f"meta:{goal.meta_id.value}",
                "goal-meta",
            )
            for goal in goals
        ]
        edges.extend(
            DependencyEdge(
                f"goal:{goal.interaction_id.value}",
                f"constraint:{constraint.constraint_id}",
                "goal-constraint",
            )
            for goal in goals
            for constraint in constraints
            if constraint.constraint_id in goal.constraint_ids
        )
        return tuple(
            sorted(edges, key=lambda edge: (edge.source, edge.target, edge.kind))
        )

    @staticmethod
    def _extraction_capabilities(*, complete: bool = False) -> tuple[str, ...]:
        capabilities = (
            "binder-display-name",
            "binder-scope-visibility",
            "binder-type-rendering",
            "goal-boundary-rendering",
            "goal-source-range",
            "goal-target-rendering",
            "interaction-meta-identity",
            "invisible-meta-identity",
            "invisible-meta-source-range",
            "invisible-meta-type-rendering",
            "rendered-constraints",
        )
        return (
            (*capabilities, "complete-json-observation") if complete else capabilities
        )

    def _register_state(
        self, state: ProofState, lineage: tuple[ActionInput, ...]
    ) -> StateToken:
        if (
            self._budget is not None
            and len(self._states) >= self._budget.artifact_count
        ):
            raise self._error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "bridge-state-count-exhausted",
                "state count reached the task artifact budget",
            )
        self._state_sequence += 1
        token = state.token(
            process_generation=self.transport.process_generation,
            sequence=self._state_sequence,
        )
        self._states[token.sequence] = _StateRecord(state, lineage)
        return token

    def _replace_state(
        self, token: StateToken, state: ProofState, lineage: tuple[ActionInput, ...]
    ) -> StateToken:
        del self._states[token.sequence]
        self._state_sequence += 1
        corrected = state.token(
            process_generation=self.transport.process_generation,
            sequence=self._state_sequence,
        )
        self._states[corrected.sequence] = _StateRecord(state, lineage)
        return corrected

    def _transition(
        self,
        command_id: CommandId,
        *,
        parent: StateToken | None,
        child: StateToken | None,
        diagnostics: tuple[BridgeDiagnostic, ...],
        cost: BridgeCost,
    ) -> StateTransition:
        return StateTransition(
            command_id=command_id,
            environment_id=self.project.environment_id,
            source_revision=self.project.source_revision,
            process_generation=self.transport.process_generation,
            parent_state=parent,
            child_state=child,
            committed=child is not None,
            diagnostics=diagnostics,
            cost=cost,
        )

    def _synthetic_command_id(self) -> CommandId:
        active = self.transport.active_command
        if active is not None:
            return active
        # Validation is a bridge operation but not an interaction-transport command.
        return CommandId("0000000000000000", max(1, self.transport.cost.commands + 1))

    @staticmethod
    def _goal_range(
        state: ProofState, interaction_id: InteractionId
    ) -> SourceRange | None:
        return next(
            (
                goal.source_range
                for goal in state.goals
                if goal.interaction_id == interaction_id
            ),
            None,
        )

    @staticmethod
    def _error(failure: BridgeFailure, code: str, message: str) -> BridgeError:
        return BridgeError(
            failure,
            BridgeDiagnostic(
                code=code,
                phase=(
                    DiagnosticPhase.RESOURCE
                    if failure
                    in {
                        BridgeFailure.TIMEOUT,
                        BridgeFailure.CANCELLED,
                        BridgeFailure.RESOURCE_EXHAUSTED,
                    }
                    else DiagnosticPhase.INTERNAL
                ),
                severity="error",
                message=message,
            ),
        )
