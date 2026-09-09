"""Typed requests and results for every Stage 1 kernel operation."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path
from typing import Any, Literal, TypeAlias

from .contracts import (
    BRIDGE_SCHEMA_VERSION,
    BridgeCost,
    BridgeDiagnostic,
    BridgeResourceSummary,
    CapabilityManifest,
    CommandId,
    EnvironmentId,
    InteractionId,
    ModuleId,
    ProjectHandle,
    SourceRange,
    SourceRevision,
    StateToken,
    stable_hash,
)
from .proof_state import Constraint, Goal, ProofState, TermView

DEFAULT_AGDA_OPTIONS = ("--without-K", "--exact-split")


def _mapping(value: object, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or not all(isinstance(key, str) for key in value):
        raise ValueError(f"{name} must be an object")
    return value


def _list(value: object, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be an array")
    return value


def _keys(value: Mapping[str, Any], expected: set[str], name: str) -> None:
    if set(value) != expected:
        raise ValueError(
            f"malformed {name}; unknown={sorted(set(value) - expected)}, "
            f"missing={sorted(expected - set(value))}"
        )


def _boolean(value: object, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be Boolean")
    return value


def _integer(value: object, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an integer")
    return value


def _text(value: object, name: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be text")
    return value


def _optional_text(value: object, name: str) -> str | None:
    return None if value is None else _text(value, name)


class Operation(StrEnum):
    OPEN_PROJECT = "open-project"
    LOAD_MODULE = "load-module"
    INSPECT_GOALS = "inspect-goals"
    INFER = "infer"
    NORMALIZE = "normalize"
    TRY_ACTION = "try-action"
    CASE_SPLIT = "case-split"
    CHECK_DEFINITION = "check-definition"
    VALIDATE_PATCH = "validate-patch"
    CLOSE = "close"


@dataclass(frozen=True)
class TermInput:
    rendered: str
    representation: Literal["agda-rendered-v1"] = "agda-rendered-v1"

    def __post_init__(self) -> None:
        if self.representation != "agda-rendered-v1":
            raise ValueError("unsupported term-input representation")
        if (
            not isinstance(self.rendered, str)
            or not self.rendered
            or len(self.rendered.encode()) > 1_048_576
        ):
            raise ValueError("rendered term must be nonempty and bounded")

    def to_dict(self) -> dict[str, str]:
        return {"representation": self.representation, "rendered": self.rendered}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> TermInput:
        if set(value) != {"representation", "rendered"}:
            raise ValueError("malformed term input")
        return cls(
            _text(value["rendered"], "rendered term"),
            _text(value["representation"], "term representation"),  # type: ignore[arg-type]
        )


class ReductionPolicy(StrEnum):
    AS_IS = "as-is"
    SIMPLIFIED = "simplified"
    NORMAL = "normal"
    HEAD_NORMAL = "head-normal"
    IGNORE_ABSTRACT = "ignore-abstract"


@dataclass(frozen=True)
class ActionInput:
    kind: Literal["check-term", "give", "refine", "case-split"]
    interaction_id: InteractionId
    expression: str
    commit: bool = False
    local_name: str | None = None
    action_id: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.kind, str) or not isinstance(self.expression, str):
            raise ValueError("action kind and expression must be text")
        if self.kind not in {"check-term", "give", "refine", "case-split"}:
            raise ValueError(f"unsupported action kind: {self.kind}")
        if len(self.expression.encode()) > 1_048_576:
            raise ValueError("action expression exceeds the bridge limit")
        if self.kind == "case-split" and not self.local_name:
            raise ValueError("case-split actions require one local name")
        if self.local_name is not None and (
            not self.local_name
            or any(character.isspace() for character in self.local_name)
        ):
            raise ValueError("action local name must be one token")
        if self.action_id is not None and len(self.action_id.encode()) > 256:
            raise ValueError("action id is too long")
        if not isinstance(self.commit, bool):
            raise ValueError("action commit flag must be Boolean")

    @property
    def identity(self) -> str:
        return self.action_id or stable_hash(
            {
                "kind": self.kind,
                "interaction_id": self.interaction_id.value,
                "expression": self.expression,
                "commit": self.commit,
                "local_name": self.local_name,
            }
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "interaction_id": self.interaction_id.value,
            "expression": self.expression,
            "commit": self.commit,
            "local_name": self.local_name,
            "action_id": self.identity,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ActionInput:
        if set(value) != {
            "kind",
            "interaction_id",
            "expression",
            "commit",
            "local_name",
            "action_id",
        }:
            raise ValueError("malformed action input")
        if not isinstance(value["commit"], bool):
            raise ValueError("action commit flag must be Boolean")
        local = value["local_name"]
        decoded = cls(
            kind=_text(value["kind"], "action kind"),  # type: ignore[arg-type]
            interaction_id=InteractionId(
                _integer(value["interaction_id"], "action interaction id")
            ),
            expression=_text(value["expression"], "action expression"),
            commit=value["commit"],
            local_name=_optional_text(local, "action local name"),
        )
        encoded_id = _text(value["action_id"], "action id")
        if encoded_id == decoded.identity:
            return decoded
        return cls(
            decoded.kind,
            decoded.interaction_id,
            decoded.expression,
            decoded.commit,
            decoded.local_name,
            encoded_id,
        )


@dataclass(frozen=True)
class SourceEdit:
    source_range: SourceRange
    original: str
    replacement: str

    def __post_init__(self) -> None:
        if not isinstance(self.original, str) or not isinstance(self.replacement, str):
            raise ValueError("source edit content must be text")
        if len(self.original.encode()) > 16_777_216:
            raise ValueError("source edit original text is too large")
        if len(self.replacement.encode()) > 16_777_216:
            raise ValueError("source edit replacement text is too large")

    def to_dict(self) -> dict[str, Any]:
        return {
            "source_range": self.source_range.to_dict(),
            "original": self.original,
            "replacement": self.replacement,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> SourceEdit:
        if set(value) != {"source_range", "original", "replacement"}:
            raise ValueError("malformed source edit")
        source_range = value["source_range"]
        if not isinstance(source_range, Mapping):
            raise ValueError("source edit range must be an object")
        return cls(
            SourceRange.from_dict(source_range),
            _text(value["original"], "source edit original"),
            _text(value["replacement"], "source edit replacement"),
        )


@dataclass(frozen=True)
class SourcePatch:
    environment_id: EnvironmentId
    source_revision: SourceRevision
    module_id: ModuleId
    edits: tuple[SourceEdit, ...]
    patch_id: str | None = None

    def __post_init__(self) -> None:
        if not self.edits:
            raise ValueError("a source patch requires at least one edit")
        ordered = sorted(self.edits, key=lambda edit: edit.source_range.start)
        for previous, current in zip(ordered, ordered[1:], strict=False):
            if previous.source_range.end > current.source_range.start:
                raise ValueError("source patch edits overlap")
        if self.patch_id is not None and (
            len(self.patch_id) != 64
            or any(character not in "0123456789abcdef" for character in self.patch_id)
        ):
            raise ValueError("patch id must be SHA-256")

    @property
    def identity(self) -> str:
        return self.patch_id or stable_hash(
            {
                "environment_id": self.environment_id.value,
                "source_revision": self.source_revision.value,
                "module_id": self.module_id.to_dict(),
                "edits": [edit.to_dict() for edit in self.edits],
            }
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "module_id": self.module_id.to_dict(),
            "edits": [edit.to_dict() for edit in self.edits],
            "patch_id": self.identity,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> SourcePatch:
        _keys(
            value,
            {
                "environment_id",
                "source_revision",
                "module_id",
                "edits",
                "patch_id",
            },
            "source patch",
        )
        environment = EnvironmentId(_text(value["environment_id"], "environment id"))
        revision = SourceRevision(_text(value["source_revision"], "source revision"))
        module = ModuleId.from_dict(_mapping(value["module_id"], "patch module"))
        edits = tuple(
            SourceEdit.from_dict(_mapping(item, "source edit"))
            for item in _list(value["edits"], "source edits")
        )
        expected = cls(environment, revision, module, edits).identity
        if expected != value["patch_id"]:
            raise ValueError("source patch checksum mismatch")
        return cls(environment, revision, module, edits)


@dataclass(frozen=True)
class PolicyProfile:
    name: str
    allow_new_postulates: bool = False
    allow_unsafe_options: bool = False
    allow_import_changes: bool = False
    require_safe: bool = False

    def __post_init__(self) -> None:
        if (
            not isinstance(self.name, str)
            or not self.name
            or len(self.name.encode()) > 256
        ):
            raise ValueError("policy profile name must be nonempty and bounded")
        if not all(
            isinstance(value, bool)
            for value in (
                self.allow_new_postulates,
                self.allow_unsafe_options,
                self.allow_import_changes,
                self.require_safe,
            )
        ):
            raise ValueError("policy switches must be Boolean")

    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "allow_new_postulates": self.allow_new_postulates,
            "allow_unsafe_options": self.allow_unsafe_options,
            "allow_import_changes": self.allow_import_changes,
            "require_safe": self.require_safe,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> PolicyProfile:
        _keys(
            value,
            {
                "name",
                "allow_new_postulates",
                "allow_unsafe_options",
                "allow_import_changes",
                "require_safe",
            },
            "policy profile",
        )
        boolean_fields = (
            "allow_new_postulates",
            "allow_unsafe_options",
            "allow_import_changes",
            "require_safe",
        )
        if not all(isinstance(value[name], bool) for name in boolean_fields):
            raise ValueError("policy switches must be Boolean")
        return cls(
            _text(value["name"], "policy name"),
            _boolean(value["allow_new_postulates"], "allow new postulates"),
            _boolean(value["allow_unsafe_options"], "allow unsafe options"),
            _boolean(value["allow_import_changes"], "allow import changes"),
            _boolean(value["require_safe"], "require safe"),
        )


@dataclass(frozen=True)
class CandidateDefinition:
    module_id: ModuleId
    source: str

    def __post_init__(self) -> None:
        if (
            not isinstance(self.source, str)
            or not self.source
            or len(self.source.encode()) > 64 * 1024 * 1024
        ):
            raise ValueError("candidate definition source must be nonempty and bounded")

    def to_dict(self) -> dict[str, Any]:
        return {"module_id": self.module_id.to_dict(), "source": self.source}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> CandidateDefinition:
        _keys(value, {"module_id", "source"}, "candidate definition")
        return cls(
            ModuleId.from_dict(_mapping(value["module_id"], "definition module")),
            _text(value["source"], "candidate source"),
        )


@dataclass(frozen=True)
class OpenProjectRequest:
    source_file: Path
    project_root: Path | None = None
    executable: str = "agda"
    options: tuple[str, ...] = DEFAULT_AGDA_OPTIONS
    library_file: Path | None = None
    operation: Operation = Operation.OPEN_PROJECT
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class LoadModuleRequest:
    project: ProjectHandle
    module: ModuleId
    expected_revision: SourceRevision
    operation: Operation = Operation.LOAD_MODULE
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class InspectGoalsRequest:
    state: StateToken
    operation: Operation = Operation.INSPECT_GOALS
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class InferRequest:
    state: StateToken
    term: TermInput
    interaction_id: InteractionId | None = None
    operation: Operation = Operation.INFER
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class NormalizeRequest:
    state: StateToken
    term: TermInput
    policy: ReductionPolicy
    interaction_id: InteractionId | None = None
    operation: Operation = Operation.NORMALIZE
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class TryActionRequest:
    state: StateToken
    action: ActionInput
    operation: Operation = Operation.TRY_ACTION
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class CaseSplitRequest:
    state: StateToken
    subject: str
    interaction_id: InteractionId
    commit: bool = False
    operation: Operation = Operation.CASE_SPLIT
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class CheckDefinitionRequest:
    state: StateToken
    definition: CandidateDefinition
    operation: Operation = Operation.CHECK_DEFINITION
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class ValidatePatchRequest:
    project: ProjectHandle
    patch: SourcePatch
    policy: PolicyProfile
    operation: Operation = Operation.VALIDATE_PATCH
    schema_version: str = BRIDGE_SCHEMA_VERSION


@dataclass(frozen=True)
class CloseRequest:
    operation: Operation = Operation.CLOSE
    schema_version: str = BRIDGE_SCHEMA_VERSION


BridgeRequest: TypeAlias = (
    OpenProjectRequest
    | LoadModuleRequest
    | InspectGoalsRequest
    | InferRequest
    | NormalizeRequest
    | TryActionRequest
    | CaseSplitRequest
    | CheckDefinitionRequest
    | ValidatePatchRequest
    | CloseRequest
)


@dataclass(frozen=True)
class StateTransition:
    command_id: CommandId
    environment_id: EnvironmentId
    source_revision: SourceRevision
    process_generation: int
    parent_state: StateToken | None
    child_state: StateToken | None
    committed: bool
    diagnostics: tuple[BridgeDiagnostic, ...]
    cost: BridgeCost

    def __post_init__(self) -> None:
        if self.process_generation < 1:
            raise ValueError("transition process generation must be positive")
        if self.committed != (self.child_state is not None):
            raise ValueError("only committed transitions may expose a child state")
        for token in (self.parent_state, self.child_state):
            if token is None:
                continue
            if token.environment_id != self.environment_id:
                raise ValueError("transition token belongs to another environment")
            if token.source_revision != self.source_revision:
                raise ValueError("transition token belongs to another revision")
            if token.process_generation != self.process_generation:
                raise ValueError(
                    "transition token belongs to another process generation"
                )

    def to_dict(self) -> dict[str, Any]:
        return {
            "command_id": self.command_id.value,
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "process_generation": self.process_generation,
            "parent_state": self.parent_state.to_dict() if self.parent_state else None,
            "child_state": self.child_state.to_dict() if self.child_state else None,
            "committed": self.committed,
            "diagnostics": [item.to_dict() for item in self.diagnostics],
            "cost": self.cost.to_dict(),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> StateTransition:
        _keys(
            value,
            {
                "command_id",
                "environment_id",
                "source_revision",
                "process_generation",
                "parent_state",
                "child_state",
                "committed",
                "diagnostics",
                "cost",
            },
            "state transition",
        )
        parent = value["parent_state"]
        child = value["child_state"]
        diagnostics = _list(value["diagnostics"], "transition diagnostics")
        if not isinstance(value["committed"], bool):
            raise ValueError("transition committed flag must be Boolean")
        return cls(
            CommandId.parse(_text(value["command_id"], "command id")),
            EnvironmentId(_text(value["environment_id"], "environment id")),
            SourceRevision(_text(value["source_revision"], "source revision")),
            _integer(value["process_generation"], "process generation"),
            StateToken.from_dict(_mapping(parent, "parent state"))
            if parent is not None
            else None,
            StateToken.from_dict(_mapping(child, "child state"))
            if child is not None
            else None,
            value["committed"],
            tuple(
                BridgeDiagnostic.from_dict(_mapping(item, "diagnostic"))
                for item in diagnostics
            ),
            BridgeCost.from_dict(_mapping(value["cost"], "transition cost")),
        )


@dataclass(frozen=True)
class OpenProjectResult:
    project: ProjectHandle
    environment_id: EnvironmentId
    source_revision: SourceRevision
    root_module: ModuleId
    capabilities: CapabilityManifest
    source_count: int
    module_graph: tuple[tuple[str, tuple[str, ...]], ...]
    diagnostics: tuple[BridgeDiagnostic, ...]
    cost: BridgeCost
    schema_version: str = BRIDGE_SCHEMA_VERSION

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "operation": Operation.OPEN_PROJECT.value,
            "project": self.project.to_dict(),
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "root_module": self.root_module.to_dict(),
            "capabilities": self.capabilities.to_dict(),
            "source_count": self.source_count,
            "module_graph": [
                {"module": module, "imports": list(imports)}
                for module, imports in self.module_graph
            ],
            "diagnostics": [item.to_dict() for item in self.diagnostics],
            "cost": self.cost.to_dict(),
        }


@dataclass(frozen=True)
class LoadModuleResult:
    transition: StateTransition
    module: ModuleId
    signature: tuple[str, ...]
    state: ProofState

    def __post_init__(self) -> None:
        if self.transition.child_state is None:
            raise ValueError("successful load must return a state token")
        if self.transition.child_state.structural_hash != self.state.structural_hash:
            raise ValueError("load token does not identify its proof state")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.LOAD_MODULE.value,
            "transition": self.transition.to_dict(),
            "module": self.module.to_dict(),
            "signature": list(self.signature),
            "state": self.state.to_dict(),
        }


@dataclass(frozen=True)
class InspectGoalsResult:
    transition: StateTransition
    state: ProofState

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.INSPECT_GOALS.value,
            "transition": self.transition.to_dict(),
            "state": self.state.to_dict(),
        }


@dataclass(frozen=True)
class InferResult:
    transition: StateTransition
    inferred_type: TermView | None
    constraints: tuple[Constraint, ...]
    accepted: bool

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.INFER.value,
            "transition": self.transition.to_dict(),
            "accepted": self.accepted,
            "inferred_type": self.inferred_type.to_dict()
            if self.inferred_type
            else None,
            "constraints": [item.to_dict() for item in self.constraints],
        }


@dataclass(frozen=True)
class NormalizeResult:
    transition: StateTransition
    normal_form: TermView | None
    complete: bool
    blockers: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.NORMALIZE.value,
            "transition": self.transition.to_dict(),
            "normal_form": self.normal_form.to_dict() if self.normal_form else None,
            "complete": self.complete,
            "blockers": list(self.blockers),
        }


@dataclass(frozen=True)
class ProofHyperedge:
    action_id: str
    parent: StateToken
    children: tuple[StateToken, ...]
    generated_goals: tuple[Goal, ...]
    verifier_response_sha256: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "action_id": self.action_id,
            "parent": self.parent.to_dict(),
            "children": [item.to_dict() for item in self.children],
            "generated_goals": [item.to_dict() for item in self.generated_goals],
            "verifier_response_sha256": self.verifier_response_sha256,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ProofHyperedge:
        _keys(
            value,
            {
                "action_id",
                "parent",
                "children",
                "generated_goals",
                "verifier_response_sha256",
            },
            "proof hyperedge",
        )
        return cls(
            _text(value["action_id"], "edge action id"),
            StateToken.from_dict(_mapping(value["parent"], "edge parent")),
            tuple(
                StateToken.from_dict(_mapping(item, "edge child"))
                for item in _list(value["children"], "edge children")
            ),
            tuple(
                Goal.from_dict(_mapping(item, "generated goal"))
                for item in _list(value["generated_goals"], "generated goals")
            ),
            _text(value["verifier_response_sha256"], "verifier response hash"),
        )


@dataclass(frozen=True)
class TryActionResult:
    transition: StateTransition
    accepted: bool
    preview: str | None
    generated_goals: tuple[Goal, ...]
    edge: ProofHyperedge | None
    rejection_code: str | None = None

    def __post_init__(self) -> None:
        if not self.accepted and self.transition.child_state is not None:
            raise ValueError("rejected action returned a child token")
        if self.edge is not None and not self.accepted:
            raise ValueError("rejected action returned a proof hyperedge")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.TRY_ACTION.value,
            "transition": self.transition.to_dict(),
            "accepted": self.accepted,
            "preview": self.preview,
            "generated_goals": [item.to_dict() for item in self.generated_goals],
            "edge": self.edge.to_dict() if self.edge else None,
            "rejection_code": self.rejection_code,
        }


@dataclass(frozen=True)
class CaseSplitResult:
    transition: StateTransition
    accepted: bool
    clauses: tuple[str, ...]
    variant: str | None
    generated_goals: tuple[Goal, ...]
    rejection_code: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.CASE_SPLIT.value,
            "transition": self.transition.to_dict(),
            "accepted": self.accepted,
            "clauses": list(self.clauses),
            "variant": self.variant,
            "generated_goals": [item.to_dict() for item in self.generated_goals],
            "rejection_code": self.rejection_code,
        }


@dataclass(frozen=True)
class CheckOutcome:
    check: Literal[
        "parse", "scope", "type", "coverage", "positivity", "termination", "metas"
    ]
    passed: bool
    diagnostics: tuple[BridgeDiagnostic, ...] = ()

    def __post_init__(self) -> None:
        if self.check not in {
            "parse",
            "scope",
            "type",
            "coverage",
            "positivity",
            "termination",
            "metas",
        }:
            raise ValueError("invalid validation check name")
        if not isinstance(self.passed, bool):
            raise ValueError("validation check flag must be Boolean")

    def to_dict(self) -> dict[str, Any]:
        return {
            "check": self.check,
            "passed": self.passed,
            "diagnostics": [item.to_dict() for item in self.diagnostics],
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> CheckOutcome:
        _keys(value, {"check", "passed", "diagnostics"}, "check outcome")
        if not isinstance(value["passed"], bool):
            raise ValueError("check passed flag must be Boolean")
        return cls(
            _text(value["check"], "check name"),  # type: ignore[arg-type]
            value["passed"],
            tuple(
                BridgeDiagnostic.from_dict(_mapping(item, "check diagnostic"))
                for item in _list(value["diagnostics"], "check diagnostics")
            ),
        )


@dataclass(frozen=True)
class CheckDefinitionResult:
    transition: StateTransition
    checks: tuple[CheckOutcome, ...]

    @property
    def accepted(self) -> bool:
        return bool(self.checks) and all(item.passed for item in self.checks)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.CHECK_DEFINITION.value,
            "transition": self.transition.to_dict(),
            "accepted": self.accepted,
            "checks": [item.to_dict() for item in self.checks],
        }


@dataclass(frozen=True)
class TrustReport:
    agda_version: str
    agda_binary_sha256: str
    environment_id: EnvironmentId
    source_revision: SourceRevision
    patch_id: str
    options: tuple[str, ...]
    imported_artifacts: tuple[tuple[str, str], ...]
    admitted_assumptions: tuple[str, ...]
    policy_profile: str
    sandbox_profile: str
    command: tuple[str, ...]
    exit_status: int | None
    output_sha256: str
    fresh_process: bool
    offline: bool

    def to_dict(self) -> dict[str, Any]:
        return {
            "agda_version": self.agda_version,
            "agda_binary_sha256": self.agda_binary_sha256,
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "patch_id": self.patch_id,
            "options": list(self.options),
            "imported_artifacts": [
                {"path": path, "sha256": digest}
                for path, digest in self.imported_artifacts
            ],
            "admitted_assumptions": list(self.admitted_assumptions),
            "policy_profile": self.policy_profile,
            "sandbox_profile": self.sandbox_profile,
            "command": list(self.command),
            "exit_status": self.exit_status,
            "output_sha256": self.output_sha256,
            "fresh_process": self.fresh_process,
            "offline": self.offline,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> TrustReport:
        expected = {
            "agda_version",
            "agda_binary_sha256",
            "environment_id",
            "source_revision",
            "patch_id",
            "options",
            "imported_artifacts",
            "admitted_assumptions",
            "policy_profile",
            "sandbox_profile",
            "command",
            "exit_status",
            "output_sha256",
            "fresh_process",
            "offline",
        }
        _keys(value, expected, "trust report")
        imported: list[tuple[str, str]] = []
        for raw in _list(value["imported_artifacts"], "imported artifacts"):
            item = _mapping(raw, "imported artifact")
            _keys(item, {"path", "sha256"}, "imported artifact")
            imported.append(
                (
                    _text(item["path"], "imported artifact path"),
                    _text(item["sha256"], "imported artifact hash"),
                )
            )
        if not isinstance(value["fresh_process"], bool) or not isinstance(
            value["offline"], bool
        ):
            raise ValueError("trust process flags must be Boolean")
        exit_status = value["exit_status"]
        if exit_status is not None and (
            not isinstance(exit_status, int) or isinstance(exit_status, bool)
        ):
            raise ValueError("trust exit status must be an integer or null")
        return cls(
            agda_version=_text(value["agda_version"], "Agda version"),
            agda_binary_sha256=_text(value["agda_binary_sha256"], "Agda hash"),
            environment_id=EnvironmentId(
                _text(value["environment_id"], "environment id")
            ),
            source_revision=SourceRevision(
                _text(value["source_revision"], "source revision")
            ),
            patch_id=_text(value["patch_id"], "patch id"),
            options=tuple(
                _text(item, "option") for item in _list(value["options"], "options")
            ),
            imported_artifacts=tuple(imported),
            admitted_assumptions=tuple(
                _text(item, "admitted assumption")
                for item in _list(value["admitted_assumptions"], "assumptions")
            ),
            policy_profile=_text(value["policy_profile"], "policy profile"),
            sandbox_profile=_text(value["sandbox_profile"], "sandbox profile"),
            command=tuple(
                _text(item, "trust command item")
                for item in _list(value["command"], "trust command")
            ),
            exit_status=exit_status,
            output_sha256=_text(value["output_sha256"], "output hash"),
            fresh_process=value["fresh_process"],
            offline=value["offline"],
        )


@dataclass(frozen=True)
class ValidatePatchResult:
    project: ProjectHandle
    patch_id: str
    verified: bool
    checks: tuple[CheckOutcome, ...]
    diagnostics: tuple[BridgeDiagnostic, ...]
    trust_report: TrustReport | None
    cost: BridgeCost

    def __post_init__(self) -> None:
        if self.verified and (
            self.trust_report is None
            or not self.trust_report.fresh_process
            or not all(item.passed for item in self.checks)
        ):
            raise ValueError("verified patch lacks a clean, complete validation")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.VALIDATE_PATCH.value,
            "project": self.project.to_dict(),
            "patch_id": self.patch_id,
            "verified": self.verified,
            "checks": [item.to_dict() for item in self.checks],
            "diagnostics": [item.to_dict() for item in self.diagnostics],
            "trust_report": self.trust_report.to_dict() if self.trust_report else None,
            "cost": self.cost.to_dict(),
        }


@dataclass(frozen=True)
class CloseResult:
    resources: BridgeResourceSummary

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": BRIDGE_SCHEMA_VERSION,
            "operation": Operation.CLOSE.value,
            "resources": self.resources.to_dict(),
        }


BridgeResult: TypeAlias = (
    OpenProjectResult
    | LoadModuleResult
    | InspectGoalsResult
    | InferResult
    | NormalizeResult
    | TryActionResult
    | CaseSplitResult
    | CheckDefinitionResult
    | ValidatePatchResult
    | CloseResult
)


def bridge_result_to_dict(result: BridgeResult) -> dict[str, Any]:
    return result.to_dict()


def bridge_request_to_dict(request: BridgeRequest) -> dict[str, Any]:
    base: dict[str, Any] = {
        "schema_version": BRIDGE_SCHEMA_VERSION,
        "operation": request.operation.value,
    }
    if isinstance(request, OpenProjectRequest):
        base.update(
            {
                "source_file": str(request.source_file),
                "project_root": (
                    str(request.project_root) if request.project_root else None
                ),
                "executable": request.executable,
                "options": list(request.options),
                "library_file": (
                    str(request.library_file) if request.library_file else None
                ),
            }
        )
    elif isinstance(request, LoadModuleRequest):
        base.update(
            {
                "project": request.project.to_dict(),
                "module": request.module.to_dict(),
                "expected_revision": request.expected_revision.value,
            }
        )
    elif isinstance(request, InspectGoalsRequest):
        base["state"] = request.state.to_dict()
    elif isinstance(request, InferRequest):
        base.update(
            {
                "state": request.state.to_dict(),
                "term": request.term.to_dict(),
                "interaction_id": (
                    request.interaction_id.value if request.interaction_id else None
                ),
            }
        )
    elif isinstance(request, NormalizeRequest):
        base.update(
            {
                "state": request.state.to_dict(),
                "term": request.term.to_dict(),
                "policy": request.policy.value,
                "interaction_id": (
                    request.interaction_id.value if request.interaction_id else None
                ),
            }
        )
    elif isinstance(request, TryActionRequest):
        base.update(
            {"state": request.state.to_dict(), "action": request.action.to_dict()}
        )
    elif isinstance(request, CaseSplitRequest):
        base.update(
            {
                "state": request.state.to_dict(),
                "subject": request.subject,
                "interaction_id": request.interaction_id.value,
                "commit": request.commit,
            }
        )
    elif isinstance(request, CheckDefinitionRequest):
        base.update(
            {
                "state": request.state.to_dict(),
                "definition": request.definition.to_dict(),
            }
        )
    elif isinstance(request, ValidatePatchRequest):
        base.update(
            {
                "project": request.project.to_dict(),
                "patch": request.patch.to_dict(),
                "policy": request.policy.to_dict(),
            }
        )
    elif not isinstance(request, CloseRequest):
        raise TypeError(f"unknown bridge request: {type(request).__name__}")
    return base


def bridge_request_from_dict(value: Mapping[str, Any]) -> BridgeRequest:
    if value.get("schema_version") != BRIDGE_SCHEMA_VERSION:
        raise ValueError("unsupported bridge schema version")
    try:
        operation = Operation(_text(value.get("operation"), "bridge operation"))
    except ValueError as error:
        raise ValueError("unknown bridge request operation") from error
    header = {"schema_version", "operation"}
    if operation is Operation.OPEN_PROJECT:
        _keys(
            value,
            header
            | {
                "source_file",
                "project_root",
                "executable",
                "options",
                "library_file",
            },
            "open-project request",
        )
        project_root = value["project_root"]
        library_file = value["library_file"]
        return OpenProjectRequest(
            Path(_text(value["source_file"], "source file")),
            Path(_text(project_root, "project root"))
            if project_root is not None
            else None,
            _text(value["executable"], "executable"),
            tuple(_text(item, "option") for item in _list(value["options"], "options")),
            Path(_text(library_file, "library file"))
            if library_file is not None
            else None,
        )
    if operation is Operation.LOAD_MODULE:
        _keys(
            value,
            header | {"project", "module", "expected_revision"},
            "load-module request",
        )
        return LoadModuleRequest(
            ProjectHandle.from_dict(_mapping(value["project"], "project")),
            ModuleId.from_dict(_mapping(value["module"], "module")),
            SourceRevision(
                _text(value["expected_revision"], "expected source revision")
            ),
        )
    if operation is Operation.INSPECT_GOALS:
        _keys(value, header | {"state"}, "inspect-goals request")
        return InspectGoalsRequest(
            StateToken.from_dict(_mapping(value["state"], "state"))
        )
    if operation in {Operation.INFER, Operation.NORMALIZE}:
        common = header | {"state", "term", "interaction_id"}
        interaction = value.get("interaction_id")
        interaction_id = (
            InteractionId(_integer(interaction, "interaction id"))
            if interaction is not None
            else None
        )
        state = StateToken.from_dict(_mapping(value.get("state"), "state"))
        term = TermInput.from_dict(_mapping(value.get("term"), "term"))
        if operation is Operation.INFER:
            _keys(value, common, "infer request")
            return InferRequest(state, term, interaction_id)
        _keys(value, common | {"policy"}, "normalize request")
        return NormalizeRequest(
            state,
            term,
            ReductionPolicy(_text(value["policy"], "reduction policy")),
            interaction_id,
        )
    if operation is Operation.TRY_ACTION:
        _keys(value, header | {"state", "action"}, "try-action request")
        return TryActionRequest(
            StateToken.from_dict(_mapping(value["state"], "state")),
            ActionInput.from_dict(_mapping(value["action"], "action")),
        )
    if operation is Operation.CASE_SPLIT:
        _keys(
            value,
            header | {"state", "subject", "interaction_id", "commit"},
            "case-split request",
        )
        if not isinstance(value["commit"], bool):
            raise ValueError("case-split commit must be Boolean")
        return CaseSplitRequest(
            StateToken.from_dict(_mapping(value["state"], "state")),
            _text(value["subject"], "case subject"),
            InteractionId(_integer(value["interaction_id"], "interaction id")),
            value["commit"],
        )
    if operation is Operation.CHECK_DEFINITION:
        _keys(
            value,
            header | {"state", "definition"},
            "check-definition request",
        )
        return CheckDefinitionRequest(
            StateToken.from_dict(_mapping(value["state"], "state")),
            CandidateDefinition.from_dict(_mapping(value["definition"], "definition")),
        )
    if operation is Operation.VALIDATE_PATCH:
        _keys(
            value,
            header | {"project", "patch", "policy"},
            "validate-patch request",
        )
        return ValidatePatchRequest(
            ProjectHandle.from_dict(_mapping(value["project"], "project")),
            SourcePatch.from_dict(_mapping(value["patch"], "patch")),
            PolicyProfile.from_dict(_mapping(value["policy"], "policy")),
        )
    _keys(value, header, "close request")
    return CloseRequest()


def _transition(value: Mapping[str, Any]) -> StateTransition:
    return StateTransition.from_dict(_mapping(value["transition"], "transition"))


def bridge_result_from_dict(value: Mapping[str, Any]) -> BridgeResult:
    if value.get("schema_version") != BRIDGE_SCHEMA_VERSION:
        raise ValueError("unsupported bridge schema version")
    try:
        operation = Operation(_text(value.get("operation"), "bridge operation"))
    except ValueError as error:
        raise ValueError("unknown bridge result operation") from error
    header = {"schema_version", "operation"}
    if operation is Operation.OPEN_PROJECT:
        expected = header | {
            "project",
            "environment_id",
            "source_revision",
            "root_module",
            "capabilities",
            "source_count",
            "module_graph",
            "diagnostics",
            "cost",
        }
        _keys(value, expected, "open-project result")
        graph: list[tuple[str, tuple[str, ...]]] = []
        for raw in _list(value["module_graph"], "module graph"):
            item = _mapping(raw, "module graph entry")
            _keys(item, {"module", "imports"}, "module graph entry")
            graph.append(
                (
                    _text(item["module"], "module graph module"),
                    tuple(
                        _text(name, "module import")
                        for name in _list(item["imports"], "module imports")
                    ),
                )
            )
        return OpenProjectResult(
            ProjectHandle.from_dict(_mapping(value["project"], "project")),
            EnvironmentId(_text(value["environment_id"], "environment id")),
            SourceRevision(_text(value["source_revision"], "source revision")),
            ModuleId.from_dict(_mapping(value["root_module"], "root module")),
            CapabilityManifest.from_dict(
                _mapping(value["capabilities"], "capabilities")
            ),
            _integer(value["source_count"], "source count"),
            tuple(graph),
            tuple(
                BridgeDiagnostic.from_dict(_mapping(item, "diagnostic"))
                for item in _list(value["diagnostics"], "diagnostics")
            ),
            BridgeCost.from_dict(_mapping(value["cost"], "cost")),
        )
    if operation is Operation.LOAD_MODULE:
        _keys(
            value,
            header | {"transition", "module", "signature", "state"},
            "load-module result",
        )
        return LoadModuleResult(
            _transition(value),
            ModuleId.from_dict(_mapping(value["module"], "module")),
            tuple(
                _text(item, "signature item")
                for item in _list(value["signature"], "signature")
            ),
            ProofState.from_dict(_mapping(value["state"], "proof state")),
        )
    if operation is Operation.INSPECT_GOALS:
        _keys(
            value,
            header | {"transition", "state"},
            "inspect-goals result",
        )
        return InspectGoalsResult(
            _transition(value),
            ProofState.from_dict(_mapping(value["state"], "proof state")),
        )
    if operation is Operation.INFER:
        _keys(
            value,
            header | {"transition", "accepted", "inferred_type", "constraints"},
            "infer result",
        )
        inferred_type = value["inferred_type"]
        return InferResult(
            _transition(value),
            TermView.from_dict(_mapping(inferred_type, "inferred type"))
            if inferred_type is not None
            else None,
            tuple(
                Constraint.from_dict(_mapping(item, "constraint"))
                for item in _list(value["constraints"], "constraints")
            ),
            _boolean(value["accepted"], "infer accepted"),
        )
    if operation is Operation.NORMALIZE:
        _keys(
            value,
            header | {"transition", "normal_form", "complete", "blockers"},
            "normalize result",
        )
        normal_form = value["normal_form"]
        return NormalizeResult(
            _transition(value),
            TermView.from_dict(_mapping(normal_form, "normal form"))
            if normal_form is not None
            else None,
            _boolean(value["complete"], "normalization complete"),
            tuple(
                _text(item, "normalization blocker")
                for item in _list(value["blockers"], "blockers")
            ),
        )
    if operation is Operation.TRY_ACTION:
        _keys(
            value,
            header
            | {
                "transition",
                "accepted",
                "preview",
                "generated_goals",
                "edge",
                "rejection_code",
            },
            "try-action result",
        )
        edge = value["edge"]
        return TryActionResult(
            _transition(value),
            _boolean(value["accepted"], "action accepted"),
            _optional_text(value["preview"], "action preview"),
            tuple(
                Goal.from_dict(_mapping(item, "generated goal"))
                for item in _list(value["generated_goals"], "generated goals")
            ),
            ProofHyperedge.from_dict(_mapping(edge, "proof edge"))
            if edge is not None
            else None,
            _optional_text(value["rejection_code"], "action rejection code"),
        )
    if operation is Operation.CASE_SPLIT:
        _keys(
            value,
            header
            | {
                "transition",
                "accepted",
                "clauses",
                "variant",
                "generated_goals",
                "rejection_code",
            },
            "case-split result",
        )
        return CaseSplitResult(
            _transition(value),
            _boolean(value["accepted"], "case split accepted"),
            tuple(
                _text(item, "case clause")
                for item in _list(value["clauses"], "clauses")
            ),
            _optional_text(value["variant"], "case variant"),
            tuple(
                Goal.from_dict(_mapping(item, "generated goal"))
                for item in _list(value["generated_goals"], "generated goals")
            ),
            _optional_text(value["rejection_code"], "case rejection code"),
        )
    if operation is Operation.CHECK_DEFINITION:
        _keys(
            value,
            header | {"transition", "accepted", "checks"},
            "check-definition result",
        )
        result = CheckDefinitionResult(
            _transition(value),
            tuple(
                CheckOutcome.from_dict(_mapping(item, "check outcome"))
                for item in _list(value["checks"], "checks")
            ),
        )
        if result.accepted != _boolean(value["accepted"], "definition accepted"):
            raise ValueError("check-definition acceptance checksum mismatch")
        return result
    if operation is Operation.VALIDATE_PATCH:
        _keys(
            value,
            header
            | {
                "project",
                "patch_id",
                "verified",
                "checks",
                "diagnostics",
                "trust_report",
                "cost",
            },
            "validate-patch result",
        )
        trust = value["trust_report"]
        return ValidatePatchResult(
            ProjectHandle.from_dict(_mapping(value["project"], "project")),
            _text(value["patch_id"], "patch id"),
            _boolean(value["verified"], "patch verified"),
            tuple(
                CheckOutcome.from_dict(_mapping(item, "check outcome"))
                for item in _list(value["checks"], "checks")
            ),
            tuple(
                BridgeDiagnostic.from_dict(_mapping(item, "diagnostic"))
                for item in _list(value["diagnostics"], "diagnostics")
            ),
            TrustReport.from_dict(_mapping(trust, "trust report"))
            if trust is not None
            else None,
            BridgeCost.from_dict(_mapping(value["cost"], "cost")),
        )
    _keys(value, header | {"resources"}, "close result")
    return CloseResult(
        BridgeResourceSummary.from_dict(_mapping(value["resources"], "resources"))
    )
