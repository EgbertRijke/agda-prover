"""Faithful, versioned representation of bridge-observable proof state."""

from __future__ import annotations

import hashlib
import math
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Any, Literal

from .contracts import (
    EnvironmentId,
    InteractionId,
    MetaId,
    ModuleId,
    SourceRange,
    SourceRevision,
    StateToken,
    stable_hash,
)

PROOF_STATE_SCHEMA_VERSION = "agdaprover.proof-state.v1"
TERM_VIEW_SCHEMA_VERSION = "agdaprover.agda-term-view.v1"
MAX_TERM_BYTES = 1_048_576
MAX_STATE_ITEMS = 100_000


def _text(value: object, name: str, *, limit: int = MAX_TERM_BYTES) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be text")
    if len(value.encode()) > limit:
        raise ValueError(f"{name} exceeds {limit} bytes")
    return value


def _mapping(value: object, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def _list(value: object, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    if len(value) > MAX_STATE_ITEMS:
        raise ValueError(f"{name} exceeds the state item limit")
    return value


def _integer(value: object, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an integer")
    return value


def _boolean(value: object, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be Boolean")
    return value


def _cost_mapping(value: object, name: str) -> Mapping[str, int | float]:
    mapping = _mapping(value, name)
    if not all(
        isinstance(key, str)
        and isinstance(amount, (int, float))
        and not isinstance(amount, bool)
        and math.isfinite(float(amount))
        and amount >= 0
        for key, amount in mapping.items()
    ):
        raise ValueError(f"{name} must contain finite nonnegative numeric costs")
    return mapping


@dataclass(frozen=True)
class TermView:
    """A bounded Agda rendering.

    The public JSON protocol does not expose Agda's internal term datatype.
    This value is explicitly tagged as a view, so no caller can mistake it for
    a language-neutral term IR.  Its digest detects truncation or corruption.
    """

    text: str
    rendering: str = "agda-pretty-2.8.0"
    schema_version: str = TERM_VIEW_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != TERM_VIEW_SCHEMA_VERSION:
            raise ValueError("unsupported term-view schema version")
        _text(self.text, "term view")
        _text(self.rendering, "term rendering", limit=256)

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.text.encode()).hexdigest()

    def to_dict(self) -> dict[str, str]:
        return {
            "schema_version": self.schema_version,
            "rendering": self.rendering,
            "text": self.text,
            "sha256": self.sha256,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> TermView:
        if set(value) != {"schema_version", "rendering", "text", "sha256"}:
            raise ValueError("malformed term view")
        result = cls(
            text=_text(value["text"], "term view"),
            rendering=_text(value["rendering"], "term rendering", limit=256),
            schema_version=_text(value["schema_version"], "term schema", limit=128),
        )
        if value["sha256"] != result.sha256:
            raise ValueError("term-view checksum mismatch")
        return result


Hiding = Literal["explicit", "implicit", "instance", "unknown"]
Relevance = Literal["relevant", "irrelevant", "shape-irrelevant", "unknown"]
InstanceStatus = Literal["ordinary", "instance", "unknown"]


@dataclass(frozen=True)
class Binder:
    binder_id: str
    debruijn_index: int
    suggested_name: str
    type: TermView
    hiding: Hiding = "unknown"
    relevance: Relevance = "unknown"
    quantity: str = "unknown"
    modality: str = "unknown"
    origin: str = "interaction-context"
    instance_status: InstanceStatus = "unknown"
    in_scope: bool = False

    def __post_init__(self) -> None:
        if not self.binder_id or len(self.binder_id.encode()) > 512:
            raise ValueError("binder id must be nonempty and bounded")
        if self.debruijn_index < 0:
            raise ValueError("de Bruijn indices must be nonnegative")
        for name in ("suggested_name", "quantity", "modality", "origin"):
            _text(getattr(self, name), name, limit=4096)
        if self.hiding not in {"explicit", "implicit", "instance", "unknown"}:
            raise ValueError("invalid binder hiding")
        if self.relevance not in {
            "relevant",
            "irrelevant",
            "shape-irrelevant",
            "unknown",
        }:
            raise ValueError("invalid binder relevance")
        if self.instance_status not in {"ordinary", "instance", "unknown"}:
            raise ValueError("invalid binder instance status")
        if not isinstance(self.in_scope, bool):
            raise ValueError("binder in-scope flag must be Boolean")

    def to_dict(self) -> dict[str, Any]:
        return {
            "binder_id": self.binder_id,
            "debruijn_index": self.debruijn_index,
            "suggested_name": self.suggested_name,
            "type": self.type.to_dict(),
            "hiding": self.hiding,
            "relevance": self.relevance,
            "quantity": self.quantity,
            "modality": self.modality,
            "origin": self.origin,
            "instance_status": self.instance_status,
            "in_scope": self.in_scope,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> Binder:
        expected = {
            "binder_id",
            "debruijn_index",
            "suggested_name",
            "type",
            "hiding",
            "relevance",
            "quantity",
            "modality",
            "origin",
            "instance_status",
            "in_scope",
        }
        if set(value) != expected:
            raise ValueError("malformed binder")
        return cls(
            binder_id=_text(value["binder_id"], "binder id", limit=512),
            debruijn_index=_integer(value["debruijn_index"], "de Bruijn index"),
            suggested_name=_text(
                value["suggested_name"], "binder suggested name", limit=4096
            ),
            type=TermView.from_dict(_mapping(value["type"], "binder type")),
            hiding=_text(value["hiding"], "binder hiding", limit=32),  # type: ignore[arg-type]
            relevance=_text(value["relevance"], "binder relevance", limit=32),  # type: ignore[arg-type]
            quantity=_text(value["quantity"], "binder quantity", limit=4096),
            modality=_text(value["modality"], "binder modality", limit=4096),
            origin=_text(value["origin"], "binder origin", limit=4096),
            instance_status=_text(  # type: ignore[arg-type]
                value["instance_status"], "binder instance status", limit=32
            ),
            in_scope=_boolean(value["in_scope"], "binder in-scope flag"),
        )


@dataclass(frozen=True)
class Goal:
    interaction_id: InteractionId
    meta_id: MetaId
    telescope: tuple[Binder, ...]
    target: TermView
    blockers: tuple[MetaId, ...] = ()
    constraint_ids: tuple[str, ...] = ()
    boundary: tuple[str, ...] = ()
    source_range: SourceRange = SourceRange(0, 0)

    def __post_init__(self) -> None:
        indices = [binder.debruijn_index for binder in self.telescope]
        if len(indices) != len(set(indices)):
            raise ValueError("goal telescope contains duplicate de Bruijn indices")
        if indices and sorted(indices) != list(range(len(indices))):
            raise ValueError("goal telescope de Bruijn indices are not contiguous")
        if len(self.telescope) > MAX_STATE_ITEMS:
            raise ValueError("goal telescope exceeds the state item limit")

    def to_dict(self) -> dict[str, Any]:
        return {
            "interaction_id": self.interaction_id.value,
            "meta_id": self.meta_id.value,
            "telescope": [item.to_dict() for item in self.telescope],
            "target": self.target.to_dict(),
            "blockers": [item.value for item in self.blockers],
            "constraint_ids": list(self.constraint_ids),
            "boundary": list(self.boundary),
            "source_range": self.source_range.to_dict(),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> Goal:
        expected = {
            "interaction_id",
            "meta_id",
            "telescope",
            "target",
            "blockers",
            "constraint_ids",
            "boundary",
            "source_range",
        }
        if set(value) != expected:
            raise ValueError("malformed goal")
        return cls(
            interaction_id=InteractionId(
                _integer(value["interaction_id"], "goal interaction id")
            ),
            meta_id=MetaId(_text(value["meta_id"], "goal meta id", limit=512)),
            telescope=tuple(
                Binder.from_dict(_mapping(item, "binder"))
                for item in _list(value["telescope"], "goal telescope")
            ),
            target=TermView.from_dict(_mapping(value["target"], "goal target")),
            blockers=tuple(
                MetaId(_text(item, "goal blocker", limit=512))
                for item in _list(value["blockers"], "blockers")
            ),
            constraint_ids=tuple(
                _text(item, "goal constraint id")
                for item in _list(value["constraint_ids"], "constraint ids")
            ),
            boundary=tuple(
                _text(item, "goal boundary")
                for item in _list(value["boundary"], "boundary")
            ),
            source_range=SourceRange.from_dict(
                _mapping(value["source_range"], "goal source range")
            ),
        )


@dataclass(frozen=True)
class Meta:
    meta_id: MetaId
    type: TermView
    context: tuple[Binder, ...]
    status: Literal["open", "solved", "blocked", "unknown"]
    solution: TermView | None = None
    blockers: tuple[MetaId, ...] = ()
    interaction_id: InteractionId | None = None
    source_range: SourceRange | None = None

    def __post_init__(self) -> None:
        if self.status not in {"open", "solved", "blocked", "unknown"}:
            raise ValueError("invalid meta status")
        if self.status == "solved" and self.solution is None:
            raise ValueError("solved metas require a solution")
        if self.status == "open" and self.solution is not None:
            raise ValueError("open metas cannot carry a solution")

    def to_dict(self) -> dict[str, Any]:
        return {
            "meta_id": self.meta_id.value,
            "type": self.type.to_dict(),
            "context": [item.to_dict() for item in self.context],
            "status": self.status,
            "solution": self.solution.to_dict() if self.solution else None,
            "blockers": [item.value for item in self.blockers],
            "interaction_id": (
                self.interaction_id.value if self.interaction_id else None
            ),
            "source_range": self.source_range.to_dict() if self.source_range else None,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> Meta:
        expected = {
            "meta_id",
            "type",
            "context",
            "status",
            "solution",
            "blockers",
            "interaction_id",
            "source_range",
        }
        if set(value) != expected:
            raise ValueError("malformed meta")
        solution = value["solution"]
        source_range = value["source_range"]
        return cls(
            meta_id=MetaId(_text(value["meta_id"], "meta id", limit=512)),
            type=TermView.from_dict(_mapping(value["type"], "meta type")),
            context=tuple(
                Binder.from_dict(_mapping(item, "meta binder"))
                for item in _list(value["context"], "meta context")
            ),
            status=_text(value["status"], "meta status", limit=32),  # type: ignore[arg-type]
            solution=(
                TermView.from_dict(_mapping(solution, "meta solution"))
                if solution is not None
                else None
            ),
            blockers=tuple(
                MetaId(_text(item, "meta blocker", limit=512))
                for item in _list(value["blockers"], "meta blockers")
            ),
            interaction_id=(
                InteractionId(_integer(value["interaction_id"], "meta interaction id"))
                if value["interaction_id"] is not None
                else None
            ),
            source_range=(
                SourceRange.from_dict(_mapping(source_range, "meta source range"))
                if source_range is not None
                else None
            ),
        )


@dataclass(frozen=True)
class Constraint:
    constraint_id: str
    kind: str
    rendered: str
    meta_ids: tuple[MetaId, ...] = ()
    name_ids: tuple[str, ...] = ()
    level_variables: tuple[str, ...] = ()
    blockers: tuple[MetaId, ...] = ()

    def __post_init__(self) -> None:
        if not self.constraint_id:
            raise ValueError("constraint id must be nonempty")
        for value in (self.kind, self.rendered):
            _text(value, "constraint field")

    def to_dict(self) -> dict[str, Any]:
        return {
            "constraint_id": self.constraint_id,
            "kind": self.kind,
            "rendered": self.rendered,
            "meta_ids": [item.value for item in self.meta_ids],
            "name_ids": list(self.name_ids),
            "level_variables": list(self.level_variables),
            "blockers": [item.value for item in self.blockers],
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> Constraint:
        expected = {
            "constraint_id",
            "kind",
            "rendered",
            "meta_ids",
            "name_ids",
            "level_variables",
            "blockers",
        }
        if set(value) != expected:
            raise ValueError("malformed constraint")
        return cls(
            constraint_id=_text(value["constraint_id"], "constraint id"),
            kind=_text(value["kind"], "constraint kind"),
            rendered=_text(value["rendered"], "rendered constraint"),
            meta_ids=tuple(
                MetaId(_text(item, "constraint meta id", limit=512))
                for item in _list(value["meta_ids"], "constraint metas")
            ),
            name_ids=tuple(
                _text(item, "constraint name")
                for item in _list(value["name_ids"], "constraint names")
            ),
            level_variables=tuple(
                _text(item, "constraint level variable")
                for item in _list(value["level_variables"], "level variables")
            ),
            blockers=tuple(
                MetaId(_text(item, "constraint blocker", limit=512))
                for item in _list(value["blockers"], "constraint blockers")
            ),
        )


@dataclass(frozen=True)
class DependencyEdge:
    source: str
    target: str
    kind: Literal["goal-meta", "goal-constraint", "constraint-meta", "meta-meta"]

    def __post_init__(self) -> None:
        if self.kind not in {
            "goal-meta",
            "goal-constraint",
            "constraint-meta",
            "meta-meta",
        }:
            raise ValueError("invalid dependency edge kind")

    def to_dict(self) -> dict[str, str]:
        return {"source": self.source, "target": self.target, "kind": self.kind}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> DependencyEdge:
        if set(value) != {"source", "target", "kind"}:
            raise ValueError("malformed dependency edge")
        return cls(
            _text(value["source"], "dependency source"),
            _text(value["target"], "dependency target"),
            _text(value["kind"], "dependency kind"),  # type: ignore[arg-type]
        )


@dataclass(frozen=True)
class ProofEdge:
    action_id: str
    parent_state_hash: str
    child_state_hashes: tuple[str, ...]
    verifier_response_sha256: str
    cost: Mapping[str, int | float]

    def __post_init__(self) -> None:
        digests = (
            self.parent_state_hash,
            self.verifier_response_sha256,
            *self.child_state_hashes,
        )
        if not all(
            len(item) == 64
            and all(character in "0123456789abcdef" for character in item)
            for item in digests
        ):
            raise ValueError("proof-edge identities must be SHA-256 digests")

    def to_dict(self) -> dict[str, Any]:
        return {
            "action_id": self.action_id,
            "parent_state_hash": self.parent_state_hash,
            "child_state_hashes": list(self.child_state_hashes),
            "verifier_response_sha256": self.verifier_response_sha256,
            "cost": dict(sorted(self.cost.items())),
        }

    def semantic_dict(self) -> dict[str, Any]:
        """Return replay identity without timing or raw-response provenance.

        Costs vary between equivalent runs, and Agda responses may contain
        relocation-specific paths.  Neither belongs in a state token.  The
        action, parent, and provisional child identities are sufficient to
        distinguish transaction lineages; the complete edge remains in the
        serialized evidence record returned by :meth:`to_dict`.
        """

        return {
            "action_id": self.action_id,
            "parent_state_hash": self.parent_state_hash,
            "child_state_hashes": list(self.child_state_hashes),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ProofEdge:
        expected = {
            "action_id",
            "parent_state_hash",
            "child_state_hashes",
            "verifier_response_sha256",
            "cost",
        }
        if set(value) != expected:
            raise ValueError("malformed proof edge")
        cost = _cost_mapping(value["cost"], "proof-edge cost")
        return cls(
            action_id=_text(value["action_id"], "proof edge action id"),
            parent_state_hash=_text(
                value["parent_state_hash"], "proof edge parent hash", limit=64
            ),
            child_state_hashes=tuple(
                _text(item, "proof edge child hash", limit=64)
                for item in _list(value["child_state_hashes"], "child state hashes")
            ),
            verifier_response_sha256=_text(
                value["verifier_response_sha256"],
                "proof edge verifier hash",
                limit=64,
            ),
            cost=dict(cost),
        )


@dataclass(frozen=True)
class ProofState:
    environment_id: EnvironmentId
    source_revision: SourceRevision
    module_id: ModuleId
    focused_interaction: InteractionId | None
    goals: tuple[Goal, ...]
    metas: tuple[Meta, ...]
    constraints: tuple[Constraint, ...]
    dependency_graph: tuple[DependencyEdge, ...] = ()
    proof_dag: tuple[ProofEdge, ...] = ()
    cost: Mapping[str, int | float] = field(default_factory=dict)
    extraction_capabilities: tuple[str, ...] = ()
    schema_version: str = PROOF_STATE_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != PROOF_STATE_SCHEMA_VERSION:
            raise ValueError("unsupported proof-state schema version")
        _cost_mapping(self.cost, "proof state cost")
        collections = (self.goals, self.metas, self.constraints, self.dependency_graph)
        if any(len(collection) > MAX_STATE_ITEMS for collection in collections):
            raise ValueError("proof state exceeds the item limit")
        goal_ids = [goal.interaction_id for goal in self.goals]
        meta_ids = [meta.meta_id for meta in self.metas]
        constraint_ids = [item.constraint_id for item in self.constraints]
        if len(goal_ids) != len(set(goal_ids)):
            raise ValueError("proof state contains duplicate interaction ids")
        if len(meta_ids) != len(set(meta_ids)):
            raise ValueError("proof state contains duplicate meta ids")
        if len(constraint_ids) != len(set(constraint_ids)):
            raise ValueError("proof state contains duplicate constraint ids")
        if (
            self.focused_interaction is not None
            and self.focused_interaction not in goal_ids
        ):
            raise ValueError("focused interaction is not an open goal")
        known_meta = set(meta_ids)
        for goal in self.goals:
            if goal.meta_id not in known_meta:
                raise ValueError("goal refers to a meta missing from the proof state")
            if any(item not in known_meta for item in goal.blockers):
                raise ValueError("goal blocker is missing from the proof state")
            if any(item not in constraint_ids for item in goal.constraint_ids):
                raise ValueError("goal constraint is missing from the proof state")
        for meta in self.metas:
            if meta.status == "solved" and any(
                goal.meta_id == meta.meta_id for goal in self.goals
            ):
                raise ValueError("solved meta appears as an open goal")
            if any(item not in known_meta for item in meta.blockers):
                raise ValueError("meta blocker is missing from the proof state")

    def semantic_dict(self) -> dict[str, Any]:
        """Return exact replay identity, excluding accumulated measurement cost."""

        return {
            "schema_version": self.schema_version,
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "module_id": self.module_id.to_dict(),
            "focused_interaction": (
                self.focused_interaction.value if self.focused_interaction else None
            ),
            "goals": [item.to_dict() for item in self.goals],
            "metas": [item.to_dict() for item in self.metas],
            "constraints": [item.to_dict() for item in self.constraints],
            "dependency_graph": [item.to_dict() for item in self.dependency_graph],
            "proof_dag": [item.semantic_dict() for item in self.proof_dag],
            "extraction_capabilities": list(self.extraction_capabilities),
        }

    @property
    def structural_hash(self) -> str:
        return stable_hash(self.semantic_dict())

    def to_dict(self) -> dict[str, Any]:
        result = self.semantic_dict()
        result["proof_dag"] = [item.to_dict() for item in self.proof_dag]
        result["cost"] = dict(sorted(self.cost.items()))
        result["structural_hash"] = self.structural_hash
        return result

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ProofState:
        expected = {
            "schema_version",
            "environment_id",
            "source_revision",
            "module_id",
            "focused_interaction",
            "goals",
            "metas",
            "constraints",
            "dependency_graph",
            "proof_dag",
            "cost",
            "extraction_capabilities",
            "structural_hash",
        }
        if set(value) != expected:
            raise ValueError("malformed proof state")
        cost = _cost_mapping(value["cost"], "proof state cost")
        state = cls(
            schema_version=_text(value["schema_version"], "proof-state schema"),
            environment_id=EnvironmentId(
                _text(value["environment_id"], "proof-state environment", limit=64)
            ),
            source_revision=SourceRevision(
                _text(value["source_revision"], "proof-state revision", limit=64)
            ),
            module_id=ModuleId.from_dict(_mapping(value["module_id"], "module id")),
            focused_interaction=(
                InteractionId(
                    _integer(value["focused_interaction"], "focused interaction id")
                )
                if value["focused_interaction"] is not None
                else None
            ),
            goals=tuple(
                Goal.from_dict(_mapping(item, "goal"))
                for item in _list(value["goals"], "goals")
            ),
            metas=tuple(
                Meta.from_dict(_mapping(item, "meta"))
                for item in _list(value["metas"], "metas")
            ),
            constraints=tuple(
                Constraint.from_dict(_mapping(item, "constraint"))
                for item in _list(value["constraints"], "constraints")
            ),
            dependency_graph=tuple(
                DependencyEdge.from_dict(_mapping(item, "dependency edge"))
                for item in _list(value["dependency_graph"], "dependency graph")
            ),
            proof_dag=tuple(
                ProofEdge.from_dict(_mapping(item, "proof edge"))
                for item in _list(value["proof_dag"], "proof DAG")
            ),
            cost=dict(cost),
            extraction_capabilities=tuple(
                _text(item, "extraction capability")
                for item in _list(
                    value["extraction_capabilities"], "extraction capabilities"
                )
            ),
        )
        if value["structural_hash"] != state.structural_hash:
            raise ValueError("proof-state structural hash mismatch")
        return state

    def token(self, *, process_generation: int, sequence: int) -> StateToken:
        return StateToken(
            environment_id=self.environment_id,
            source_revision=self.source_revision,
            module_id=self.module_id,
            process_generation=process_generation,
            sequence=sequence,
            structural_hash=self.structural_hash,
        )
