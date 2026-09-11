"""Versioned Stage 2 search-state and action identities.

These values are orchestration IRs, not a replacement for Agda syntax or the
kernel.  They make deterministic generation, exact transposition keys, module
provenance, and replay evidence explicit while every transition is still
authorized by an Agda interaction command.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any, Literal

from .actions import RefinementCandidate
from .contracts import ContextEntry, GoalInfo
from .module_scope import ModuleScope
from .type_syntax import normalize_type_text

SYMBOLIC_STATE_SCHEMA = "agdaprover.symbolic-state.v1"
SYMBOLIC_ACTION_SCHEMA = "agdaprover.symbolic-action.v1"
MAX_ACTION_OPERANDS = 64
MAX_ACTION_TEXT_BYTES = 1 << 20

SymbolicActionTag = Literal[
    "introduce-pi",
    "exact-local",
    "apply-local",
    "introduce-constructor",
    "select-constructor",
    "eliminate-local",
    "refine-visible-premise",
    "recursive-call",
    "structural-induction",
    "normalize",
    "rewrite",
    "close-zero-constructor",
]

SUPPORTED_SYMBOLIC_ACTIONS: tuple[SymbolicActionTag, ...] = (
    "introduce-pi",
    "exact-local",
    "apply-local",
    "introduce-constructor",
    "select-constructor",
    "eliminate-local",
    "refine-visible-premise",
    "recursive-call",
    "structural-induction",
    "normalize",
    "rewrite",
    "close-zero-constructor",
)

ElaborationStrategy = Literal["refine", "case-split", "check-term", "normalize"]


def _stable_hash(value: object) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _bounded_text(value: object, label: str) -> str:
    if not isinstance(value, str) or len(value.encode()) > MAX_ACTION_TEXT_BYTES:
        raise ValueError(f"{label} must be bounded text")
    return value


@dataclass(frozen=True)
class SymbolicState:
    """Exact controller identity for one focused, module-scoped Agda goal."""

    goal: GoalInfo
    environment_id: str
    source_revision: str
    toolchain_id: str
    model_ids: tuple[str, ...] = ()
    schema_version: str = SYMBOLIC_STATE_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != SYMBOLIC_STATE_SCHEMA:
            raise ValueError("unsupported symbolic-state schema")
        if self.goal.module_scope is None:
            raise ValueError("Stage 2 symbolic states require module provenance")
        for label, value in (
            ("environment id", self.environment_id),
            ("source revision", self.source_revision),
            ("toolchain id", self.toolchain_id),
        ):
            if not value or len(value.encode()) > 4096:
                raise ValueError(f"{label} must be nonempty bounded text")
        if len(self.model_ids) > 16 or any(
            not item or len(item.encode()) > 4096 for item in self.model_ids
        ):
            raise ValueError("symbolic-state model identities are malformed")

    def semantic_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "goal": self.goal.to_dict(),
            "environment_id": self.environment_id,
            "source_revision": self.source_revision,
            "toolchain_id": self.toolchain_id,
            "model_ids": list(self.model_ids),
        }

    @property
    def state_id(self) -> str:
        return _stable_hash(self.semantic_dict())

    def to_dict(self) -> dict[str, object]:
        result = self.semantic_dict()
        result["state_id"] = self.state_id
        return result

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> SymbolicState:
        expected = {
            "schema_version",
            "goal",
            "environment_id",
            "source_revision",
            "toolchain_id",
            "model_ids",
            "state_id",
        }
        if set(value) != expected:
            raise ValueError("malformed symbolic state")
        goal_value = value["goal"]
        if not isinstance(goal_value, Mapping) or set(goal_value) - {
            "universe_names"
        } != {
            "goal_id",
            "target",
            "context",
            "source_range",
            "module_scope",
        }:
            raise ValueError("malformed symbolic-state goal")
        goal_id = goal_value["goal_id"]
        target = goal_value["target"]
        context = goal_value["context"]
        source_range = goal_value["source_range"]
        module_scope = goal_value["module_scope"]
        universe_names = goal_value.get("universe_names")
        if universe_names is not None and (
            not isinstance(universe_names, list)
            or not all(
                isinstance(name, str) and name and not any(c.isspace() for c in name)
                for name in universe_names
            )
            or universe_names != sorted(set(universe_names))
        ):
            raise ValueError("malformed symbolic-state universe names")
        if (
            not isinstance(goal_id, int)
            or isinstance(goal_id, bool)
            or goal_id < 0
            or not isinstance(target, str)
            or not isinstance(context, list)
            or not isinstance(source_range, list)
            or len(source_range) != 2
            or not all(
                isinstance(position, int) and not isinstance(position, bool)
                for position in source_range
            )
            or not isinstance(module_scope, dict)
        ):
            raise ValueError("malformed symbolic-state goal fields")
        entries: list[ContextEntry] = []
        for item in context:
            if not isinstance(item, dict) or set(item) != {"name", "type", "in_scope"}:
                raise ValueError("malformed symbolic-state context")
            if (
                not isinstance(item["name"], str)
                or not isinstance(item["type"], str)
                or not isinstance(item["in_scope"], bool)
            ):
                raise ValueError("malformed symbolic-state context fields")
            entries.append(ContextEntry(item["name"], item["type"], item["in_scope"]))
        model_ids = value["model_ids"]
        if not isinstance(model_ids, list) or not all(
            isinstance(item, str) for item in model_ids
        ):
            raise ValueError("symbolic-state model identities must be a list")
        for field in (
            "schema_version",
            "environment_id",
            "source_revision",
            "toolchain_id",
        ):
            if not isinstance(value[field], str):
                raise ValueError(f"symbolic state {field} must be text")
        result = cls(
            goal=GoalInfo(
                goal_id,
                target,
                tuple(entries),
                (source_range[0], source_range[1]),
                ModuleScope.from_dict(module_scope),
                None if universe_names is None else frozenset(universe_names),
            ),
            environment_id=value["environment_id"],
            source_revision=value["source_revision"],
            toolchain_id=value["toolchain_id"],
            model_ids=tuple(model_ids),
            schema_version=value["schema_version"],
        )
        if value["state_id"] != result.state_id:
            raise ValueError("symbolic-state identity mismatch")
        return result


@dataclass(frozen=True)
class SymbolicAction:
    """One deterministic proposal whose applicability Agda must decide."""

    tag: SymbolicActionTag
    expression: str
    elaboration: ElaborationStrategy
    operands: tuple[tuple[str, str], ...] = ()
    generator: str = "stage2-core"
    module_scope_id: str | None = None
    schema_version: str = SYMBOLIC_ACTION_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != SYMBOLIC_ACTION_SCHEMA:
            raise ValueError("unsupported symbolic-action schema")
        if self.tag not in SUPPORTED_SYMBOLIC_ACTIONS:
            raise ValueError("unsupported symbolic action")
        _bounded_text(self.expression, "symbolic action expression")
        _bounded_text(self.generator, "symbolic action generator")
        if self.elaboration not in {"refine", "case-split", "check-term", "normalize"}:
            raise ValueError("unsupported symbolic elaboration strategy")
        if len(self.operands) > MAX_ACTION_OPERANDS:
            raise ValueError("symbolic action has too many operands")
        if tuple(sorted(self.operands)) != self.operands or len(
            {name for name, _value in self.operands}
        ) != len(self.operands):
            raise ValueError("symbolic action operands must be sorted and unique")
        for name, value in self.operands:
            _bounded_text(name, "symbolic action operand name")
            _bounded_text(value, "symbolic action operand value")
        if self.module_scope_id is not None and not (
            len(self.module_scope_id) == 64
            and all(
                character in "0123456789abcdef" for character in self.module_scope_id
            )
        ):
            raise ValueError("symbolic action module scope must be a SHA-256 identity")

    @property
    def action_id(self) -> str:
        return _stable_hash(self.semantic_dict())

    def semantic_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "tag": self.tag,
            "expression": self.expression,
            "elaboration": self.elaboration,
            "operands": {name: value for name, value in self.operands},
            "generator": self.generator,
            "module_scope_id": self.module_scope_id,
            "kernel_authority": "agda",
        }

    def to_dict(self) -> dict[str, object]:
        result = self.semantic_dict()
        result["action_id"] = self.action_id
        return result

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> SymbolicAction:
        expected = {
            "schema_version",
            "tag",
            "expression",
            "elaboration",
            "operands",
            "generator",
            "module_scope_id",
            "kernel_authority",
            "action_id",
        }
        if set(value) != expected or value.get("kernel_authority") != "agda":
            raise ValueError("malformed symbolic action")
        operands = value["operands"]
        if not isinstance(operands, Mapping) or not all(
            isinstance(name, str) and isinstance(item, str)
            for name, item in operands.items()
        ):
            raise ValueError("symbolic action operands must be a text mapping")
        scope_id = value["module_scope_id"]
        if scope_id is not None and not isinstance(scope_id, str):
            raise ValueError("symbolic action module scope must be text or null")
        for field in (
            "schema_version",
            "tag",
            "expression",
            "elaboration",
            "generator",
        ):
            if not isinstance(value[field], str):
                raise ValueError(f"symbolic action {field} must be text")
        result = cls(
            tag=value["tag"],
            expression=value["expression"],
            elaboration=value["elaboration"],
            operands=tuple(sorted(operands.items())),
            generator=value["generator"],
            module_scope_id=scope_id,
            schema_version=value["schema_version"],
        )
        if value["action_id"] != result.action_id:
            raise ValueError("symbolic-action identity mismatch")
        return result


def action_from_refinement(
    goal: GoalInfo, action: RefinementCandidate
) -> SymbolicAction:
    """Lift the interactive action family into the Stage 2 action envelope."""

    if action.tag == "introduce-lambda":
        tag: SymbolicActionTag = "introduce-pi"
    elif action.tag == "introduce-constructor":
        tag = "introduce-constructor"
    elif action.tag == "select-constructor":
        tag = "select-constructor"
    elif action.tag == "case-split":
        tag = "eliminate-local"
    elif action.tag == "use-local":
        tag = (
            "exact-local"
            if normalize_type_text(action.local_type or "")
            == normalize_type_text(goal.target)
            else "apply-local"
        )
    else:
        tag = "refine-visible-premise"
    operands = tuple(
        sorted(
            (name, value)
            for name, value in (
                ("name", action.local_name),
                ("type", action.local_type),
            )
            if value is not None
        )
    )
    return SymbolicAction(
        tag=tag,
        expression=action.expression,
        elaboration="case-split" if action.tag == "case-split" else "refine",
        operands=operands,
        generator="p0-refinement-adapter",
        module_scope_id=(
            goal.module_scope.scope_id if goal.module_scope is not None else None
        ),
    )
