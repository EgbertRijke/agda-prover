"""Finite, proof-relevant dependency telescopes used by search heuristics.

The IR does not distinguish among forms of data or records. Every node is a
typed, proof-relevant inhabitant whose type may refer to earlier nodes. Textual
dependency recovery is only a planning hint; Agda remains the authority on
binding, elaboration, and type correctness.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Literal

from .contracts import GoalInfo
from .type_syntax import (
    normalize_type_text,
    parse_named_binder,
    split_adjacent_binders,
    split_top_level_arrows,
)

DEPENDENCY_TOWER_SCHEMA = "agdaprover.dependency-tower.v1"
DEFAULT_MAX_TOWER_NODES = 4096
DEFAULT_MAX_TOWER_TEXT_BYTES = 1 << 20

_TOKEN = re.compile(r"[\w'′₀-₉⁰-⁹-]+|[^\w\s()\[\]{}:;,→λ∀⦃⦄]+", re.UNICODE)


class DependencyTowerError(ValueError):
    """A malformed or over-budget dependency tower."""


@dataclass(frozen=True)
class TowerNode:
    """One proof-relevant inhabitant in a topologically ordered telescope."""

    node_id: int
    name: str
    type_text: str
    dependencies: tuple[int, ...]
    origin: Literal["context", "telescope"]
    visibility: Literal["explicit", "implicit", "instance", "context"]
    in_scope: bool

    def __post_init__(self) -> None:
        if self.node_id < 0 or not self.name or not self.type_text:
            raise DependencyTowerError("malformed tower node")
        if self.origin not in {"context", "telescope"}:
            raise DependencyTowerError("unknown tower-node origin")
        if self.visibility not in {
            "explicit",
            "implicit",
            "instance",
            "context",
        }:
            raise DependencyTowerError("unknown tower-node visibility")
        if not isinstance(self.in_scope, bool):
            raise DependencyTowerError("tower-node scope flag must be boolean")

    def to_dict(self) -> dict[str, object]:
        return {
            "node_id": self.node_id,
            "name": self.name,
            "type": self.type_text,
            "dependencies": list(self.dependencies),
            "origin": self.origin,
            "visibility": self.visibility,
            # Proof relevance is an invariant, not an inference from the type.
            "relevance": "proof-relevant",
            "in_scope": self.in_scope,
        }


@dataclass(frozen=True)
class DependencyTower:
    """A finite DAG presented in telescope order.

    Node IDs are dense and every edge points backwards.  This makes validation,
    depth computation, and ancestor queries linear in the size of the tower.
    """

    nodes: tuple[TowerNode, ...]
    result_type: str
    result_dependencies: tuple[int, ...]
    schema_version: str = DEPENDENCY_TOWER_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != DEPENDENCY_TOWER_SCHEMA:
            raise DependencyTowerError(
                f"unsupported dependency-tower schema: {self.schema_version!r}"
            )
        for expected_id, node in enumerate(self.nodes):
            if node.node_id != expected_id:
                raise DependencyTowerError("tower node IDs must be dense and ordered")
            if len(set(node.dependencies)) != len(node.dependencies):
                raise DependencyTowerError("duplicate dependency edge")
            if any(
                parent < 0 or parent >= node.node_id for parent in node.dependencies
            ):
                raise DependencyTowerError("tower dependencies must point backwards")
        if len(set(self.result_dependencies)) != len(self.result_dependencies):
            raise DependencyTowerError("duplicate result dependency")
        if any(
            index < 0 or index >= len(self.nodes) for index in self.result_dependencies
        ):
            raise DependencyTowerError("result dependency is outside the tower")

    def depths(self) -> tuple[int, ...]:
        depths: list[int] = []
        for node in self.nodes:
            depths.append(
                0
                if not node.dependencies
                else 1 + max(depths[parent] for parent in node.dependencies)
            )
        return tuple(depths)

    def instantiation_dependencies(self, node_id: int) -> tuple[int, ...]:
        """Return the selected node's complete ambient instantiation.

        The closure deliberately does not guess which upstream arguments a
        datatype declaration calls parameters and which it calls indices.
        It is computed iteratively and on demand for a selected action, rather
        than materializing the potentially quadratic transitive closure of
        every node in a deep telescope.
        """

        if node_id < 0 or node_id >= len(self.nodes):
            raise DependencyTowerError("unknown tower node")
        pending = list(self.nodes[node_id].dependencies)
        closure = set(pending)
        while pending:
            current = pending.pop()
            for parent in self.nodes[current].dependencies:
                if parent not in closure:
                    closure.add(parent)
                    pending.append(parent)
        return tuple(sorted(closure))

    def max_depth(self) -> int:
        depths = self.depths()
        return max(depths, default=0)

    def children(self) -> tuple[tuple[int, ...], ...]:
        """Return direct dependants for every node in one linear pass."""

        children: list[list[int]] = [[] for _node in self.nodes]
        for node in self.nodes:
            for parent in node.dependencies:
                children[parent].append(node.node_id)
        return tuple(tuple(entries) for entries in children)

    def result_cone(self) -> frozenset[int]:
        pending = list(self.result_dependencies)
        cone = set(pending)
        while pending:
            current = pending.pop()
            for parent in self.nodes[current].dependencies:
                if parent not in cone:
                    cone.add(parent)
                    pending.append(parent)
        return frozenset(cone)

    def visible_node(self, name: str) -> TowerNode | None:
        """Return the last in-scope binding, respecting ordinary shadowing."""

        for node in reversed(self.nodes):
            if node.in_scope and node.name == name:
                return node
        return None

    def has_runtime_dependency(self) -> bool:
        """Whether an eliminable inhabitant can affect another type or result."""

        runtime_ids = {
            node.node_id
            for node in self.nodes
            if node.in_scope or node.origin == "telescope"
        }
        return any(
            parent in runtime_ids for node in self.nodes for parent in node.dependencies
        ) or any(parent in runtime_ids for parent in self.result_dependencies)

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "nodes": [node.to_dict() for node in self.nodes],
            "result_type": self.result_type,
            "result_dependencies": list(self.result_dependencies),
        }

    @classmethod
    def from_dict(
        cls,
        value: dict[str, Any],
        *,
        max_nodes: int = DEFAULT_MAX_TOWER_NODES,
        max_text_bytes: int = DEFAULT_MAX_TOWER_TEXT_BYTES,
    ) -> DependencyTower:
        if max_nodes <= 0 or max_text_bytes <= 0:
            raise DependencyTowerError("dependency-tower budgets must be positive")
        if value.get("schema_version") != DEPENDENCY_TOWER_SCHEMA:
            raise DependencyTowerError("unsupported dependency-tower schema")
        raw_nodes = value.get("nodes")
        if not isinstance(raw_nodes, list) or len(raw_nodes) > max_nodes:
            raise DependencyTowerError("dependency tower exceeds its node budget")
        nodes: list[TowerNode] = []
        text_bytes = 0
        for raw in raw_nodes:
            if not isinstance(raw, dict):
                raise DependencyTowerError("tower node must be an object")
            if raw.get("relevance") != "proof-relevant":
                raise DependencyTowerError("tower node lost proof relevance")
            if not isinstance(raw.get("name"), str) or not isinstance(
                raw.get("type"), str
            ):
                raise DependencyTowerError("tower node names and types must be text")
            if not isinstance(raw.get("dependencies"), list) or not isinstance(
                raw.get("in_scope"), bool
            ):
                raise DependencyTowerError("malformed tower node fields")
            try:
                node = TowerNode(
                    node_id=int(raw["node_id"]),
                    name=str(raw["name"]),
                    type_text=str(raw["type"]),
                    dependencies=tuple(int(item) for item in raw["dependencies"]),
                    origin=raw["origin"],
                    visibility=raw["visibility"],
                    in_scope=raw["in_scope"],
                )
            except (KeyError, TypeError, ValueError) as error:
                raise DependencyTowerError("malformed tower node") from error
            text_bytes += len(node.name.encode()) + len(node.type_text.encode())
            nodes.append(node)
        result_type = value.get("result_type")
        raw_result_dependencies = value.get("result_dependencies")
        if not isinstance(result_type, str) or not isinstance(
            raw_result_dependencies, list
        ):
            raise DependencyTowerError("malformed dependency-tower result")
        text_bytes += len(result_type.encode())
        if text_bytes > max_text_bytes:
            raise DependencyTowerError("dependency tower exceeds its text budget")
        try:
            result_dependencies = tuple(int(item) for item in raw_result_dependencies)
        except (TypeError, ValueError) as error:
            raise DependencyTowerError("malformed result dependencies") from error
        return cls(tuple(nodes), result_type, result_dependencies)


def _tokens(text: str) -> tuple[str, ...]:
    return tuple(_TOKEN.findall(text))


def _dependencies(type_text: str, visible_by_name: dict[str, int]) -> tuple[int, ...]:
    found: list[int] = []
    seen: set[int] = set()
    for token in _tokens(type_text):
        node_id = visible_by_name.get(token)
        if node_id is not None and node_id not in seen:
            found.append(node_id)
            seen.add(node_id)
    return tuple(found)


def tower_from_goal(
    goal: GoalInfo,
    *,
    max_nodes: int = DEFAULT_MAX_TOWER_NODES,
    max_text_bytes: int = DEFAULT_MAX_TOWER_TEXT_BYTES,
) -> DependencyTower:
    """Recover a bounded dependency telescope from one kernel goal.

    This scan is deliberately linear in the displayed input size.  It never
    invents a typing judgment: false-positive textual edges can only influence
    action ordering, and every selected action is checked by Agda.
    """

    if max_nodes <= 0 or max_text_bytes <= 0:
        raise DependencyTowerError("dependency-tower budgets must be positive")
    nodes: list[TowerNode] = []
    visible_by_name: dict[str, int] = {}
    text_bytes = 0

    def append(
        name: str,
        type_text: str,
        *,
        origin: Literal["context", "telescope"],
        visibility: Literal["explicit", "implicit", "instance", "context"],
        in_scope: bool,
    ) -> None:
        nonlocal text_bytes
        if len(nodes) >= max_nodes:
            raise DependencyTowerError("dependency tower exceeds its node budget")
        normalized = normalize_type_text(type_text)
        text_bytes += len(name.encode()) + len(normalized.encode())
        if text_bytes > max_text_bytes:
            raise DependencyTowerError("dependency tower exceeds its text budget")
        node = TowerNode(
            node_id=len(nodes),
            name=name,
            type_text=normalized,
            dependencies=_dependencies(normalized, visible_by_name),
            origin=origin,
            visibility=visibility,
            in_scope=in_scope,
        )
        nodes.append(node)
        visible_by_name[name] = node.node_id

    for entry in goal.context:
        append(
            entry.name,
            entry.type,
            origin="context",
            visibility="context",
            in_scope=entry.in_scope,
        )

    parts = split_top_level_arrows(goal.target)
    anonymous = 0
    for domain in parts[:-1]:
        groups = split_adjacent_binders(domain) or (domain,)
        for group in groups:
            binder = parse_named_binder(group)
            if binder is None:
                append(
                    f"$arg{anonymous}",
                    group,
                    origin="telescope",
                    visibility="explicit",
                    in_scope=False,
                )
                anonymous += 1
                continue
            for name in binder.names:
                append(
                    name,
                    binder.domain,
                    origin="telescope",
                    visibility=binder.visibility,
                    in_scope=False,
                )
    result_type = normalize_type_text(parts[-1])
    text_bytes += len(result_type.encode())
    if text_bytes > max_text_bytes:
        raise DependencyTowerError("dependency tower exceeds its text budget")
    return DependencyTower(
        nodes=tuple(nodes),
        result_type=result_type,
        result_dependencies=_dependencies(result_type, visible_by_name),
    )
