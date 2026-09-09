"""Versioned actions for eliminating inhabitants in dependent telescopes."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal

DEPENDENT_ACTION_SCHEMA = "agdaprover.dependent-action.v1"
EliminationReason = Literal[
    "preferred-inhabitant",
    "result-index",
    "target-ancestor",
    "dependent-descendant",
    "fallback",
]


@dataclass(frozen=True)
class DependentEliminationAction:
    """Ask Agda to eliminate one proof-relevant telescope inhabitant.

    This action covers every data, record, or indexed-family inhabitant
    uniformly. It prescribes no family-specific coercion term; Agda's
    eliminator refines all dependent nodes.
    """

    node_id: int
    name: str
    type_text: str
    dependencies: tuple[int, ...]
    instantiation_dependencies: tuple[int, ...]
    dependency_depth: int
    reason: EliminationReason
    schema_version: str = DEPENDENT_ACTION_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != DEPENDENT_ACTION_SCHEMA:
            raise ValueError("unsupported dependent-action schema")
        if self.node_id < 0 or self.dependency_depth < 0:
            raise ValueError("dependent-action indices cannot be negative")
        if not self.name or not self.type_text:
            raise ValueError("dependent action requires a named, typed inhabitant")
        if len(set(self.dependencies)) != len(self.dependencies):
            raise ValueError("duplicate dependent-action dependency")
        if len(set(self.instantiation_dependencies)) != len(
            self.instantiation_dependencies
        ):
            raise ValueError("duplicate dependent-action instantiation dependency")
        if any(index < 0 or index >= self.node_id for index in self.dependencies):
            raise ValueError("dependent-action dependencies must point backwards")
        if any(
            index < 0 or index >= self.node_id
            for index in self.instantiation_dependencies
        ):
            raise ValueError(
                "dependent-action instantiation dependencies must point backwards"
            )
        if not set(self.dependencies).issubset(self.instantiation_dependencies):
            raise ValueError(
                "dependent-action instantiation must retain direct dependencies"
            )
        if self.reason not in {
            "preferred-inhabitant",
            "result-index",
            "target-ancestor",
            "dependent-descendant",
            "fallback",
        }:
            raise ValueError("unsupported dependent-action reason")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "tag": "eliminate-dependent-inhabitant",
            "node_id": self.node_id,
            "name": self.name,
            "type": self.type_text,
            "dependencies": list(self.dependencies),
            "instantiation_dependencies": list(self.instantiation_dependencies),
            "dependency_depth": self.dependency_depth,
            "reason": self.reason,
            "relevance": "proof-relevant",
            "elaboration": "agda-case-split",
        }

    @classmethod
    def from_dict(cls, value: dict[str, Any]) -> DependentEliminationAction:
        if value.get("schema_version") != DEPENDENT_ACTION_SCHEMA:
            raise ValueError("unsupported dependent-action schema")
        if value.get("tag") != "eliminate-dependent-inhabitant":
            raise ValueError("unsupported dependent-action tag")
        if value.get("relevance") != "proof-relevant":
            raise ValueError("dependent elimination cannot erase proof relevance")
        if value.get("elaboration") != "agda-case-split":
            raise ValueError("unsupported dependent-action elaboration")
        try:
            return cls(
                node_id=int(value["node_id"]),
                name=str(value["name"]),
                type_text=str(value["type"]),
                dependencies=tuple(int(item) for item in value["dependencies"]),
                instantiation_dependencies=tuple(
                    int(item) for item in value["instantiation_dependencies"]
                ),
                dependency_depth=int(value["dependency_depth"]),
                reason=value["reason"],
            )
        except (KeyError, TypeError, ValueError) as error:
            raise ValueError("malformed dependent elimination action") from error
