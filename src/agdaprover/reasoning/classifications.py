"""Typed, model-independent facts used by structural search scheduling.

The symbolic engines compute these facts from live proof state.  Rankers may
observe them, but they cannot promote an unavailable action or turn an unknown
fact into a soundness decision.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, fields

from ..relation_path import parse_relation
from ..type_syntax import (
    normalize_type_text,
    parse_named_binder,
    result_head,
    split_adjacent_binders,
    split_top_level_arrows,
)

STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION = "agdaprover.structural-classification.v2"


@dataclass(frozen=True)
class StructuralClassification:
    """Name-neutral scheduling evidence at one solver interaction point.

    ``None`` means that the caller did not establish the fact.  It is distinct
    from ``False`` so training data cannot learn from an accidental negative.
    """

    recursive_result_head_matches_goal: bool | None = None
    construction_result_head_matches_goal: bool | None = None
    structural_construction_available: bool | None = None
    productive_elimination_available: bool | None = None
    structural_descent_available: bool | None = None
    higher_order_structural_descent_available: bool | None = None
    dependencies_ready: bool | None = None
    homogeneous_coordinate_permutation: bool | None = None
    reflexive_relation_target: bool | None = None
    relational_elimination_available: bool | None = None
    construction_elimination_compete: bool | None = None
    schema_version: str = STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION:
            raise ValueError("unsupported structural-classification schema")
        for item in fields(self):
            if item.name == "schema_version":
                continue
            value = getattr(self, item.name)
            if value is not None and not isinstance(value, bool):
                raise TypeError(
                    f"structural classification {item.name!r} must be boolean or null"
                )

    def to_dict(self) -> dict[str, bool | str | None]:
        return {
            "schema_version": self.schema_version,
            "recursive_result_head_matches_goal": (
                self.recursive_result_head_matches_goal
            ),
            "construction_result_head_matches_goal": (
                self.construction_result_head_matches_goal
            ),
            "structural_construction_available": (
                self.structural_construction_available
            ),
            "productive_elimination_available": (self.productive_elimination_available),
            "structural_descent_available": self.structural_descent_available,
            "higher_order_structural_descent_available": (
                self.higher_order_structural_descent_available
            ),
            "dependencies_ready": self.dependencies_ready,
            "homogeneous_coordinate_permutation": (
                self.homogeneous_coordinate_permutation
            ),
            "reflexive_relation_target": self.reflexive_relation_target,
            "relational_elimination_available": (self.relational_elimination_available),
            "construction_elimination_compete": (self.construction_elimination_compete),
        }

    @classmethod
    def from_dict(cls, value: object) -> StructuralClassification:
        if value is None:
            return cls()
        if not isinstance(value, dict):
            raise ValueError("structural classification must be an object")
        expected = {
            "schema_version",
            "recursive_result_head_matches_goal",
            "construction_result_head_matches_goal",
            "structural_construction_available",
            "productive_elimination_available",
            "structural_descent_available",
            "higher_order_structural_descent_available",
            "dependencies_ready",
            "homogeneous_coordinate_permutation",
            "reflexive_relation_target",
            "relational_elimination_available",
            "construction_elimination_compete",
        }
        if set(value) != expected:
            raise ValueError("malformed structural classification")
        return cls(
            recursive_result_head_matches_goal=value[
                "recursive_result_head_matches_goal"
            ],
            construction_result_head_matches_goal=value[
                "construction_result_head_matches_goal"
            ],
            structural_construction_available=value[
                "structural_construction_available"
            ],
            productive_elimination_available=value["productive_elimination_available"],
            structural_descent_available=value["structural_descent_available"],
            higher_order_structural_descent_available=value[
                "higher_order_structural_descent_available"
            ],
            dependencies_ready=value["dependencies_ready"],
            homogeneous_coordinate_permutation=value[
                "homogeneous_coordinate_permutation"
            ],
            reflexive_relation_target=value["reflexive_relation_target"],
            relational_elimination_available=value["relational_elimination_available"],
            construction_elimination_compete=value["construction_elimination_compete"],
            schema_version=value["schema_version"],
        )


def classify_structural_scheduling(
    *,
    recursive_result_head_matches_goal: bool | None = None,
    construction_result_head_matches_goal: bool | None = None,
    structural_construction_available: bool | None = None,
    productive_elimination_available: bool | None = None,
    structural_descent_available: bool | None = None,
    higher_order_structural_descent_available: bool | None = None,
    dependencies_ready: bool | None = None,
    homogeneous_coordinate_permutation: bool | None = None,
    reflexive_relation_target: bool | None = None,
    relational_elimination_available: bool | None = None,
) -> StructuralClassification:
    """Build facts and derive competition only when both inputs are known."""

    competition: bool | None = None
    if (
        structural_construction_available is not None
        and productive_elimination_available is not None
    ):
        competition = (
            structural_construction_available and productive_elimination_available
        )
    return StructuralClassification(
        recursive_result_head_matches_goal=recursive_result_head_matches_goal,
        construction_result_head_matches_goal=construction_result_head_matches_goal,
        structural_construction_available=structural_construction_available,
        productive_elimination_available=productive_elimination_available,
        structural_descent_available=structural_descent_available,
        higher_order_structural_descent_available=(
            higher_order_structural_descent_available
        ),
        dependencies_ready=dependencies_ready,
        homogeneous_coordinate_permutation=homogeneous_coordinate_permutation,
        reflexive_relation_target=reflexive_relation_target,
        relational_elimination_available=relational_elimination_available,
        construction_elimination_compete=competition,
    )


def is_reflexive_relation_target(target: str) -> bool:
    """Recognize a displayed binary relation with identical endpoints.

    No relation or constructor receives built-in semantics. Consumers may use
    this fact only for scheduling or ranking; the kernel still decides whether
    any proposed introduction exists.
    """

    relation = parse_relation(target)
    return relation is not None and normalize_type_text(
        relation.left
    ) == normalize_type_text(relation.right)


def has_relational_elimination_shape(target: str) -> bool:
    """Whether a function can eliminate relation evidence toward a relation.

    The relation symbol is opaque. Shared endpoint coordinates make the
    premise structurally relevant enough to preserve a case-analysis
    alternative when a later joint goal may depend on computation.
    """

    try:
        parts = split_top_level_arrows(target)
    except ValueError:
        return False
    if len(parts) < 2:
        return False
    result = parse_relation(parts[-1])
    if result is None:
        return False
    result_endpoints = {
        normalize_type_text(result.left),
        normalize_type_text(result.right),
    }
    for part in parts[:-1]:
        binder = parse_named_binder(part)
        premise = parse_relation(binder.domain if binder is not None else part)
        if premise is None or premise.operator != result.operator:
            continue
        premise_endpoints = {
            normalize_type_text(premise.left),
            normalize_type_text(premise.right),
        }
        if premise_endpoints & result_endpoints:
            return True
    return False


def has_result_subject_elimination_shape(target: str) -> bool:
    """Whether a quantified subject is inspected by a relational result.

    This is the generic shape behind projection computation, inverse laws,
    algebraic induction laws, and datatype no-confusion goals.  It says only
    that case analysis is structurally productive enough to schedule before
    constructor synthesis; Agda still selects and validates every split.
    """

    try:
        parts = split_top_level_arrows(target)
    except ValueError:
        return False
    if len(parts) < 2 or parse_relation(parts[-1]) is None:
        return False
    result = parts[-1]
    for part in parts[:-1]:
        for group in split_adjacent_binders(part) or (part,):
            binder = parse_named_binder(group)
            if binder is None or binder.visibility != "explicit":
                continue
            if any(
                re.search(rf"(?<![\w'′-]){re.escape(name)}(?![\w'′-])", result)
                for name in binder.names
            ):
                return True
    return False


def has_relational_context_evidence(
    target: str, evidence_types: tuple[str, ...]
) -> bool:
    """Whether contextual evidence belongs to the target's relation graph."""

    result = parse_relation(target)
    if result is None:
        return False
    result_endpoints = {
        normalize_type_text(result.left),
        normalize_type_text(result.right),
    }
    for evidence_type in evidence_types:
        evidence = parse_relation(evidence_type, expected_operator=result.operator)
        if evidence is None:
            continue
        evidence_endpoints = {
            normalize_type_text(evidence.left),
            normalize_type_text(evidence.right),
        }
        if evidence_endpoints & result_endpoints:
            return True
    return False


def is_higher_order_structural_field(root_domain: str, field_domain: str) -> bool:
    """Recognize a constructor field whose function codomain is the carrier.

    This is a scheduling classification, not a positivity or termination
    judgment.  It therefore uses only name-neutral displayed type shape and
    leaves every proposed recursive call to Agda.
    """

    try:
        field_parts = split_top_level_arrows(field_domain)
    except ValueError:
        return False
    return (
        len(field_parts) > 1
        and normalize_type_text(field_domain) != normalize_type_text(root_domain)
        and result_head(field_parts[-1]) == result_head(root_domain)
    )


def reorders_homogeneous_coordinates(root_type: str) -> bool:
    """Detect a coordinate permutation in a relational result.

    Names and operation spellings are treated as opaque syntax.  The result
    is a scheduling fact only: consumers may propose bounded transposed calls,
    but Agda remains responsible for typing and termination.
    """

    try:
        parts = split_top_level_arrows(root_type)
    except ValueError:
        return False
    named_domains: list[tuple[str, str]] = []
    for part in parts[:-1]:
        binder = parse_named_binder(part)
        if binder is None or binder.visibility != "explicit":
            continue
        named_domains.extend((name, binder.domain) for name in binder.names)
    relation = parse_relation(parts[-1])
    if relation is None:
        return False

    domains = tuple(
        dict.fromkeys(normalize_type_text(domain) for _name, domain in named_domains)
    )
    for domain in domains:
        names = tuple(
            name
            for name, candidate_domain in named_domains
            if normalize_type_text(candidate_domain) == domain
        )
        if len(names) < 2:
            continue

        def occurrence_order(
            endpoint: str, coordinate_names: tuple[str, ...] = names
        ) -> tuple[str, ...]:
            occurrences = (
                (matched.start(), name)
                for name in coordinate_names
                for matched in re.finditer(
                    rf"(?<![\w'′-]){re.escape(name)}(?![\w'′-])",
                    endpoint,
                )
            )
            return tuple(name for _position, name in sorted(occurrences))

        left_order = occurrence_order(relation.left)
        right_order = occurrence_order(relation.right)
        if (
            left_order != right_order
            and sorted(left_order) == sorted(right_order)
            and set(left_order) == set(names)
        ):
            return True
    return False


__all__ = [
    "STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION",
    "StructuralClassification",
    "classify_structural_scheduling",
    "has_relational_context_evidence",
    "has_relational_elimination_shape",
    "has_result_subject_elimination_shape",
    "is_higher_order_structural_field",
    "is_reflexive_relation_target",
    "reorders_homogeneous_coordinates",
]
