"""Model-independent sparse feature extraction for local action rankers."""

from __future__ import annotations

import hashlib
import unicodedata
from collections.abc import Iterable, Mapping

from ..actions import RefinementCandidate
from ..contracts import GoalInfo
from ..reasoning.classifications import StructuralClassification
from ..terms import Term
from ..type_syntax import result_head, top_level_arrow_count


def _bucket(value: int, boundaries: tuple[int, ...]) -> str:
    for boundary in boundaries:
        if value <= boundary:
            return str(boundary)
    return "large"


def _goal_head(target: str) -> str:
    return result_head(target)


def _surface_symbol_tokens(text: str) -> tuple[str, ...]:
    symbols: list[str] = []
    for character in text:
        if not unicodedata.category(character).startswith("S"):
            continue
        if character == "→" or character in symbols:
            continue
        symbols.append(character)
        if len(symbols) == 8:
            break
    return tuple(f"goal-surface-symbol:{symbol}" for symbol in symbols)


def state_feature_tokens(goal: GoalInfo) -> tuple[str, ...]:
    tokens = [
        f"goal-head:{_goal_head(goal.target)}",
        f"goal-arrows:{_bucket(top_level_arrow_count(goal.target), (0, 1, 2, 3))}",
        f"context-size:{_bucket(len(goal.context), (0, 1, 2, 4, 8))}",
    ]
    tokens.extend(_surface_symbol_tokens(goal.target))
    if goal.module_scope is not None:
        tokens.extend(
            (
                f"module-depth:{_bucket(len(goal.module_scope.frames), (1, 2, 3, 4))}",
                f"module-parameters:{_bucket(len(goal.module_scope.parameters), (0, 1, 2, 4, 8))}",
                f"module-directives:{_bucket(len(goal.module_scope.directives), (0, 1, 2, 4, 8))}",
            )
        )
    for entry in goal.context:
        type_head = entry.type.split()[0] if entry.type else "unknown"
        tokens.append(f"context-head:{type_head}")
    return tuple(tokens)


def structural_classification_feature_tokens(
    classification: StructuralClassification,
) -> tuple[str, ...]:
    """Encode symbolic scheduling evidence without giving it logical authority."""

    def encoded(value: bool | None) -> str:
        if value is None:
            return "unknown"
        return str(value).lower()

    return tuple(
        f"structural:{name}={encoded(value)}"
        for name, value in (
            (
                "recursive-result-head-matches-goal",
                classification.recursive_result_head_matches_goal,
            ),
            (
                "construction-result-head-matches-goal",
                classification.construction_result_head_matches_goal,
            ),
            (
                "construction-available",
                classification.structural_construction_available,
            ),
            (
                "productive-elimination-available",
                classification.productive_elimination_available,
            ),
            (
                "structural-descent-available",
                classification.structural_descent_available,
            ),
            (
                "higher-order-structural-descent-available",
                classification.higher_order_structural_descent_available,
            ),
            ("dependencies-ready", classification.dependencies_ready),
            (
                "homogeneous-coordinate-permutation",
                classification.homogeneous_coordinate_permutation,
            ),
            (
                "reflexive-relation-target",
                classification.reflexive_relation_target,
            ),
            (
                "relational-elimination-available",
                classification.relational_elimination_available,
            ),
            (
                "construction-elimination-compete",
                classification.construction_elimination_compete,
            ),
        )
    )


def policy_state_feature_tokens(
    goal: GoalInfo, classification: StructuralClassification
) -> tuple[str, ...]:
    """Shared live/training feature contract for the generic OR-policy head."""

    return (
        *state_feature_tokens(goal),
        *structural_classification_feature_tokens(classification),
    )


def action_feature_tokens(goal: GoalInfo, term: Term) -> tuple[str, ...]:
    root = term.tag
    return (
        f"action-root:{root}",
        f"action-size:{_bucket(term.size, (1, 2, 3, 5, 8, 13))}",
        f"action-depth:{_bucket(term.depth, (1, 2, 3, 4, 6))}",
        f"action-lambdas:{_bucket(term.lambda_count, (0, 1, 2, 3))}",
        f"action-applications:{_bucket(term.application_count, (0, 1, 2, 4))}",
        f"joint:arrows={top_level_arrow_count(goal.target)}:lambdas={term.lambda_count}",
        f"joint:goal={_goal_head(goal.target)}:root={root}",
    )


def refinement_action_feature_tokens(
    goal: GoalInfo, candidate: RefinementCandidate
) -> tuple[str, ...]:
    target = " ".join(goal.target.split())
    local_type = " ".join((candidate.local_type or "").split())
    local_head = _goal_head(local_type) if local_type else "none"
    goal_head = _goal_head(target)
    return (
        "action-family:one-step-refinement",
        f"action-root:{candidate.tag}",
        f"step-local-arrows:{_bucket(top_level_arrow_count(local_type), (0, 1, 2, 3))}",
        f"step-local-result:{local_head}",
        f"joint:goal={goal_head}:step={candidate.tag}",
        f"joint:goal={goal_head}:local-result={local_head}",
        f"joint:exact-local-type={bool(local_type) and local_type == target}",
    )


def hash_features(tokens: Iterable[str], input_size: int) -> dict[int, float]:
    values: dict[int, float] = {}
    for token in tokens:
        digest = hashlib.blake2b(
            token.encode("utf-8"), digest_size=8, person=b"AgdaProverP0"
        ).digest()
        raw = int.from_bytes(digest, "little")
        index = raw % input_size
        sign = -1.0 if raw & (1 << 63) else 1.0
        values[index] = values.get(index, 0.0) + sign
    return values


def merge_sparse(*features: Mapping[int, float]) -> dict[int, float]:
    merged: dict[int, float] = {}
    for feature_set in features:
        for index, value in feature_set.items():
            merged[index] = merged.get(index, 0.0) + value
    return {index: value for index, value in merged.items() if value != 0.0}


def sparse_delta(
    previous: Mapping[int, float], current: Mapping[int, float]
) -> tuple[dict[int, float], dict[int, float]]:
    remove: dict[int, float] = {}
    add: dict[int, float] = {}
    for index in previous.keys() | current.keys():
        difference = current.get(index, 0.0) - previous.get(index, 0.0)
        if difference > 0.0:
            add[index] = difference
        elif difference < 0.0:
            remove[index] = -difference
    return remove, add


__all__ = [
    "action_feature_tokens",
    "hash_features",
    "merge_sparse",
    "policy_state_feature_tokens",
    "refinement_action_feature_tokens",
    "sparse_delta",
    "state_feature_tokens",
    "structural_classification_feature_tokens",
]
