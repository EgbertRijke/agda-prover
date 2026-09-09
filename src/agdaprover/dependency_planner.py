"""Kernel-safe action ordering derived from generic dependency towers.

The planner has no built-in knowledge of any datatype. Optional hints must be
injected through a generic interface and may influence order only; Agda still
generates and checks every elimination.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Protocol

from .contracts import GoalInfo
from .dependency_tower import DependencyTower, tower_from_goal
from .dependent_actions import DependentEliminationAction, EliminationReason
from .type_syntax import normalize_type_text, result_head


def goal_has_concrete_nullary_scrutinee(goal: GoalInfo) -> bool:
    """Whether generic batched case analysis has an especially cheap subject.

    This is deliberately only a scheduling hint. It names no datatype and
    grants no logical rule: Agda must still accept the resulting case split.
    """

    abstract_heads = {
        entry.name
        for entry in goal.context
        if entry.in_scope and entry.name and result_head(entry.type).startswith("Set")
    }
    for entry in goal.context:
        if not entry.in_scope or not entry.name:
            continue
        type_text = normalize_type_text(entry.type)
        if (
            not type_text
            or "→" in type_text
            or any(character.isspace() for character in type_text)
            or any(delimiter in type_text for delimiter in "(){}[]")
        ):
            continue
        if result_head(type_text) in abstract_heads:
            continue
        if re.search(rf"(?<![\w']){re.escape(entry.name)}(?![\w'])", goal.target):
            return True
    return False


@dataclass(frozen=True)
class PlanningHints:
    """Datatype-neutral ordering hints from an optional metadata provider."""

    preferred_names: tuple[str, ...] = ()


class PlanningHintProvider(Protocol):
    """Inject optional constructor/index metadata without extending the core."""

    def __call__(self, goal: GoalInfo, tower: DependencyTower) -> PlanningHints: ...


@dataclass(frozen=True)
class DependencyPlan:
    tower: DependencyTower
    preferred_names: tuple[str, ...]
    depths: tuple[int, ...]
    children: tuple[tuple[int, ...], ...]
    result_cone: frozenset[int]
    proof_relevant_nodes: int
    parallel_inhabitants: int

    def priority(self, name: str) -> tuple[int, int, int, int, int, int]:
        """Return a deterministic, low-is-good priority for a case variable."""

        node = self.tower.visible_node(name)
        if node is None:
            return (2, 2, 2, 0, 0, len(self.tower.nodes))
        try:
            preferred_rank = self.preferred_names.index(name)
        except ValueError:
            preferred_rank = len(self.preferred_names) + 1
        return (
            0 if name in self.preferred_names else 1,
            preferred_rank,
            # Eliminate the most dependent cell before its indices.  Such a
            # cell can constrain several result-relevant predecessors at
            # once, whereas splitting a predecessor first usually destroys
            # the strongest computation rule and multiplies branches.
            -self.depths[node.node_id],
            0 if node.node_id in self.tower.result_dependencies else 1,
            0 if node.node_id in self.result_cone else 1,
            -len(self.children[node.node_id]),
        )

    def is_dependency_guided(self, name: str) -> bool:
        node = self.tower.visible_node(name)
        if node is None:
            return False
        return (
            name in self.preferred_names
            or node.node_id in self.result_cone
            or bool(self.children[node.node_id])
        )

    def elimination_action(self, name: str) -> DependentEliminationAction | None:
        node = self.tower.visible_node(name)
        if node is None:
            return None
        reason: EliminationReason
        if name in self.preferred_names:
            reason = "preferred-inhabitant"
        elif node.node_id in self.tower.result_dependencies:
            reason = "result-index"
        elif node.node_id in self.result_cone:
            reason = "target-ancestor"
        elif self.children[node.node_id]:
            reason = "dependent-descendant"
        else:
            reason = "fallback"
        return DependentEliminationAction(
            node_id=node.node_id,
            name=node.name,
            type_text=node.type_text,
            dependencies=node.dependencies,
            instantiation_dependencies=self.tower.instantiation_dependencies(
                node.node_id
            ),
            dependency_depth=self.depths[node.node_id],
            reason=reason,
        )


def _parallel_inhabitant_count(tower: DependencyTower) -> int:
    counts: dict[str, int] = {}
    for node in tower.nodes:
        if node.origin == "context":
            counts[node.type_text] = counts.get(node.type_text, 0) + 1
    return sum(count - 1 for count in counts.values() if count > 1)


def build_dependency_plan(
    goal: GoalInfo,
    *,
    hint_provider: PlanningHintProvider | None = None,
) -> DependencyPlan:
    tower = tower_from_goal(goal)
    hints = PlanningHints() if hint_provider is None else hint_provider(goal, tower)
    if len(set(hints.preferred_names)) != len(hints.preferred_names):
        raise ValueError("planning hints contain duplicate inhabitants")
    return DependencyPlan(
        tower=tower,
        preferred_names=hints.preferred_names,
        depths=tower.depths(),
        children=tower.children(),
        result_cone=tower.result_cone(),
        proof_relevant_nodes=len(tower.nodes),
        parallel_inhabitants=_parallel_inhabitant_count(tower),
    )


def goal_has_dependency_tower(goal: GoalInfo) -> bool:
    """Cheap routing predicate for root goals with dependent binders."""

    try:
        return tower_from_goal(goal).has_runtime_dependency()
    except ValueError:
        # This is a performance route only. Syntax outside the lightweight
        # scanner must fall back to ordinary kernel-guided search.
        return False
