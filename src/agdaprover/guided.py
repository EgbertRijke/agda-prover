"""Bounded best-first AND/OR search over Agda-checked source states."""

from __future__ import annotations

import hashlib
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from .actions import RefinementCandidate
from .bridge.resources import temporary_workspace
from .budget import action_limit_view
from .contracts import GoalInfo
from .focused import focused_prove
from .kernel.p0 import AgdaLoadError, AgdaSession, open_kernel_session
from .kernel.protocol import KernelSessionFactory
from .or_policy import ORPolicyRouter, policy_candidate
from .presentation import (
    apply_source_edit,
    guided_clause_region,
    reconstruct_case_split,
    reconstruct_guided_completion,
    reconstruct_hole_completion,
    reconstruct_intro,
)
from .project_configuration import ProjectConfiguration
from .ranking.protocol import SparsePolicyRanker
from .resource_budget import charge_io
from .search_frontier import BatchedFrontier
from .terms import render_term
from .type_syntax import top_level_arrow_count
from .verification import prepare_project_overlay

GUIDED_ALGORITHM = "agda-guided-best-first-and-or-v1"


@dataclass
class GuidedStats:
    algorithm: str = GUIDED_ALGORITHM
    states_expanded: int = 0
    states_enqueued: int = 0
    transposition_hits: int = 0
    actions_considered: int = 0
    actions_generated: int = 0
    depth_pruned: int = 0
    max_depth: int = 0
    kernel_loads: int = 0
    kernel_load_elapsed_ms: float = 0.0
    goal_inspections: int = 0
    refinement_queries: int = 0
    case_queries: int = 0
    generated_subgoals: int = 0
    model_calls: int = 0
    model_batches: int = 0
    model_elapsed_ms: float = 0.0
    elapsed_ms: float = 0.0
    depth_limit: int | None = None
    source_bytes_materialized: int = 0
    source_bytes_written: int = 0
    focused: dict[str, int | float] = field(default_factory=dict)

    def to_dict(self) -> dict[str, object]:
        return {
            "algorithm": self.algorithm,
            "states_expanded": self.states_expanded,
            "states_enqueued": self.states_enqueued,
            "transposition_hits": self.transposition_hits,
            "actions_considered": self.actions_considered,
            "actions_generated": self.actions_generated,
            "depth_pruned": self.depth_pruned,
            "max_depth": self.max_depth,
            "kernel_loads": self.kernel_loads,
            "kernel_load_elapsed_ms": self.kernel_load_elapsed_ms,
            "goal_inspections": self.goal_inspections,
            "refinement_queries": self.refinement_queries,
            "case_queries": self.case_queries,
            "generated_subgoals": self.generated_subgoals,
            "model_calls": self.model_calls,
            "model_batches": self.model_batches,
            "model_elapsed_ms": self.model_elapsed_ms,
            "elapsed_ms": self.elapsed_ms,
            "depth_limit": self.depth_limit,
            "source_bytes_materialized": self.source_bytes_materialized,
            "source_bytes_written": self.source_bytes_written,
            "focused": self.focused,
        }


@dataclass(frozen=True)
class GuidedResult:
    status: Literal["solved", "no-proof", "resource-exhausted"]
    patch: dict[str, object] | None
    proof_text: str | None
    stats: GuidedStats
    diagnostic: str = ""


@dataclass(order=True)
class _State:
    priority: tuple[int, int, int]
    sequence: int
    replacement: str = field(compare=False)
    depth: int = field(compare=False)


def guided_prove(
    source_file: Path,
    root_goal: GoalInfo,
    *,
    action_budget: float,
    timeout_seconds: float,
    max_depth: int | None,
    focused_model: SparsePolicyRanker | None,
    refinement_model: SparsePolicyRanker | None,
    policy_router: ORPolicyRouter | None = None,
    session_factory: KernelSessionFactory = AgdaSession,
    project_configuration: ProjectConfiguration | None = None,
) -> GuidedResult:
    """Search constructor and case branches while every state remains Agda-loadable."""

    started = time.monotonic()
    deadline = started + timeout_seconds
    stats = GuidedStats(depth_limit=max_depth)
    original_source = source_file.read_text()
    try:
        region_start, initial_end = guided_clause_region(original_source, root_goal)
    except ValueError as error:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return GuidedResult("no-proof", None, None, stats, str(error))

    queue = BatchedFrontier[_State]()
    sequence = 0
    initial_replacement = original_source[region_start:initial_end]
    initial_state = _State((1, 1, sequence), sequence, initial_replacement, 0)
    queue.push(initial_state.priority, initial_state.sequence, initial_state)
    stats.states_enqueued = 1
    seen: set[str] = set()
    queued = {hashlib.sha256(initial_replacement.encode("utf-8")).hexdigest()}
    saw_exhaustion = False
    active_policy = policy_router or ORPolicyRouter(
        focused_model=focused_model,
        refinement_model=refinement_model,
        budget_envelope={
            "max_actions": action_limit_view(action_budget),
            "max_depth": max_depth,
            "timeout_seconds": timeout_seconds,
        },
    )
    focused_policy = active_policy.focused_policy

    def charge() -> bool:
        nonlocal saw_exhaustion
        if time.monotonic() >= deadline or stats.actions_considered >= action_budget:
            saw_exhaustion = True
            return False
        stats.actions_considered += 1
        return True

    def enqueue(
        source: str,
        region_end: int,
        depth: int,
        estimated_open_goals: int,
    ) -> None:
        nonlocal sequence
        digest = hashlib.sha256(
            source[region_start:region_end].encode("utf-8")
        ).hexdigest()
        if digest in seen or digest in queued:
            stats.transposition_hits += 1
            return
        replacement = source[region_start:region_end]
        queued.add(digest)
        sequence += 1
        estimated = max(0, estimated_open_goals)
        next_state = _State(
            (depth + estimated, estimated, sequence),
            sequence,
            replacement,
            depth,
        )
        queue.push(next_state.priority, next_state.sequence, next_state)
        stats.states_enqueued += 1

    with temporary_workspace(prefix="agdaprover-guided-") as temporary:
        workspace = prepare_project_overlay(
            source_file,
            original_source,
            Path(temporary),
            project_configuration=project_configuration,
            timeout_seconds=deadline - time.monotonic(),
        )
        candidate_path = workspace.source_file
        stats.source_bytes_materialized += workspace.total_bytes
        stats.source_bytes_written += workspace.total_bytes
        with open_kernel_session(
            session_factory,
            project_configuration=workspace.configuration,
            timeout_seconds=timeout_seconds,
            deadline=deadline,
        ) as session:
            while queue:
                if (
                    time.monotonic() >= deadline
                    or stats.actions_considered >= action_budget
                ):
                    saw_exhaustion = True
                    break
                state = queue.pop()
                digest = hashlib.sha256(state.replacement.encode("utf-8")).hexdigest()
                queued.discard(digest)
                if digest in seen:
                    stats.transposition_hits += 1
                    continue
                seen.add(digest)
                stats.states_expanded += 1
                stats.max_depth = max(stats.max_depth, state.depth)
                if time.monotonic() >= deadline:
                    saw_exhaustion = True
                    break

                state_source = (
                    original_source[:region_start]
                    + state.replacement
                    + original_source[initial_end:]
                )
                state_region_end = region_start + len(state.replacement)
                stats.source_bytes_materialized += len(state_source.encode("utf-8"))
                candidate_path.write_text(state_source)
                charge_io(len(state_source.encode()))
                stats.source_bytes_written += len(state_source.encode("utf-8"))
                stats.kernel_loads += 1
                load_started = time.monotonic()
                try:
                    loaded = session.load_module(candidate_path)
                except AgdaLoadError:
                    continue
                finally:
                    stats.kernel_load_elapsed_ms += (
                        time.monotonic() - load_started
                    ) * 1000.0
                target_goals = tuple(
                    goal
                    for goal in loaded
                    if region_start <= goal.source_range[0] - 1
                    and goal.source_range[1] - 1 <= state_region_end
                )
                if not target_goals:
                    try:
                        patch = reconstruct_guided_completion(
                            original_source, root_goal, state.replacement
                        )
                    except ValueError:
                        continue
                    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                    if focused_policy is not None:
                        stats.focused["nnue_actions_scored"] = (
                            focused_policy.actions_scored
                        )
                    return GuidedResult("solved", patch, state.replacement, stats)

                if max_depth is not None and state.depth >= max_depth:
                    stats.depth_pruned += 1
                    saw_exhaustion = True
                    continue

                selected = min(target_goals, key=lambda goal: goal.source_range)
                goal = session.inspect_goal(selected)
                stats.goal_inspections += 1
                remaining_actions = action_budget - stats.actions_considered
                if remaining_actions <= 0:
                    saw_exhaustion = True
                    break
                focused = focused_prove(
                    goal,
                    action_budget=remaining_actions,
                    timeout_seconds=max(0.0, deadline - time.monotonic()),
                    max_depth=(None if max_depth is None else max_depth - state.depth),
                    branch_scorer=(
                        active_policy.score_focused
                        if focused_policy is not None
                        else None
                    ),
                )
                stats.actions_considered += focused.stats.actions_considered
                stats.actions_generated += focused.stats.actions_generated
                stats.model_calls += focused.stats.model_calls
                stats.model_batches += focused.stats.policy_nodes
                stats.model_elapsed_ms += focused.stats.model_elapsed_ms
                for name in ("nodes_expanded", "cache_hits", "cycles_pruned"):
                    stats.focused[name] = int(stats.focused.get(name, 0)) + int(
                        getattr(focused.stats, name)
                    )
                if focused.status == "resource-exhausted":
                    saw_exhaustion = True
                    if focused.exhaustion_kind != "depth":
                        continue
                current_open = len(target_goals)
                if focused.term is not None:
                    rendered = render_term(focused.term)
                    next_source, next_end = _replace_goal(
                        state_source,
                        goal,
                        rendered,
                        region_end=state_region_end,
                    )
                    enqueue(next_source, next_end, state.depth + 1, current_open - 1)
                    continue

                # Empty refinement is deterministic: it introduces function
                # binders or the unique constructor selected by Agda.
                if not charge():
                    break
                stats.actions_generated += 1
                checked = session.check_refinement(goal.goal_id, "")
                stats.refinement_queries += 1
                if checked.accepted and checked.preview is not None:
                    if top_level_arrow_count(goal.target):
                        edit = reconstruct_intro(state_source, goal, checked.preview)
                        next_source = apply_source_edit(state_source, edit)
                        next_end = (
                            state_region_end
                            + len(edit["replacement"])
                            - len(edit["original"])
                        )
                    else:
                        next_source, next_end = _replace_goal(
                            state_source,
                            goal,
                            checked.preview,
                            region_end=state_region_end,
                        )
                    generated = max(1, checked.preview.count("?"))
                    stats.generated_subgoals += generated
                    enqueue(
                        next_source,
                        next_end,
                        state.depth + 1,
                        current_open - 1 + generated,
                    )
                    continue

                case_actions = [
                    RefinementCandidate.case_split(entry.name, entry.type)
                    for entry in goal.context
                    if entry.in_scope and entry.name
                ]
                case_actions.sort(key=lambda action: action.symbolic_key(goal))
                stats.actions_generated += len(case_actions)
                before_items = active_policy.model_items_scored
                before_batches = active_policy.model_batches
                before_elapsed = active_policy.model_elapsed_ms
                ranked = active_policy.rank(
                    goal,
                    tuple(
                        policy_candidate(
                            family="case-variable",
                            tag=action.tag,
                            expression=action.expression,
                            type_text=action.local_type or "unknown",
                            symbolic_key=action.symbolic_key(goal),
                        )
                        for action in case_actions
                    ),
                )
                by_expression = {action.expression: action for action in case_actions}
                case_actions = [
                    by_expression[candidate.expression]
                    for candidate in ranked.candidates
                ]
                stats.model_calls += active_policy.model_items_scored - before_items
                stats.model_batches += active_policy.model_batches - before_batches
                stats.model_elapsed_ms += (
                    active_policy.model_elapsed_ms - before_elapsed
                )

                for action in case_actions:
                    if not charge():
                        break
                    active_policy.mark("case-variable", action.expression)
                    checked_case = session.check_case_split(
                        goal.goal_id, action.expression
                    )
                    stats.case_queries += 1
                    if not checked_case.accepted:
                        active_policy.mark(
                            "case-variable", action.expression, outcome="invalid"
                        )
                        continue
                    try:
                        edit = reconstruct_case_split(
                            state_source, goal, checked_case.clauses
                        )
                    except ValueError:
                        continue
                    next_source = apply_source_edit(state_source, edit)
                    next_end = (
                        state_region_end
                        + len(edit["replacement"])
                        - len(edit["original"])
                    )
                    enqueue(
                        next_source,
                        next_end,
                        state.depth + 1,
                        current_open - 1 + len(checked_case.clauses),
                    )
                    stats.generated_subgoals += len(checked_case.clauses)

    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
    if focused_policy is not None:
        stats.focused["nnue_actions_scored"] = focused_policy.actions_scored
    if saw_exhaustion:
        return GuidedResult(
            "resource-exhausted",
            None,
            None,
            stats,
            "guided action, depth, or wall-time budget exhausted",
        )
    return GuidedResult("no-proof", None, None, stats)


def _replace_goal(
    source: str,
    goal: GoalInfo,
    replacement: str,
    *,
    region_end: int,
) -> tuple[str, int]:
    start = goal.source_range[0] - 1
    end = goal.source_range[1] - 1
    if start < 0 or end <= start or end > len(source):
        raise ValueError("Agda returned an invalid guided goal range")
    selected = source[start:end]
    if not (selected == "?" or (selected.startswith("{!") and selected.endswith("!}"))):
        raise ValueError("guided goal range does not select a source hole")
    try:
        edit = reconstruct_hole_completion(source, goal, replacement)
    except ValueError:
        # Agda previews deliberately contain fresh holes.  Those transitional
        # states are not completed proof terms and therefore remain outside
        # the formatter's scope.
        candidate = source[:start] + replacement + source[end:]
        return candidate, region_end + len(replacement) - len(selected)
    candidate = apply_source_edit(source, edit)
    rendered = str(edit["replacement"])
    return candidate, region_end + len(rendered) - len(selected)
