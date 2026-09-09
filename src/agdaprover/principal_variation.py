"""Versioned, provisional principal-variation snapshots.

Snapshots are observations of search order.  They carry no proof authority;
only an advertised one-goal reconstruction that passes a separate fresh Agda
validation may be offered for editor application.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

from .contracts import GoalInfo
from .presentation import apply_source_edit

PRINCIPAL_VARIATION_SCHEMA = "agdaprover.principal-variation.v1"
MAX_PRINCIPAL_VARIATION_BYTES = 4 * 1024 * 1024
PrincipalVariationObserver = Callable[[dict[str, Any]], None]

_OPEN_GOAL = re.compile(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])")


def _acceptance_options(
    original_source: str,
    target_goals: Sequence[GoalInfo],
    steps: Sequence[Mapping[str, object]],
) -> list[dict[str, Any]]:
    """Return only complete steps replayable against the original snapshot."""

    options: dict[int, dict[str, Any]] = {}
    for raw_step in steps:
        step = dict(raw_step)
        replacement = step.get("replacement")
        source_range = step.get("source_range")
        if (
            not isinstance(replacement, str)
            or _OPEN_GOAL.search(replacement)
            or not isinstance(source_range, list)
            or len(source_range) != 2
            or not all(type(value) is int for value in source_range)
        ):
            continue
        try:
            apply_source_edit(original_source, step)
        except ValueError:
            continue
        start, end = source_range
        owners = [
            goal
            for goal in target_goals
            if start <= goal.source_range[0] and goal.source_range[1] <= end
        ]
        if len(owners) != 1:
            continue
        goal = owners[0]
        options[goal.goal_id] = {
            "goal_id": goal.goal_id,
            "target": goal.target,
            "proof_term": step.get("body", replacement),
            "patch": step,
        }
    return [options[goal_id] for goal_id in sorted(options)]


def joint_principal_variation(
    *,
    task_id: str,
    source_file: Path,
    source_sha256: str,
    target_goals: Sequence[GoalInfo],
    remaining_goals: Sequence[GoalInfo],
    active_goal: GoalInfo | None,
    priority: Sequence[int],
    depth: int,
    steps: Sequence[Mapping[str, object]],
    states_expanded: int,
    frontier_size: int,
    original_source: str,
) -> dict[str, Any]:
    """Construct a bounded provisional view of the best live joint branch."""

    step_list = [dict(step) for step in steps]
    payload: dict[str, Any] = {
        "schema_version": PRINCIPAL_VARIATION_SCHEMA,
        "mode": "prove-prefix",
        "task_id": task_id,
        "source_file": str(source_file),
        "source_sha256": source_sha256,
        "target_goal_ids": [goal.goal_id for goal in target_goals],
        "remaining_goals": [goal.to_dict() for goal in remaining_goals],
        "active_goal": active_goal.to_dict() if active_goal is not None else None,
        "priority": list(priority),
        "depth": depth,
        "steps": step_list,
        "acceptance_options": _acceptance_options(
            original_source, target_goals, step_list
        ),
        "search": {
            "states_expanded": states_expanded,
            "frontier_size": frontier_size,
        },
    }
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    payload["variation_id"] = hashlib.sha256(encoded).hexdigest()[:24]
    return payload


def validate_principal_variation(value: object) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError("principal variation must be an object")
    if value.get("schema_version") != PRINCIPAL_VARIATION_SCHEMA:
        raise ValueError("unsupported principal-variation schema")
    for name in ("variation_id", "task_id", "source_file", "source_sha256"):
        if not isinstance(value.get(name), str) or not value[name]:
            raise ValueError(f"principal variation has invalid {name}")
    if not re.fullmatch(r"[0-9a-f]{24}", value["variation_id"]):
        raise ValueError("principal variation has invalid variation ID")
    identity_payload = dict(value)
    claimed_identity = identity_payload.pop("variation_id")
    encoded = json.dumps(
        identity_payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    if hashlib.sha256(encoded).hexdigest()[:24] != claimed_identity:
        raise ValueError("principal variation identity does not match its payload")
    if not re.fullmatch(r"[0-9a-f]{64}", value["source_sha256"]):
        raise ValueError("principal variation has invalid source hash")
    options = value.get("acceptance_options")
    if not isinstance(options, list):
        raise ValueError("principal variation has invalid acceptance options")
    for option in options:
        if (
            not isinstance(option, dict)
            or type(option.get("goal_id")) is not int
            or not isinstance(option.get("patch"), dict)
        ):
            raise ValueError("principal variation has malformed acceptance option")
    return value


class AtomicPrincipalVariationPublisher:
    """Publish the latest snapshot atomically for an interactive supervisor."""

    def __init__(self, path: Path) -> None:
        self.path = path

    def __call__(self, variation: dict[str, Any]) -> None:
        validated = validate_principal_variation(variation)
        encoded = (
            json.dumps(validated, sort_keys=True, ensure_ascii=False) + "\n"
        ).encode("utf-8")
        if len(encoded) > MAX_PRINCIPAL_VARIATION_BYTES:
            return
        temporary = self.path.with_name(f".{self.path.name}.{os.getpid()}.tmp")
        temporary.write_bytes(encoded)
        os.replace(temporary, self.path)


def load_principal_variation(path: Path) -> dict[str, Any] | None:
    try:
        size = path.stat().st_size
    except FileNotFoundError:
        return None
    if size > MAX_PRINCIPAL_VARIATION_BYTES:
        raise ValueError("principal-variation snapshot exceeds its byte limit")
    return validate_principal_variation(json.loads(path.read_text()))
