"""Ownership of serialized native source exports, not search-state collection."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

from ..resource_budget import ResourceLimitError
from .symbolic import SymbolicConnection, SymbolicProtocolError


def export_source_batch(
    connection: SymbolicConnection,
    goal_ids: tuple[int, ...],
    descendant: dict[str, Any],
    publish: Callable[[dict[str, Any]], None],
) -> dict[str, Any]:
    """Copy the checked source view and relinquish its temporary native states.

    Native export checks a fresh branch; it does not reuse the search branch.
    Only this bridge consumes the new handles. Serialized proof data and their
    provenance remain usable for independent validation after release. The
    original descendant, run, alternatives and replay ancestry are untouched.
    Direct session-protocol callers retain the ordinary explicit lifetime API.
    """
    reply = connection.request(
        "export-goals",
        {
            "state": connection.root_state,
            "goal_ids": list(goal_ids),
            "descendant": descendant,
        },
        publish,
    )
    outcome = reply["outcome"]
    if outcome.get("status") == "rejected":
        # Native reconstruction is atomic; rejection publishes no new states.
        if "state" in outcome or "entries" in outcome:
            raise SymbolicProtocolError("rejected export published checking states")
        if outcome.get("reason") == "cancelled":
            raise ResourceLimitError("native source export was cancelled")
        return reply
    if outcome.get("status") not in {
        "apparently-closed",
        "accepted-partial",
        "accepted-blocked",
    }:
        raise SymbolicProtocolError("unknown native source export status")
    entries = outcome.get("entries")
    if not isinstance(entries, list) or not entries or len(entries) != len(goal_ids):
        raise SymbolicProtocolError("native export changed its selected entries")
    if (
        not isinstance(descendant, dict)
        or set(descendant) != {"session", "epoch", "branch"}
        or not isinstance(descendant["session"], str)
        or not descendant["session"]
        or type(descendant["epoch"]) is not int
        or descendant["epoch"] < 0
        or type(descendant["branch"]) is not int
        or descendant["branch"] < 0
    ):
        raise SymbolicProtocolError("invalid native export parent identity")
    previous = descendant["branch"]
    states = []
    for point, entry in zip(goal_ids, entries, strict=True):
        if (
            not isinstance(entry, dict)
            or type(entry.get("goal_id")) is not int
            or entry["goal_id"] != point
            or not isinstance(entry.get("evidence"), dict)
        ):
            raise SymbolicProtocolError("native export changed its selected entries")
        state = entry["evidence"].get("state")
        if (
            not isinstance(state, dict)
            or set(state) != {"session", "epoch", "branch"}
            or state["session"] != descendant["session"]
            or type(state["epoch"]) is not int
            or state["epoch"] != descendant["epoch"]
            or type(state["branch"]) is not int
            or state["branch"] <= previous
        ):
            raise SymbolicProtocolError(
                "native export did not issue a fresh owned branch"
            )
        previous = state["branch"]
        states.append(state)
    final = outcome.get("state")
    if (
        not isinstance(final, dict)
        or type(final.get("epoch")) is not int
        or type(final.get("branch")) is not int
        or final != states[-1]
    ):
        raise SymbolicProtocolError("native export changed its final checking state")
    # Validate the entire batch before any release; never guess at an unknown
    # owner. Malformed replies or interrupted cleanup close the scoped session.
    cost = reply["cost"]
    for state in reversed(states):
        released = connection.request("release", {"state": state}, publish)
        if released["outcome"].get("reason") == "cancelled":
            raise ResourceLimitError("native source export release was cancelled")
        if released["outcome"].get("status") != "released":
            raise SymbolicProtocolError("native source export release failed")
        cost = released["cost"]
    return {**reply, "cost": cost}
