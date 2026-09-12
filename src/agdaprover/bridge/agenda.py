"""Coarse resident run protocol; symbolic planning stays entirely native."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from pathlib import Path
from typing import Any

from .contracts import BridgeBudget
from .project import ResolvedProject
from .resources import CancellationToken
from .symbolic import SymbolicProtocolError, resident_session


def search_agenda(
    executable: Path,
    project: ResolvedProject,
    goal_ids: tuple[int, ...],
    *,
    budget: BridgeBudget,
    work_units: int | None,
    action_limit: int | None,
    ranker: str,
    model_path: Path | None,
    focused_model_path: Path | None,
    focused_search: bool,
    native_path: Path | None,
    cancellation: CancellationToken,
    publish: Callable[[dict[str, Any]], None],
    quantum: int = 64,
    principal_variations: bool = False,
    one_move: bool = False,
) -> Iterator[dict[str, Any]]:
    """Yield provisional exports, resuming after caller rejection.

    The caller must close this generator on early acceptance/failure. A slice
    is not exhaustion, and candidate rejection never starts a new search. One
    supervisor and immutable project overlay span the entire iterator.
    """
    if type(quantum) is not int or quantum <= 0:
        raise ValueError("native scheduling quantum must be positive")
    if type(principal_variations) is not bool:
        raise ValueError("native principal-variation switch must be boolean")
    if type(one_move) is not bool or (one_move and len(goal_ids) != 1):
        raise ValueError("native step must select exactly one goal")
    if (
        not goal_ids
        or any(type(g) is not int or g < 0 for g in goal_ids)
        or len(set(goal_ids)) != len(goal_ids)
    ):
        raise ValueError("native goal selection must be nonempty, unique integers")
    with resident_session(executable, project, budget, cancellation) as connection:
        limits = {"work_units": work_units}
        reply = connection.request(
            "start-step" if one_move else "start-search",
            {
                "state": connection.root_state,
                "goal_ids": list(goal_ids),
                "limits": limits,
                "action_limit": action_limit,
                "ranker": ranker,
                "model_path": str(model_path.resolve()) if model_path else None,
                "focused_model_path": str(focused_model_path.resolve())
                if focused_model_path
                else None,
                "native_path": str(native_path.resolve()) if native_path else None,
                "focused_search": focused_search,
                "exclude_names": [],
            },
            publish,
        )
        current = reply["outcome"]
        if current.get("status") != "ready":
            raise SymbolicProtocolError(f"native agenda could not start: {current}")
        models = current["cost"].get("models")

        def variation() -> dict[str, Any]:
            viewed = connection.request("search-cost", {"run": current["run"]}, publish)
            snapshot = viewed["outcome"]
            if (
                snapshot.get("status") != "retained"
                or snapshot.get("run") != current["run"]
                or snapshot.get("goal_ids") != list(goal_ids)
                or snapshot.get("cost", {}).get("models") != models
            ):
                raise SymbolicProtocolError("native principal snapshot changed its run")
            principal = snapshot.get("principal")
            exports = []
            if principal is not None:
                if (
                    not isinstance(principal, dict)
                    or not isinstance(principal.get("pending"), dict)
                    or not isinstance(principal["pending"].get("goals"), list)
                ):
                    raise SymbolicProtocolError("malformed native principal snapshot")
                for point in goal_ids:
                    if point in principal["pending"]["goals"]:
                        continue
                    exported = connection.request(
                        "export-goals",
                        {
                            "state": connection.root_state,
                            "goal_ids": [point],
                            "descendant": principal["state"],
                        },
                        publish,
                    )["outcome"]
                    if exported.get("status") == "accepted-blocked":
                        continue
                    if exported.get("status") == "rejected":
                        if exported.get("reason") not in {
                            "kernel-rejected",
                            "kernel-blocked",
                        }:
                            raise SymbolicProtocolError(
                                f"native preview export failed: {exported}"
                            )
                        # A consumed source hole can still have unfinished AND
                        # children. That is not an individually complete proof.
                        continue
                    entries = exported.get("entries")
                    if (
                        exported.get("status")
                        not in {"apparently-closed", "accepted-partial"}
                        or not isinstance(entries, list)
                        or len(entries) != 1
                        or not isinstance(entries[0], dict)
                        or entries[0].get("goal_id") != point
                    ):
                        raise SymbolicProtocolError(
                            "native preview changed its source goal"
                        )
                    exports.extend(entries)
            return {
                "outcome": {
                    "status": "principal-variation",
                    "snapshot": snapshot,
                    "entries": exports,
                }
            }

        if principal_variations:
            yield variation()
        while True:
            reply = connection.request(
                "advance-search",
                {"run": current["run"], "steps": quantum, "limits": limits},
                publish,
            )
            current = reply["outcome"]
            if (
                current.get("goal_ids") != list(goal_ids)
                or current.get("cost", {}).get("models") != models
            ):
                raise SymbolicProtocolError(
                    "native agenda changed its selection or models"
                )
            status = current.get("status")
            if (
                principal_variations
                and "run" in current
                and status in {"paused", "candidate"}
            ):
                yield variation()
            refutation = current.get("refutation")
            if refutation is not None and (
                not isinstance(refutation, dict)
                or len(goal_ids) != 1
                or refutation.get("parent") != connection.root_state
                or refutation.get("goal_id") != goal_ids[0]
            ):
                raise SymbolicProtocolError(
                    "native refutation changed its source owner"
                )
            if status == "paused" and current.get("reason") == "slice-ended":
                continue
            if status == "refutation-candidate":
                if refutation is None:
                    raise SymbolicProtocolError(
                        "native refutation candidate is missing"
                    )
                yield reply
                continue
            if status == "candidate":
                exported = connection.request(
                    "export-goals",
                    {
                        "state": connection.root_state,
                        "goal_ids": list(goal_ids),
                        "descendant": current["state"],
                    },
                    publish,
                )
                yield {
                    **reply,
                    "source_export": exported["outcome"],
                    "cost": exported["cost"],
                }
                continue
            yield reply
            return
