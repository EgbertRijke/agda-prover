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
    ranker: str,
    model_path: Path | None,
    focused_model_path: Path | None,
    focused_search: bool,
    native_path: Path | None,
    cancellation: CancellationToken,
    publish: Callable[[dict[str, Any]], None],
    quantum: int = 64,
) -> Iterator[dict[str, Any]]:
    """Yield provisional exports, resuming after caller rejection.

    The caller must close this generator on early acceptance/failure. A slice
    is not exhaustion, and candidate rejection never starts a new search. One
    supervisor and immutable project overlay span the entire iterator.
    """
    if type(quantum) is not int or quantum <= 0:
        raise ValueError("native scheduling quantum must be positive")
    if (
        not goal_ids
        or any(type(g) is not int or g < 0 for g in goal_ids)
        or len(set(goal_ids)) != len(goal_ids)
    ):
        raise ValueError("native goal selection must be nonempty, unique integers")
    with resident_session(executable, project, budget, cancellation) as connection:
        limits = {"work_units": work_units}
        reply = connection.request(
            "start-search",
            {
                "state": connection.root_state,
                "goal_ids": list(goal_ids),
                "limits": limits,
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
            if status == "paused" and current.get("reason") == "slice-ended":
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
