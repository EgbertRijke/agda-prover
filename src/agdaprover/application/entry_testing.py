"""Sequential independent entry tests over a private project workspace."""

from __future__ import annotations

import tempfile
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from typing import Any

from ..bridge.compat_p0 import AgdaBridgeError
from ..bridge.contracts import BridgeBudget, BridgeError
from ..bridge.source_entries import inspect_entries
from ..bridge.source_prefix import independent_prefix, inspect_prefix
from ..contracts import ProverResult, TaskSpec
from ..presentation.entry_testing import virtual_entry
from ..resource_budget import ResourceLimitError
from ..verification import ValidationError, prepare_project_overlay
from .inspection import CommandResult

ENTRY_TEST_SCHEMA = "agdaprover.entry-tests.v1"


def test_entries(
    task: TaskSpec,
    *,
    solve: Callable[[TaskSpec], ProverResult],
    publish: Callable[[str, dict[str, Any]], None],
) -> CommandResult:
    """Replace only the current definition in a fresh original-source view.

    Each solve has its own ordinary task allowance. Neither the original source
    nor the editor buffer is changed, and no completion becomes the next test's
    premise. Results are streamed rather than accumulated in controller memory.
    """
    total = attempted = solved = 0
    current: dict[str, Any] | None = None

    def summary(status: str, diagnostic: str = "") -> CommandResult:
        return CommandResult(
            0 if status == "completed" else 130 if status == "cancelled" else 2,
            {
                "schema_version": ENTRY_TEST_SCHEMA,
                "status": status,
                "total": total,
                "attempted": attempted,
                "solved": solved,
                "failed_entry": current if status == "stopped" else None,
                "diagnostic": diagnostic,
            },
        )

    try:
        original_bytes = task.source_file.read_bytes()
        original = original_bytes.decode("utf-8")

        def unchanged() -> None:
            if task.source_file.read_bytes() != original_bytes:
                raise ValueError("Source changed during entry testing; run stopped")

        wall = task.timeout_seconds or float("inf")
        entries = inspect_entries(
            task.source_file, original, BridgeBudget.for_run(wall)
        )
        total = len(entries)
        publish("started", {"total": total})
        if not entries:
            return summary("completed")
        with tempfile.TemporaryDirectory(prefix="agdaprover-entry-tests-") as directory:
            workspace = prepare_project_overlay(
                task.source_file,
                original,
                Path(directory),
                project_configuration=task.project_configuration,
                timeout_seconds=wall,
            )
            if not workspace.source_file.resolve().is_relative_to(
                Path(directory).resolve()
            ):
                raise ValueError("Entry workspace is not private")
            for index, entry in enumerate(entries, 1):
                unchanged()
                current = {
                    "index": index,
                    "name": entry.name,
                    "line": original.count("\n", 0, entry.start) + 1,
                }
                publish("entry-started", current)
                attempted += 1
                if entry.reason:
                    publish(
                        "entry-result",
                        {
                            **current,
                            "status": "unsupported",
                            "solution": None,
                            "diagnostic": entry.reason,
                        },
                    )
                    return summary("stopped", entry.reason)
                candidate, position = virtual_entry(
                    original,
                    entry,
                    literate=task.source_file.name.endswith(".lagda.md"),
                )
                workspace.source_file.write_text(
                    candidate, encoding="utf-8", newline=""
                )
                # Test the entry, not the compatibility of a replacement with
                # its later clients. Agda owns the enclosing checking boundary;
                # mutual/record groups stay intact. No preceding entry is
                # omitted or substituted with a completion from this run.
                parsed = inspect_prefix(
                    workspace.source_file,
                    candidate,
                    position + 3,
                    BridgeBudget.for_run(wall),
                )
                if parsed["status"] != "parsed":
                    diagnostic = parsed.get("reason", parsed["status"])
                    publish(
                        "entry-result",
                        {
                            **current,
                            "status": "resource-exhausted"
                            if parsed["status"] == "resource-exhausted"
                            else "unsupported",
                            "solution": None,
                            "diagnostic": diagnostic,
                        },
                    )
                    return summary("stopped", diagnostic)
                prefix, _ = independent_prefix(
                    candidate,
                    parsed,
                    entry.start,
                    (),
                    allow_omissions=False,
                )
                workspace.source_file.write_text(prefix, encoding="utf-8", newline="")
                result = solve(
                    replace(
                        task,
                        source_file=workspace.source_file,
                        goal_id=None,
                        goal_position=position,
                        project_configuration=workspace.configuration,
                    )
                )
                unchanged()
                solution = (result.patch or {}).get("replacement", result.proof_term)
                verified = (
                    result.status == "verified"
                    and result.validation is not None
                    and result.validation.get("fresh_process") is True
                    and result.validation.get("checked") is True
                    and isinstance(solution, str)
                    and bool(solution.strip())
                )
                diagnostic = "; ".join(
                    str(d.get("message", "")) for d in result.diagnostics
                )
                status = result.status
                if status == "verified" and not verified:
                    status, diagnostic = (
                        "internal-error",
                        "Completion lacks a solution or fresh validation",
                    )
                publish(
                    "entry-result",
                    {
                        **current,
                        "status": status,
                        "solution": solution if verified else None,
                        "elapsed_ms": result.elapsed_ms,
                        "cost": result.cost.to_dict(),
                        "diagnostic": diagnostic,
                        "validation": result.validation,
                        "validation_scope": "entry-prefix",
                    },
                )
                if not verified:
                    return summary("stopped", diagnostic)
                solved += 1
        unchanged()
        return summary("completed")
    except KeyboardInterrupt:
        return summary("cancelled", "Entry testing cancelled")
    except (
        OSError,
        ValueError,
        TimeoutError,
        ResourceLimitError,
        AgdaBridgeError,
        BridgeError,
        ValidationError,
    ) as error:
        return summary("stopped", str(error))
