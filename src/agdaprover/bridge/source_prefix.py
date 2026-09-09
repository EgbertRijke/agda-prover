"""Kernel-parser-owned declaration boundaries for fresh prefix validation."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import time
from pathlib import Path
from typing import Any

from .contracts import BridgeBudget
from .resources import CancellationToken
from .validator import _run_checker

SCHEMA = "agdaprover.source-prefix.v1"
MAX_SOURCE_BYTES = 4 * 1024**2


def parser_executable() -> Path | None:
    """Use an explicitly built parser; never compile or download during solving."""
    configured = os.environ.get("AGDAPROVER_SOURCE_PARSER")
    if configured is not None:
        candidate = Path(configured)
    else:
        installed = shutil.which("agdaprover-source-parser")
        candidate = (
            Path(installed)
            if installed
            else Path(__file__).resolve().parents[3]
            / "native/source-parser/target/agdaprover-source-parser"
        )
    return (
        candidate.resolve()
        if candidate.is_file() and os.access(candidate, os.X_OK)
        else None
    )


def inspect_prefix(
    source_file: Path, source: str, end: int, budget: BridgeBudget
) -> dict[str, Any]:
    """Propose a whole-declaration end, not proof acceptance or name resolution."""
    if type(end) is not int or not 0 < end <= len(source):
        raise ValueError("invalid-prefix-position")
    raw = source.encode("utf-8")
    if len(raw) > MAX_SOURCE_BYTES:
        return {"status": "resource-exhausted", "reason": "prefix-source-size-limit"}
    position = len(source[:end].rstrip()) - 1
    if position < 0:
        raise ValueError("empty-prefix")
    executable = parser_executable()
    if executable is None:
        return {"status": "unavailable", "reason": "prefix-parser-unavailable"}
    digest = hashlib.sha256(executable.read_bytes()).hexdigest()
    if source_file.read_bytes() != raw:
        raise OSError("prefix-source-changed")
    run = _run_checker(
        (str(executable), "--prefix", str(position), str(source_file)),
        overlay=source_file.parent,
        budget=budget,
        cancellation=CancellationToken(),
    )
    if (
        source_file.read_bytes() != raw
        or hashlib.sha256(executable.read_bytes()).hexdigest() != digest
    ):
        raise OSError("prefix-parser-or-source-changed")
    evidence = {
        "parser_sha256": digest,
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "elapsed_ms": run.elapsed_ms,
        "peak_rss_bytes": run.peak_rss_bytes,
        "output_sha256": run.output_sha256,
    }
    if run.timed_out:
        raise TimeoutError("prefix parser deadline exhausted")
    if run.exit_status != 0:
        try:
            failure = json.loads(run.output)
        except ValueError:
            failure = None
        if (
            isinstance(failure, dict)
            and set(failure) == {"schema_version", "status", "diagnostic"}
            and failure["schema_version"] == "agdaprover.corpus-prefix.v1"
            and failure["status"] == "prefix-rejected"
            and isinstance(failure["diagnostic"], str)
            and len(failure["diagnostic"]) <= 4096
            and "\x00" not in failure["diagnostic"]
        ):
            reason = failure["diagnostic"].replace(
                str(source_file), "<project>/" + source_file.name
            )
            return {
                **evidence,
                "status": "resource-exhausted"
                if reason.endswith("-limit")
                else "rejected",
                "reason": reason,
            }
        raise OSError("prefix parser failed without a valid protocol result")
    try:
        native = json.loads(run.output)
    except ValueError as error:
        raise OSError("invalid-prefix-parser-output") from error
    if (
        not isinstance(native, dict)
        or set(native)
        != {
            "schema_version",
            "parser_version",
            "source_characters",
            "position",
            "prefix_end",
            "parse_warning_count",
            "omission_candidates",
        }
        or native["schema_version"] != SCHEMA
        or native["parser_version"] != "2.8.0"
        or type(native["source_characters"]) is not int
        or native["source_characters"] != len(source)
        or type(native["position"]) is not int
        or native["position"] != position
        or type(native["prefix_end"]) is not int
        or not position < native["prefix_end"] <= len(source)
        or type(native["parse_warning_count"]) is not int
        or native["parse_warning_count"] != 0
    ):
        raise OSError("invalid-prefix-parser-output")
    omissions = native["omission_candidates"]
    if not isinstance(omissions, list) or len(omissions) > 4096:
        raise OSError("invalid-prefix-omission-candidates")
    previous_end = 0
    for row in omissions:
        if (
            not isinstance(row, dict)
            or set(row) != {"name", "start", "end"}
            or not isinstance(row["name"], str)
            or not row["name"]
            or any(c.isspace() or c == "\x00" for c in row["name"])
            or type(row["start"]) is not int
            or type(row["end"]) is not int
            or not previous_end <= row["start"] < row["end"] < position
        ):
            raise OSError("invalid-prefix-omission-candidates")
        previous_end = row["end"]
    return {**evidence, "status": "parsed", "boundary": native}


def independent_prefix(
    source: str,
    parsed: dict[str, Any],
    edit_start: int,
    remaining_ranges: tuple[tuple[int, int], ...],
    *,
    allow_omissions: bool = True,
    deadline: float = float("inf"),
) -> tuple[str, list[dict[str, Any]]]:
    """Conservatively weaken away unused ordinary declarations with old holes.

    Names are checked as substrings, including every mixfix component. This
    deliberately over-rejects rather than resolving/shadowing a different name.
    Native grouping excludes instances, macros, where bodies and mutual groups.
    Agda must still strictly check the resulting source; this never accepts it.
    """
    prefix = source[: parsed["boundary"]["prefix_end"]] + "\n"
    if not allow_omissions or any(word in source for word in ("macro", "unquote")):
        return prefix, []
    omitted = []
    for row in reversed(parsed["boundary"]["omission_candidates"]):
        if time.monotonic() >= deadline:
            raise TimeoutError("prefix independence check deadline exhausted")
        start, end = row["start"], row["end"]
        if end > edit_start or not any(
            start <= lo - 1 and hi - 1 <= end for lo, hi in remaining_ranges
        ):
            continue
        name_parts = [part for part in row["name"].split("_") if part]
        outside = prefix[:start] + prefix[end:]
        if not name_parts or any(part in outside for part in name_parts):
            continue
        prefix = (
            prefix[:start]
            + "".join(c if c.isspace() else " " for c in prefix[start:end])
            + prefix[end:]
        )
        omitted.append(row)
    return prefix, list(reversed(omitted))
