"""Agda-owned declaration boundaries for non-mutating entry tests."""

from __future__ import annotations

import json
from pathlib import Path

from ..project.entries import SourceEntry
from .contracts import BridgeBudget
from .resources import CancellationToken
from .source_prefix import MAX_SOURCE_BYTES, parser_executable
from .validator import _run_checker


def decode_entries(value: object, source: str) -> tuple[SourceEntry, ...]:
    if (
        not isinstance(value, dict)
        or set(value)
        != {
            "schema_version",
            "parser_version",
            "source_characters",
            "parse_warning_count",
            "entries",
        }
        or value["schema_version"] != "agdaprover.source-entries.v1"
        or value["parser_version"] != "2.8.0"
        or type(value["source_characters"]) is not int
        or value["source_characters"] != len(source)
        or type(value["parse_warning_count"]) is not int
        or value["parse_warning_count"] != 0
        or not isinstance(value["entries"], list)
    ):
        raise ValueError(
            "Invalid source-entry parser response; update the source parser"
        )
    entries = []
    intervals = []
    for row in value["entries"]:
        if (
            not isinstance(row, dict)
            or set(row) != {"name", "parts", "reason"}
            or not isinstance(row["name"], str)
            or not row["name"]
            or any(c.isspace() or c == "\x00" for c in row["name"])
            or not isinstance(row["reason"], str)
            or not isinstance(row["parts"], list)
            or not row["parts"]
        ):
            raise ValueError("Invalid source-entry declaration")
        parts: list[tuple[int, int]] = []
        for part in row["parts"]:
            if (
                not isinstance(part, list)
                or len(part) != 2
                or any(type(x) is not int for x in part)
                or not 0 <= part[0] < part[1] <= len(source)
                or (parts and part[0] < parts[-1][1])
            ):
                raise ValueError("Invalid source-entry clause range")
            parts.append((part[0], part[1]))
        entries.append(SourceEntry(row["name"], tuple(parts), row["reason"]))
        intervals.extend(parts)
    intervals.sort()
    if any(a[1] > b[0] for a, b in zip(intervals, intervals[1:], strict=False)):
        raise ValueError("Overlapping source-entry declarations")
    return tuple(sorted(entries, key=lambda entry: entry.start))


def inspect_entries(
    source_file: Path, source: str, budget: BridgeBudget
) -> tuple[SourceEntry, ...]:
    executable = parser_executable()
    if executable is None:
        raise ValueError(
            "Entry testing requires the source parser; run scripts/build-source-parser"
        )
    raw = source.encode("utf-8")
    if len(raw) > MAX_SOURCE_BYTES:
        raise ValueError("Source exceeds the source parser's size allowance")
    if source_file.read_bytes() != raw:
        raise ValueError("Source changed before entry inspection")
    run = _run_checker(
        (str(executable), "--entries", str(source_file)),
        overlay=source_file.parent,
        budget=budget,
        cancellation=CancellationToken(),
        validation_process=False,
    )
    if source_file.read_bytes() != raw:
        raise ValueError("Source changed during entry inspection")
    if run.timed_out:
        raise TimeoutError("Source-entry inspection exhausted its time allowance")
    if run.exit_status != 0:
        raise ValueError("Source-entry inspection failed: " + run.output[:4096])
    return decode_entries(json.loads(run.output), source)
