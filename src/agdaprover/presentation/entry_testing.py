"""Pure, declaration-owned virtual hole placement; never writes source files."""

from __future__ import annotations

from ..project.entries import SourceEntry
from ..project.sources import mask_literate_markdown


def virtual_entry(
    source: str, entry: SourceEntry, *, literate: bool = False
) -> tuple[str, int]:
    if entry.reason:
        raise ValueError(entry.reason)
    replacement = entry.name + " = {!!}"
    candidate = source
    code = mask_literate_markdown(source) if literate else source
    for index in range(len(entry.parts) - 1, -1, -1):
        start, end = entry.parts[index]
        # Keep physical line boundaries (including literate fences/prose), but
        # remove all clauses and anonymous where bodies owned by this entry.
        blank = "".join(
            c if c in "\r\n" or c != code[offset] else " "
            for offset, c in enumerate(source[start:end], start)
        )
        text = replacement + blank if index == 0 else blank
        candidate = candidate[:start] + text + candidate[end:]
    return candidate, entry.start + replacement.index("{!!}") + 1
