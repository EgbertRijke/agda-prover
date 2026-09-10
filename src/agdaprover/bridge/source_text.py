"""Small position-preserving lexer shared by resolution and source policy."""

from __future__ import annotations

import re
from collections.abc import Iterator
from pathlib import Path

from ..source_files import agda_source_suffix

_MARKDOWN_AGDA_BEGIN = re.compile(r"^.*[ \t]*```(?:agda)?[ \t]*(?:\r?\n)?$")
_MARKDOWN_OTHER_BEGIN = re.compile(r"^[ \t]*```[A-Za-z0-9-]+[ \t]*(?:\r?\n)?$")
_MARKDOWN_END = re.compile(r"^[ \t]*```[ \t]*(?:\r?\n)?$")

# One observational spelling/header boundary for project resolution and scope
# provenance. Parameters are not part of the module's qualified source name.
MODULE_NAME_COMPONENT = r"[^\W\d][\w'′₀-₉⁰-⁹-]*"
QUALIFIED_MODULE_NAME = rf"{MODULE_NAME_COMPONENT}(?:\.{MODULE_NAME_COMPONENT})*"
_MODULE_START = re.compile(
    rf"(?m)^(?P<indent>[ \t]*)module\s+"
    rf"(?P<name>_|{QUALIFIED_MODULE_NAME})(?=[\s({{⦃]|$)"
)


def module_headers(
    masked: str, *, header_limit: int | None = None
) -> Iterator[tuple[re.Match[str], int]]:
    """Yield balanced declaration headers, not module applications/aliases.

    The caller supplies position-preserving masked Agda. This is a lexical
    routing hint, not a replacement for Agda parsing or checking the telescope.
    An optional limit preserves the existing scope-view capacity contract.
    """
    for match in _MODULE_START.finditer(masked):
        boundary, kind = _module_header_boundary(masked, match.end(), header_limit)
        if kind == "where":
            yield match, boundary


def _module_header_boundary(
    masked: str, start: int, limit: int | None
) -> tuple[int, str]:
    stack: list[str] = []
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    index = start
    while index < len(masked) and (limit is None or index - start <= limit):
        character = masked[index]
        if character in pairs:
            stack.append(pairs[character])
        elif character in closing:
            if not stack or stack.pop() != character:
                return index, "malformed"
        elif not stack and character == "=":
            return index + 1, "alias"
        elif not stack and masked.startswith("where", index):
            before = masked[index - 1] if index else " "
            after = masked[index + 5] if index + 5 < len(masked) else " "
            if not (
                before.isalnum() or before in "_'" or after.isalnum() or after in "_'"
            ):
                return index + 5, "where"
        index += 1
    return min(index, len(masked)), "missing"


def _bleach(text: str) -> str:
    """Replace non-whitespace characters without changing source positions."""

    return "".join(
        character if character.isspace() and character != "\t" else " "
        for character in text
    )


def _physical_lines(source: str) -> list[str]:
    """Split only at LF, matching Agda's literate Markdown lexer."""

    return re.findall(r"[^\n]*\n|[^\n]+$", source)


def mask_literate_markdown(source: str) -> str:
    """Mask Markdown outside Agda code fences while preserving all positions.

    Agda 2.8 treats both unlabelled triple-backtick blocks and blocks labelled
    ``agda`` as code. Other fenced languages are prose. Delimiter lines are
    markup in either case and are therefore masked as well.
    """

    output: list[str] = []
    state = "prose"
    for line in _physical_lines(source):
        if state == "agda":
            if _MARKDOWN_END.fullmatch(line):
                output.append(_bleach(line))
                state = "prose"
            else:
                output.append(line)
        elif state == "other":
            output.append(_bleach(line))
            if _MARKDOWN_END.fullmatch(line):
                state = "prose"
        elif _MARKDOWN_AGDA_BEGIN.fullmatch(line):
            output.append(_bleach(line))
            state = "agda"
        elif _MARKDOWN_OTHER_BEGIN.fullmatch(line):
            output.append(_bleach(line))
            state = "other"
        else:
            output.append(_bleach(line))
    return "".join(output)


def mask_comments_and_strings(source: str) -> str:
    """Mask comments/strings while retaining newlines, offsets, and pragmas.

    Agda pragmas deliberately remain visible because they alter elaboration and
    trust. Nested block comments, line comments, and string contents cannot
    create false module, import, option, declaration, or policy matches.
    """

    output = list(source)
    index = 0
    block_depth = 0
    pragma = False
    string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        if pragma:
            if source[index : index + 3] == "#-}":
                pragma = False
                index += 3
            else:
                index += 1
            continue
        if block_depth:
            if pair == "{-":
                output[index] = output[index + 1] = " "
                block_depth += 1
                index += 2
                continue
            if pair == "-}":
                output[index] = output[index + 1] = " "
                block_depth -= 1
                index += 2
                continue
            if source[index] != "\n":
                output[index] = " "
            index += 1
            continue
        if string:
            if source[index] != "\n":
                output[index] = " "
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                string = False
            index += 1
            continue
        if pair == "{-" and source[index : index + 3] == "{-#":
            pragma = True
            index += 3
            continue
        if pair == "{-":
            output[index] = output[index + 1] = " "
            block_depth = 1
            index += 2
            continue
        if pair == "--":
            while index < len(source) and source[index] != "\n":
                output[index] = " "
                index += 1
            continue
        if source[index] == '"':
            output[index] = " "
            string = True
        index += 1
    return "".join(output)


def mask_agda_source(source: str, source_file: str | Path) -> str:
    """Expose only executable Agda text, preserving physical source offsets."""

    visible = (
        mask_literate_markdown(source)
        if agda_source_suffix(source_file) == ".lagda.md"
        else source
    )
    return mask_comments_and_strings(visible)


__all__ = [
    "MODULE_NAME_COMPONENT",
    "QUALIFIED_MODULE_NAME",
    "mask_agda_source",
    "mask_comments_and_strings",
    "mask_literate_markdown",
    "module_headers",
]
