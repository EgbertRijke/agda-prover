"""Small position-preserving lexer shared by resolution and source policy."""

from __future__ import annotations

import re
from pathlib import Path

from ..source_files import agda_source_suffix

_MARKDOWN_AGDA_BEGIN = re.compile(r"^.*[ \t]*```(?:agda)?[ \t]*(?:\r?\n)?$")
_MARKDOWN_OTHER_BEGIN = re.compile(r"^[ \t]*```[A-Za-z0-9-]+[ \t]*(?:\r?\n)?$")
_MARKDOWN_END = re.compile(r"^[ \t]*```[ \t]*(?:\r?\n)?$")


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
    "mask_agda_source",
    "mask_comments_and_strings",
    "mask_literate_markdown",
]
