"""Linear, shared structural scans over the small P0 Agda type fragment."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

_OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
_CLOSERS = set(_OPEN_TO_CLOSE.values())


@dataclass(frozen=True)
class NamedBinder:
    """A named Agda telescope group such as ``(x y : A)``."""

    names: tuple[str, ...]
    domain: str
    visibility: Literal["explicit", "implicit", "instance"]


def normalize_type_text(text: str) -> str:
    return " ".join(text.split())


def _scan(text: str, token: str) -> tuple[list[int], dict[int, int]]:
    stack: list[tuple[str, int]] = []
    positions: list[int] = []
    matches: dict[int, int] = {}
    for index, character in enumerate(text):
        if character in _OPEN_TO_CLOSE:
            stack.append((_OPEN_TO_CLOSE[character], index))
        elif character in _CLOSERS:
            if not stack or stack[-1][0] != character:
                raise ValueError("unbalanced type delimiters")
            _closer, opening = stack.pop()
            matches[opening] = index
        elif character == token and not stack:
            positions.append(index)
    if stack:
        raise ValueError("unbalanced type delimiters")
    return positions, matches


def strip_outer_delimiters(text: str) -> str:
    """Remove enclosing bracket pairs after one delimiter-validation scan."""

    stripped = text.strip()
    if not stripped:
        return stripped
    _positions, matches = _scan(stripped, "\0")
    start = 0
    end = len(stripped)
    while start < end and stripped[start] in _OPEN_TO_CLOSE:
        if matches.get(start) != end - 1:
            break
        start += 1
        end -= 1
        while start < end and stripped[start].isspace():
            start += 1
        while end > start and stripped[end - 1].isspace():
            end -= 1
    return stripped[start:end]


def split_top_level_arrows(text: str) -> tuple[str, ...]:
    """Split a type at top-level arrows in one pass, rejecting malformed text."""

    stripped = strip_outer_delimiters(text)
    if not stripped:
        raise ValueError("empty type")
    positions, _matches = _scan(stripped, "→")
    if not positions:
        return (stripped,)
    parts: list[str] = []
    start = 0
    for position in positions:
        part = stripped[start:position].strip()
        if not part:
            raise ValueError("malformed function type")
        parts.append(part)
        start = position + 1
    tail = stripped[start:].strip()
    if not tail:
        raise ValueError("malformed function type")
    parts.append(tail)
    return tuple(parts)


def binder_domain(text: str) -> str:
    """Return ``A`` for a named binder ``(x : A)`` and TEXT otherwise."""

    stripped = text.strip()
    binder = parse_named_binder(stripped)
    return binder.domain if binder is not None else strip_outer_delimiters(stripped)


def binder_domains(text: str) -> tuple[str, ...]:
    """Expand ``(x y : A)`` to two copies of ``A``.

    Agda displays consecutive binders as one arrow-domain group.  Treating the
    group as one binder produces under-applied proof terms, so focused search
    must retain its multiplicity even though this prototype keeps dependency
    names opaque.
    """

    stripped = text.strip()
    adjacent = split_adjacent_binders(stripped)
    if adjacent is not None and len(adjacent) > 1:
        return tuple(domain for group in adjacent for domain in binder_domains(group))
    binder = parse_named_binder(stripped)
    if binder is None:
        return (strip_outer_delimiters(stripped),)
    return (binder.domain,) * len(binder.names)


def parse_named_binder(text: str) -> NamedBinder | None:
    """Parse one displayed named-binder group without interpreting its type.

    The parser deliberately preserves the domain as Agda text.  It supports
    explicit, implicit, double-braced instance, and unicode instance binders;
    elaboration and scope remain the kernel's responsibility.
    """

    stripped = text.strip()
    _positions, matches = _scan(stripped, "\0")
    if stripped and stripped[0] in _OPEN_TO_CLOSE:
        if matches.get(0) != len(stripped) - 1:
            return None
    visibility: Literal["explicit", "implicit", "instance"]
    if stripped.startswith("{{") and stripped.endswith("}}"):
        inner = stripped[2:-2].strip()
        visibility = "instance"
    elif stripped.startswith("⦃") and stripped.endswith("⦄"):
        inner = stripped[1:-1].strip()
        visibility = "instance"
    elif stripped.startswith("(") and stripped.endswith(")"):
        inner = stripped[1:-1].strip()
        visibility = "explicit"
    elif stripped.startswith("{") and stripped.endswith("}"):
        inner = stripped[1:-1].strip()
        visibility = "implicit"
    else:
        return None
    colons, _matches = _scan(inner, ":")
    if not colons:
        return None
    names = tuple(inner[: colons[0]].split())
    domain = inner[colons[0] + 1 :].strip()
    if not names or not domain or any(not name for name in names):
        raise ValueError("malformed named binder")
    return NamedBinder(names, domain, visibility)


def split_adjacent_binders(text: str) -> tuple[str, ...] | None:
    """Split Agda's ``(x : A) (y : B x)`` telescope display.

    Agda pretty-prints consecutive named binders without an arrow between
    groups. Return ``None`` when the input is not entirely a sequence of
    balanced binder groups, so callers can retain it as one anonymous domain.
    """

    stripped = text.strip()
    if not stripped:
        return None
    _positions, matches = _scan(stripped, "\0")
    groups: list[str] = []
    index = 0
    while index < len(stripped):
        while index < len(stripped) and stripped[index].isspace():
            index += 1
        if index == len(stripped):
            break
        if stripped[index] not in _OPEN_TO_CLOSE:
            return None
        end = matches.get(index)
        if end is None:
            return None
        groups.append(stripped[index : end + 1])
        index = end + 1
    return tuple(groups) if groups else None


def top_level_arrow_count(text: str) -> int:
    if not text.strip():
        return 0
    return len(split_top_level_arrows(text)) - 1


def split_top_level_application(text: str) -> tuple[str, ...]:
    """Split a surface application at whitespace outside delimiters."""

    stripped = strip_outer_delimiters(text)
    if not stripped:
        raise ValueError("empty application")
    stack: list[str] = []
    parts: list[str] = []
    start = 0
    for index, character in enumerate(stripped):
        if character in _OPEN_TO_CLOSE:
            stack.append(_OPEN_TO_CLOSE[character])
        elif character in _CLOSERS:
            if not stack or stack[-1] != character:
                raise ValueError("unbalanced application delimiters")
            stack.pop()
        elif character.isspace() and not stack:
            part = stripped[start:index].strip()
            if part:
                parts.append(part)
            start = index + 1
    if stack:
        raise ValueError("unbalanced application delimiters")
    tail = stripped[start:].strip()
    if tail:
        parts.append(tail)
    return tuple(parts)


def result_head(text: str) -> str:
    if not text.strip():
        return "unknown"
    parts = split_top_level_arrows(text)
    tail = strip_outer_delimiters(parts[-1]).strip()
    return tail.split()[0] if tail else "unknown"
