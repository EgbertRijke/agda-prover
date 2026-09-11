"""Linear, shared structural scans over the small P0 Agda type fragment."""

from __future__ import annotations

import re
import sys
from collections import OrderedDict
from collections.abc import Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from threading import get_ident
from typing import Literal

_OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
_CLOSERS = set(_OPEN_TO_CLOSE.values())

DEFAULT_UNIVERSE_NAMES = frozenset(
    prefix + name
    for prefix in ("", "Agda.Primitive.")
    for name in ("Set", "Setω", "Prop", "SSet", "Propω", "SSetω")
)


def is_universe_head(
    head: str, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> bool:
    """Recognize a sort spelling supplied by the kernel's local scope.

    Live scopes supply exact observed spellings, including level suffixes,
    so a shadowed suffixed name cannot inherit a primitive's identity.
    Legacy callers retain canonical built-in notation. A prefix match is not
    sufficient: SetLike is not a universe. This is not typing evidence.
    """
    return head in universe_names or (
        universe_names == DEFAULT_UNIVERSE_NAMES
        and head.rstrip("₀₁₂₃₄₅₆₇₈₉") in universe_names
    )


def has_universe_codomain(
    type_text: str, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> bool:
    return is_universe_head(result_head(type_text), universe_names)


def type_heads(type_text: str) -> frozenset[str]:
    """Collect possible sort names from a displayed telescope, without guessing.

    The kernel resolves these names; the scanner does not classify them.
    Bound variables and applications may therefore occur in the result.
    """
    pending = [type_text]
    heads: set[str] = set()
    while pending:
        text = pending.pop()
        try:
            parts = split_top_level_arrows(text)
            heads.add(result_head(parts[-1]))
            for part in parts[:-1]:
                for group in split_adjacent_binders(part) or (part,):
                    binder = parse_named_binder(group)
                    pending.append(binder.domain if binder is not None else group)
        except ValueError:
            continue
    return frozenset(
        head
        for head in heads
        if head and head != "_" and not any(c.isspace() or c in "(){}⦃⦄" for c in head)
    )


class _ScanBatch:
    """Short-lived lexical work reuse, never a type/proof/visibility cache."""

    def __init__(self, max_bytes: int) -> None:
        self.max_bytes = max_bytes
        self.retained_bytes = 0
        self.hits = 0
        self.misses = 0
        self.owner = get_ident()
        self.active = True
        self.entries: OrderedDict[
            tuple[str, str], tuple[tuple[int, ...], dict[int, int], int]
        ] = OrderedDict()

    def scan(self, text: str, token: str) -> tuple[list[int], dict[int, int]]:
        if not self.active or self.owner != get_ident():
            return _scan_uncached(text, token)
        key = (text, token)
        cached = self.entries.get(key)
        if cached is not None:
            self.hits += 1
            self.entries.move_to_end(key)
            cached_positions, cached_matches, _size = cached
            # No caller may mutate another call's lexical observation.
            return list(cached_positions), cached_matches.copy()
        self.misses += 1
        positions, matches = _scan_uncached(text, token)
        if not self.max_bytes:
            return positions, matches
        frozen_positions = tuple(positions)
        # Conservatively count retained Python objects, including repeated
        # references and per-entry mapping overhead. This bounds a best-effort
        # optimization; an oversized input still follows the ordinary scan.
        size = (
            256
            + sys.getsizeof(key)
            + sys.getsizeof(text)
            + sys.getsizeof(token)
            + sys.getsizeof(frozen_positions)
            + sum(map(sys.getsizeof, frozen_positions))
            + sys.getsizeof(matches)
            + sum(sys.getsizeof(k) + sys.getsizeof(v) for k, v in matches.items())
        )
        if size <= self.max_bytes:
            while self.entries and self.retained_bytes + size > self.max_bytes:
                _key, (_positions, _matches, removed) = self.entries.popitem(last=False)
                self.retained_bytes -= removed
            self.entries[key] = (frozen_positions, matches.copy(), size)
            self.retained_bytes += size
        return positions, matches


_scan_batch: ContextVar[_ScanBatch | None] = ContextVar(
    "type-syntax-batch", default=None
)


@contextmanager
def syntax_scan_batch(*, max_bytes: int = 2 * 1024**2) -> Iterator[_ScanBatch]:
    """Reuse exact delimiter scans within one synchronous admission batch.

    The byte reservation limits retained lexical results, not Agda expression
    size or search completeness. Eviction, disabled caching and failed scans
    all retain the uncached behavior. Nested batches restore their parent;
    returning, raising or cancellation clears this batch's retained strings.
    """
    if type(max_bytes) is not int or max_bytes < 0:
        raise ValueError("syntax scan cache reservation must be nonnegative")
    batch = _ScanBatch(max_bytes)
    previous = _scan_batch.set(batch)
    try:
        yield batch
    finally:
        batch.active = False
        batch.entries.clear()
        batch.retained_bytes = 0
        _scan_batch.reset(previous)


@dataclass(frozen=True)
class NamedBinder:
    """A named Agda telescope group such as ``(x y : A)``."""

    names: tuple[str, ...]
    domain: str
    visibility: Literal["explicit", "implicit", "instance"]


def telescope_introduction(
    type_text: str,
    occupied: frozenset[str],
    *,
    trailing_only: bool = False,
    implicit_only: bool = True,
) -> str | None:
    """Render a capture-free lambda proposal from a displayed telescope.

    Ordinary reasoning requests hidden-binder exposure only. An adapter can
    also request an explicit telescope when automatic introduction cannot
    print internal pattern binders. This is syntax, not a typing witness:
    callers must check the resulting expression with Agda.
    """
    try:
        groups = tuple(
            group
            for part in split_top_level_arrows(type_text)[:-1]
            for group in split_adjacent_binders(part) or (part,)
        )
        parsed = tuple(parse_named_binder(group) for group in groups)
    except ValueError:
        return None
    if not parsed:
        return None
    if trailing_only and (parsed[-1] is None or parsed[-1].visibility != "implicit"):
        return None
    if implicit_only and not any(
        binder is not None and binder.visibility == "implicit" for binder in parsed
    ):
        return None
    if any(
        binder is not None and (binder.visibility == "instance" or "=" in binder.names)
        for binder in parsed
    ):
        return None
    used = set(occupied) | set(re.findall(r"[^\s(){}⦃⦄:→]+", type_text))
    names: list[str] = []
    index = 0
    for binder in parsed:
        for label in binder.names if binder is not None else (None,):
            while (name := f"arg{index}") in used:
                index += 1
            used.add(name)
            if binder is not None and binder.visibility == "implicit":
                names.append(f"{{{label} = {name}}}")
            else:
                names.append(name)
    return "λ " + " ".join(names) + " → ?"


def normalize_type_text(text: str) -> str:
    return " ".join(text.split())


def _scan(text: str, token: str) -> tuple[list[int], dict[int, int]]:
    batch = _scan_batch.get()
    if batch is not None:
        return batch.scan(text, token)
    return _scan_uncached(text, token)


def _scan_uncached(text: str, token: str) -> tuple[list[int], dict[int, int]]:
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
