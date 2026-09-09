"""Stack-safe JSON for exact deep terms, with no mathematical nesting ceiling.

The caller owns its I/O/memory envelope. Traversal polls that envelope and
rejects cycles and non-JSON data; it never truncates an observation. Encoding
matches the standard library's selected formatting for stable persisted IDs.
"""

from __future__ import annotations

import json
import math
import re
from collections.abc import Iterator
from json.encoder import encode_basestring
from typing import Any

from .resource_budget import checkpoint

_WHITESPACE = re.compile(r"[ \t\n\r]*")
_DECODER = json.JSONDecoder()


def _scalar(value: object) -> str:
    # Reuse the stdlib's native string escaping and scalar representations
    # without allocating a new JSONEncoder for every leaf in a large type.
    if isinstance(value, str):
        return encode_basestring(value)
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, int):
        return int.__repr__(value)
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("non-finite JSON number")
        return float.__repr__(value)
    raise TypeError(f"Object of type {type(value).__name__} is not JSON serializable")


def loads(payload: str | bytes) -> Any:
    text = payload.decode("utf-8") if isinstance(payload, bytes) else payload
    # Each frame holds a container, its next grammar state, and a pending key.
    stack: list[list[Any]] = []
    root: Any = None
    have_root = False
    position = 0

    def fail(message: str) -> None:
        raise json.JSONDecodeError(message, text, position)

    def accept(value: Any) -> None:
        nonlocal root, have_root
        if not stack:
            if have_root:
                fail("extra JSON value")
            root, have_root = value, True
        else:
            frame = stack[-1]
            if frame[1] in {"list-first", "list-value"}:
                frame[0].append(value)
            elif frame[1] == "object-value":
                frame[0][frame[2]] = value
            else:
                fail("unexpected JSON value")
            frame[1] = (
                "list-separator" if isinstance(frame[0], list) else "object-separator"
            )

    steps = 0
    while True:
        steps += 1
        if steps % 256 == 1:
            checkpoint()
        whitespace = _WHITESPACE.match(text, position)
        assert whitespace is not None
        position = whitespace.end()
        if position == len(text):
            if stack or not have_root:
                fail("incomplete JSON value")
            return root
        character = text[position]
        if stack:
            frame = stack[-1]
            state = frame[1]
            closing = "]" if isinstance(frame[0], list) else "}"
            if character == closing and state in {
                "list-first",
                "list-separator",
                "object-first",
                "object-separator",
            }:
                stack.pop()
                position += 1
                continue
            if state in {"list-separator", "object-separator"}:
                if character != ",":
                    fail("expected comma or closing delimiter")
                frame[1] = "list-value" if closing == "]" else "object-key"
                position += 1
                continue
            if state in {"object-first", "object-key"}:
                if character != '"':
                    fail("expected object key")
                key, position = _DECODER.raw_decode(text, position)
                if key in frame[0]:
                    fail("duplicate object key")
                frame[2], frame[1] = key, "object-colon"
                continue
            if state == "object-colon":
                if character != ":":
                    fail("expected colon")
                frame[1] = "object-value"
                position += 1
                continue
        elif have_root:
            fail("extra data")
        if character in "[{":
            container: Any = [] if character == "[" else {}
            accept(container)
            stack.append(
                [container, "list-first" if character == "[" else "object-first", None]
            )
            position += 1
        elif character in "]},:":
            fail("unexpected delimiter")
        else:
            # Only scalar tokens reach the native scanner; it never recurses.
            value, position = _DECODER.raw_decode(text, position)
            if isinstance(value, float) and not (-float("inf") < value < float("inf")):
                fail("non-finite JSON number")
            accept(value)


def iterencode(
    value: object,
    *,
    indent: int | None = None,
    sort_keys: bool = True,
    compact: bool = False,
) -> Iterator[str]:
    active: set[int] = set()
    # Iterators keep wide containers incremental, rather than duplicating all
    # pending children on the traversal stack.
    work: list[tuple[Any, ...]] = [("value", value, 0)]
    key_separator = ":" if compact else ": "
    item_separator = "," if compact or indent is not None else ", "
    steps = 0
    while work:
        steps += 1
        if steps % 256 == 1:
            checkpoint()
        operation, *arguments = work.pop()
        if operation == "text":
            yield arguments[0]
        elif operation == "items":
            iterator, identity, depth, mapping, first = arguments
            try:
                item = next(iterator)
            except StopIteration:
                active.remove(identity)
                if indent is not None and not first:
                    yield "\n" + " " * (indent * depth)
                yield "}" if mapping else "]"
                continue
            if not first:
                yield item_separator
            if indent is not None:
                yield "\n" + " " * (indent * (depth + 1))
            work.append(("items", iterator, identity, depth, mapping, False))
            if mapping:
                key, child = item
                if not isinstance(key, str):
                    raise ValueError("JSON object keys must be strings")
                yield encode_basestring(key) + key_separator
            else:
                child = item
            work.append(("value", child, depth + 1))
        else:
            item, depth = arguments
            if isinstance(item, (dict, list, tuple)):
                identity = id(item)
                if identity in active:
                    raise ValueError("cyclic JSON value")
                active.add(identity)
                mapping = isinstance(item, dict)
                children = (
                    (sorted(item.items()) if sort_keys else item.items())
                    if isinstance(item, dict)
                    else item
                )
                yield "{" if mapping else "["
                work.append(("items", iter(children), identity, depth, mapping, True))
            else:
                yield _scalar(item)


def dumps(
    value: object,
    *,
    indent: int | None = None,
    sort_keys: bool = True,
    compact: bool = False,
) -> str:
    return "".join(
        iterencode(value, indent=indent, sort_keys=sort_keys, compact=compact)
    )


def iterbytes(
    value: object, *, indent: int | None = None, compact: bool = False
) -> Iterator[bytes]:
    """Batch exact UTF-8 output for hashing/storage without a whole-wire copy."""
    pending: list[str] = []
    size = 0
    # At most four UTF-8 bytes per code point, hence chunks stay <= 64 KiB.
    # Join before encoding instead of allocating bytes/memoryviews per token.
    batch = 16384  # I/O granularity, not an accepted-value size limit.
    for part in iterencode(value, indent=indent, compact=compact):
        offset = 0
        while offset < len(part):
            end = min(len(part), offset + batch - size)
            pending.append(part[offset:end])
            size += end - offset
            offset = end
            if size == batch:
                checkpoint()
                yield "".join(pending).encode("utf-8")
                pending.clear()
                size = 0
    if pending:
        yield "".join(pending).encode("utf-8")
