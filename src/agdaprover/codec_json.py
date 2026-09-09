"""Stack-safe JSON for exact deep terms, with no mathematical nesting ceiling.

The caller owns its I/O/memory envelope. Traversal polls that envelope and
rejects cycles and non-JSON data; it never truncates an observation. Encoding
matches the standard library's selected formatting for stable persisted IDs.
"""

from __future__ import annotations

import codecs
import json
import math
import re
from collections.abc import Iterable, Iterator
from json.encoder import encode_basestring
from typing import Any, NoReturn

from .resource_budget import checkpoint

_WHITESPACE = re.compile(r"[ \t\n\r]*")
_DECODER = json.JSONDecoder()
_STRING_SPECIAL = re.compile(r'["\\]')
_SCALAR_END = re.compile(r"[ \t\n\r\[\]{},:]")


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


class _JsonInput:
    """One chunk plus a spanning scalar; never retain the consumed prefix."""

    def __init__(self, chunks: Iterable[str], *, origin: str | None = None) -> None:
        self.chunks = iter(chunks)
        self.origin = origin
        self.text = ""
        self.position = 0
        self.offset = 0
        self.finished = False

    def refill(self) -> bool:
        if self.position < len(self.text):
            return True
        if self.finished:
            return False
        self.offset += len(self.text)
        self.text, self.position = "", 0
        for chunk in self.chunks:
            checkpoint()
            if chunk:
                self.text = chunk
                return True
        self.finished = True
        return False

    def skip_space(self) -> str:
        while True:
            if self.position < len(self.text):
                character = self.text[self.position]
                if character not in " \t\n\r":
                    return character
            whitespace = _WHITESPACE.match(self.text, self.position)
            assert whitespace is not None
            self.position = whitespace.end()
            if self.position < len(self.text):
                return self.text[self.position]
            if not self.refill():
                return ""

    def fail(self, message: str, position: int | None = None) -> NoReturn:
        absolute = self.offset + self.position if position is None else position
        if self.origin is not None:
            raise json.JSONDecodeError(message, self.origin, absolute)
        raise ValueError(f"{message} at source character {absolute}")

    def scalar(self) -> Any:
        if self.origin is not None:
            value, self.position = _DECODER.raw_decode(self.text, self.position)
            return value
        start = self.offset + self.position
        parts: list[str] = []
        if self.text[self.position] == '"':
            begin = self.position
            self.position += 1
            escaped = False
            while True:
                if escaped and self.position < len(self.text):
                    self.position += 1
                    escaped = False
                match = _STRING_SPECIAL.search(self.text, self.position)
                if match is None:
                    parts.append(self.text[begin:])
                    self.position = len(self.text)
                    if not self.refill():
                        self.fail("unterminated JSON string", start)
                    begin = 0
                    continue
                self.position = match.end()
                if match[0] == '"':
                    parts.append(self.text[begin : self.position])
                    break
                escaped = True
        else:
            while True:
                match = _SCALAR_END.search(self.text, self.position)
                end = len(self.text) if match is None else match.start()
                parts.append(self.text[self.position : end])
                self.position = end
                if match is not None or not self.refill():
                    break
        token = "".join(parts)
        try:
            value, end = _DECODER.raw_decode(token)
        except json.JSONDecodeError as error:
            self.fail(error.msg, start + error.pos)
        if end != len(token):
            self.fail("invalid JSON scalar", start + end)
        return value


def loads(payload: str | bytes) -> Any:
    if not isinstance(payload, str | bytes):
        raise TypeError("JSON input must be str or bytes")
    text = payload.decode("utf-8") if isinstance(payload, bytes) else payload
    return _parse(_JsonInput((text,), origin=text))


def load_chunks(chunks: Iterable[bytes]) -> Any:
    """Decode exact UTF-8 chunks under the caller's resource/I/O ownership."""

    def decoded() -> Iterator[str]:
        decoder = codecs.getincrementaldecoder("utf-8")()
        for chunk in chunks:
            checkpoint()
            if not isinstance(chunk, bytes):
                raise TypeError("JSON input chunks must be bytes")
            text = decoder.decode(chunk)
            if text:
                yield text
        tail = decoder.decode(b"", final=True)
        if tail:
            yield tail

    return _parse(_JsonInput(decoded()))


def _parse(source: _JsonInput) -> Any:
    # Each frame holds a container, its next grammar state, and a pending key.
    stack: list[list[Any]] = []
    root: Any = None
    have_root = False
    fail = source.fail

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
        character = source.skip_space()
        if not character:
            if stack or not have_root:
                fail("incomplete JSON value")
            return root
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
                source.position += 1
                continue
            if state in {"list-separator", "object-separator"}:
                if character != ",":
                    fail("expected comma or closing delimiter")
                frame[1] = "list-value" if closing == "]" else "object-key"
                source.position += 1
                continue
            if state in {"object-first", "object-key"}:
                if character != '"':
                    fail("expected object key")
                key = source.scalar()
                if key in frame[0]:
                    fail("duplicate object key")
                frame[2], frame[1] = key, "object-colon"
                continue
            if state == "object-colon":
                if character != ":":
                    fail("expected colon")
                frame[1] = "object-value"
                source.position += 1
                continue
        elif have_root:
            fail("extra data")
        if character in "[{":
            container: Any = [] if character == "[" else {}
            accept(container)
            stack.append(
                [container, "list-first" if character == "[" else "object-first", None]
            )
            source.position += 1
        elif character in "]},:":
            fail("unexpected delimiter")
        else:
            # Only scalar tokens reach the native scanner; it never recurses.
            value = source.scalar()
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
