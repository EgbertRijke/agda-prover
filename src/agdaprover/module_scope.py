"""Bounded, datatype-neutral views of Agda module scopes.

The public Agda protocol remains the authority on name resolution.  This module
records enough position-preserving source structure to keep search identities,
premise provenance, and reconstruction from conflating distinct parameterized
module contexts.  Its parser is deliberately observational: a false or missing
surface hint can change ordering, never authorize a name or establish typing.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from .bridge.source_text import mask_agda_source, mask_comments_and_strings
from .type_syntax import parse_named_binder, split_adjacent_binders

MODULE_SCOPE_SCHEMA_VERSION = "agdaprover.module-scope.v1"
MAX_MODULE_FRAMES = 128
MAX_MODULE_PARAMETERS = 4096
MAX_MODULE_DIRECTIVES = 4096
MAX_MODULE_HEADER_BYTES = 1 << 20

_NAME_COMPONENT = r"[^\W\d][\w'′₀-₉⁰-⁹-]*"
_QUALIFIED_NAME = rf"{_NAME_COMPONENT}(?:\.{_NAME_COMPONENT})*"
_MODULE_START = re.compile(
    rf"(?m)^(?P<indent>[ \t]*)module[ \t]+"
    rf"(?P<name>_|{_QUALIFIED_NAME})(?=[ \t({{⦃]|$)"
)
_OPEN_LINE = re.compile(r"(?m)^(?P<indent>[ \t]*)open[ \t]+(?P<body>[^\n]+)$")
_ALIAS_LINE = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?P<open>open[ \t]+)?module[ \t]+"
    rf"(?P<alias>{_NAME_COMPONENT})[ \t]*=[ \t]*(?P<body>[^\n]+)$"
)
_PLAIN_QNAME = re.compile(_QUALIFIED_NAME)


def _bounded(text: str, label: str, limit: int = MAX_MODULE_HEADER_BYTES) -> str:
    if not isinstance(text, str) or len(text.encode()) > limit:
        raise ValueError(f"{label} must be bounded text")
    return text


def _stable_hash(value: object) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


@dataclass(frozen=True)
class ModuleParameter:
    names: tuple[str, ...]
    type_text: str
    hiding: Literal["explicit", "implicit", "instance"]
    rendered: str

    def __post_init__(self) -> None:
        if not self.names or any(not name or name.isspace() for name in self.names):
            raise ValueError("module parameters require nonempty names")
        _bounded(self.type_text, "module parameter type")
        _bounded(self.rendered, "rendered module parameter")
        if self.hiding not in {"explicit", "implicit", "instance"}:
            raise ValueError("invalid module parameter hiding")

    def to_dict(self) -> dict[str, object]:
        return {
            "names": list(self.names),
            "type": self.type_text,
            "hiding": self.hiding,
            "rendered": self.rendered,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ModuleParameter:
        if set(value) != {"names", "type", "hiding", "rendered"}:
            raise ValueError("malformed module parameter")
        names = value["names"]
        if not isinstance(names, list) or not all(
            isinstance(item, str) for item in names
        ):
            raise ValueError("module parameter names must be text")
        if not all(
            isinstance(value[field], str) for field in ("type", "hiding", "rendered")
        ):
            raise ValueError("module parameter fields must be text")
        return cls(
            tuple(names),
            value["type"],
            value["hiding"],
            value["rendered"],
        )


@dataclass(frozen=True)
class ModuleFrame:
    kind: Literal["root", "named", "anonymous"]
    name: str | None
    qualified_name: str | None
    parameters: tuple[ModuleParameter, ...]
    start: int
    header_end: int
    end: int
    indentation: int

    def __post_init__(self) -> None:
        if self.kind not in {"root", "named", "anonymous"}:
            raise ValueError("invalid module frame kind")
        if self.kind == "anonymous" and (self.name is not None or self.qualified_name):
            raise ValueError("anonymous module frame cannot have a name")
        if self.kind != "anonymous" and (not self.name or not self.qualified_name):
            raise ValueError("named module frame requires names")
        if not (0 <= self.start < self.header_end <= self.end):
            raise ValueError("module frame ranges must be ordered")
        if self.indentation < 0 or len(self.parameters) > MAX_MODULE_PARAMETERS:
            raise ValueError("module frame exceeds its structural bounds")

    def semantic_dict(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "name": self.name,
            "qualified_name": self.qualified_name,
            "parameters": [item.to_dict() for item in self.parameters],
            "source_range": [self.start, self.end],
            "header_end": self.header_end,
            "indentation": self.indentation,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ModuleFrame:
        if set(value) != {
            "kind",
            "name",
            "qualified_name",
            "parameters",
            "source_range",
            "header_end",
            "indentation",
        }:
            raise ValueError("malformed module frame")
        parameters = value["parameters"]
        source_range = value["source_range"]
        if (
            not isinstance(parameters, list)
            or not all(isinstance(item, dict) for item in parameters)
            or not isinstance(source_range, list)
            or len(source_range) != 2
        ):
            raise ValueError("malformed module frame collections")
        name = value["name"]
        qualified = value["qualified_name"]
        if name is not None and not isinstance(name, str):
            raise ValueError("module frame name must be text or null")
        if qualified is not None and not isinstance(qualified, str):
            raise ValueError("qualified module name must be text or null")
        if not isinstance(value["kind"], str):
            raise ValueError("module frame kind must be text")
        if not all(
            isinstance(item, int) and not isinstance(item, bool)
            for item in (*source_range, value["header_end"], value["indentation"])
        ):
            raise ValueError("module frame positions must be integers")
        return cls(
            value["kind"],  # type: ignore[arg-type]
            name,
            qualified,
            tuple(ModuleParameter.from_dict(item) for item in parameters),
            int(source_range[0]),
            int(value["header_end"]),
            int(source_range[1]),
            int(value["indentation"]),
        )


@dataclass(frozen=True)
class ModuleDirective:
    kind: Literal["open", "module-alias", "open-module-alias"]
    target: str
    rendered_arguments: str
    alias: str | None
    public: bool
    using: str | None
    hiding: str | None
    renaming: str | None
    source_range: tuple[int, int]

    def __post_init__(self) -> None:
        if self.kind not in {"open", "module-alias", "open-module-alias"}:
            raise ValueError("invalid module directive kind")
        if not _PLAIN_QNAME.fullmatch(self.target):
            raise ValueError("module directive target must be a qualified name")
        if self.alias is not None and not _PLAIN_QNAME.fullmatch(self.alias):
            raise ValueError("module alias must be a name")
        if not (0 <= self.source_range[0] < self.source_range[1]):
            raise ValueError("module directive range must be ordered")
        for label, value in (
            ("module arguments", self.rendered_arguments),
            ("using", self.using),
            ("hiding", self.hiding),
            ("renaming", self.renaming),
        ):
            if value is not None:
                _bounded(value, label)

    def to_dict(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "target": self.target,
            "rendered_arguments": self.rendered_arguments,
            "alias": self.alias,
            "public": self.public,
            "using": self.using,
            "hiding": self.hiding,
            "renaming": self.renaming,
            "source_range": list(self.source_range),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ModuleDirective:
        expected = {
            "kind",
            "target",
            "rendered_arguments",
            "alias",
            "public",
            "using",
            "hiding",
            "renaming",
            "source_range",
        }
        if set(value) != expected or not isinstance(value["source_range"], list):
            raise ValueError("malformed module directive")
        source_range = value["source_range"]
        if len(source_range) != 2:
            raise ValueError("module directive range must contain two positions")
        alias = value["alias"]
        if alias is not None and not isinstance(alias, str):
            raise ValueError("module directive alias must be text or null")
        if not isinstance(value["public"], bool):
            raise ValueError("module directive public flag must be boolean")
        for field in ("kind", "target", "rendered_arguments"):
            if not isinstance(value[field], str):
                raise ValueError(f"module directive {field} must be text")
        for field in ("using", "hiding", "renaming"):
            if value[field] is not None and not isinstance(value[field], str):
                raise ValueError(f"module directive {field} must be text or null")
        if not all(
            isinstance(item, int) and not isinstance(item, bool)
            for item in source_range
        ):
            raise ValueError("module directive positions must be integers")
        return cls(
            value["kind"],
            value["target"],
            value["rendered_arguments"],
            alias,
            value["public"],
            value["using"],
            value["hiding"],
            value["renaming"],
            (int(source_range[0]), int(source_range[1])),
        )


@dataclass(frozen=True)
class ModuleScope:
    source_sha256: str
    position: int
    frames: tuple[ModuleFrame, ...]
    directives: tuple[ModuleDirective, ...] = ()
    schema_version: str = MODULE_SCOPE_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != MODULE_SCOPE_SCHEMA_VERSION:
            raise ValueError("unsupported module-scope schema version")
        if not re.fullmatch(r"[0-9a-f]{64}", self.source_sha256):
            raise ValueError("module scope source identity must be SHA-256")
        if self.position < 0 or not self.frames or self.frames[0].kind != "root":
            raise ValueError("module scope requires a position and root frame")
        if (
            len(self.frames) > MAX_MODULE_FRAMES
            or len(self.directives) > MAX_MODULE_DIRECTIVES
        ):
            raise ValueError("module scope exceeds its structural bounds")
        if any(
            not (frame.start <= self.position <= frame.end) for frame in self.frames
        ):
            raise ValueError("module frame does not contain the focused position")
        if any(
            directive.source_range[1] > self.position for directive in self.directives
        ):
            raise ValueError("module directive follows the focused position")
        if any(
            not (
                self.frames[index - 1].start <= frame.start
                and frame.end <= self.frames[index - 1].end
            )
            for index, frame in enumerate(self.frames[1:], 1)
        ):
            raise ValueError("module frames are not properly nested")

    @property
    def scope_id(self) -> str:
        # Raw cursor position is intentionally excluded: goals in the same
        # lexical environment share a scope identity. Directives are filtered
        # at the focused position, so crossing an `open` or alias still changes
        # the identity.
        return _stable_hash(
            {
                "schema_version": self.schema_version,
                "source_sha256": self.source_sha256,
                "frames": [frame.semantic_dict() for frame in self.frames],
                "directives": [directive.to_dict() for directive in self.directives],
            }
        )

    @property
    def parameters(self) -> tuple[ModuleParameter, ...]:
        return tuple(
            parameter for frame in self.frames for parameter in frame.parameters
        )

    def semantic_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "source_sha256": self.source_sha256,
            "position": self.position,
            "frames": [frame.semantic_dict() for frame in self.frames],
            "directives": [directive.to_dict() for directive in self.directives],
        }

    def to_dict(self) -> dict[str, object]:
        result = self.semantic_dict()
        result["scope_id"] = self.scope_id
        return result

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ModuleScope:
        expected = {
            "schema_version",
            "source_sha256",
            "position",
            "frames",
            "directives",
            "scope_id",
        }
        if set(value) != expected:
            raise ValueError("malformed module scope")
        frames = value["frames"]
        directives = value["directives"]
        if (
            not isinstance(frames, list)
            or not all(isinstance(item, dict) for item in frames)
            or not isinstance(directives, list)
            or not all(isinstance(item, dict) for item in directives)
        ):
            raise ValueError("module scope frames and directives must be lists")
        if not isinstance(value["source_sha256"], str):
            raise ValueError("module scope source identity must be text")
        if not isinstance(value["schema_version"], str):
            raise ValueError("module scope schema version must be text")
        if not isinstance(value["position"], int) or isinstance(
            value["position"], bool
        ):
            raise ValueError("module scope position must be an integer")
        result = cls(
            source_sha256=value["source_sha256"],
            position=value["position"],
            frames=tuple(ModuleFrame.from_dict(item) for item in frames),
            directives=tuple(ModuleDirective.from_dict(item) for item in directives),
            schema_version=value["schema_version"],
        )
        if value["scope_id"] != result.scope_id:
            raise ValueError("module-scope identity mismatch")
        return result


def analyze_module_scope(
    source: str,
    position: int,
    source_file: str | Path | None = None,
) -> ModuleScope:
    """Return the lexical module scope containing a zero-based position."""

    if not isinstance(source, str) or len(source.encode()) > 64 * 1024 * 1024:
        raise ValueError("module source must be bounded text")
    if not 0 <= position <= len(source):
        raise ValueError("module-scope position is outside the source")
    masked = (
        mask_agda_source(source, source_file)
        if source_file is not None
        else mask_comments_and_strings(source)
    )
    headers = _module_frames(source, masked)
    containing = [frame for frame in headers if frame.start <= position <= frame.end]
    containing.sort(key=lambda frame: (frame.start, -frame.end))
    if not containing:
        raise ValueError("source contains no enclosing Agda module")
    frames: list[ModuleFrame] = []
    for frame in containing:
        if not frames or (
            frames[-1].start <= frame.start and frame.end <= frames[-1].end
        ):
            frames.append(frame)
    if not frames or frames[0].kind != "root":
        raise ValueError("source has no enclosing root module")
    directives: list[ModuleDirective] = []
    for directive in _module_directives(source, masked):
        owners = [
            frame
            for frame in headers
            if frame.header_end <= directive.source_range[0] <= frame.end
        ]
        owner = (
            min(owners, key=lambda frame: frame.end - frame.start) if owners else None
        )
        if directive.source_range[1] <= position and owner in frames:
            directives.append(directive)
    return ModuleScope(
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        position=position,
        frames=tuple(frames),
        directives=tuple(directives),
    )


def attach_module_scope(
    goal: Any,
    source: str,
    source_file: str | Path | None = None,
) -> Any:
    """Return a GoalInfo-like dataclass with its optional module scope attached."""

    from dataclasses import replace

    start = int(goal.source_range[0])
    position = min(max(start - 1, 0), len(source))
    return replace(
        goal,
        module_scope=analyze_module_scope(source, position, source_file),
    )


def _module_frames(source: str, masked: str) -> tuple[ModuleFrame, ...]:
    raw: list[tuple[re.Match[str], int, int, str]] = []
    for match in _MODULE_START.finditer(masked):
        boundary, boundary_kind = _module_header_boundary(masked, match.end())
        if boundary_kind != "where":
            continue
        header_end = boundary
        raw.append((match, header_end, len(match.group("indent")), match.group("name")))
        if len(raw) > MAX_MODULE_FRAMES:
            raise ValueError("module source exceeds the frame limit")
    if not raw:
        return ()
    frames: list[ModuleFrame] = []
    for index, (match, header_end, indentation, raw_name) in enumerate(raw):
        is_root = index == 0 and indentation == 0 and raw_name != "_"
        end = len(source) if is_root else _layout_end(masked, header_end, indentation)
        telescope = source[match.end() : header_end - len("where")]
        parameters = _module_parameters(telescope)
        if is_root:
            frame_kind: Literal["root", "named", "anonymous"] = "root"
            name: str | None = raw_name
            qualified = raw_name
        elif raw_name == "_":
            frame_kind = "anonymous"
            name = None
            qualified = None
        else:
            frame_kind = "named"
            name = raw_name.rsplit(".", 1)[-1]
            qualified = raw_name
        frames.append(
            ModuleFrame(
                frame_kind,
                name,
                qualified,
                parameters,
                match.start(),
                header_end,
                end,
                indentation,
            )
        )
    return tuple(frames)


def _module_header_boundary(masked: str, start: int) -> tuple[int, str]:
    stack: list[str] = []
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    index = start
    while index < len(masked) and index - start <= MAX_MODULE_HEADER_BYTES:
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


def _layout_end(masked: str, header_end: int, indentation: int) -> int:
    line_end = masked.find("\n", header_end)
    cursor = len(masked) if line_end < 0 else line_end + 1
    while cursor < len(masked):
        next_end = masked.find("\n", cursor)
        next_end = len(masked) if next_end < 0 else next_end + 1
        line = masked[cursor:next_end]
        content = line.lstrip(" \t\r\n")
        if content:
            current_indent = len(line) - len(line.lstrip(" \t"))
            if current_indent <= indentation:
                return cursor
        cursor = next_end
    return len(masked)


def _module_parameters(telescope: str) -> tuple[ModuleParameter, ...]:
    groups = split_adjacent_binders(telescope)
    if groups is None:
        if telescope.strip():
            raise ValueError("unsupported module telescope surface syntax")
        return ()
    parameters: list[ModuleParameter] = []
    for group in groups:
        parsed = parse_named_binder(group)
        if parsed is None:
            raise ValueError("module telescope contains an unnamed parameter")
        parameters.append(
            ModuleParameter(
                parsed.names, parsed.domain, parsed.visibility, group.strip()
            )
        )
        if len(parameters) > MAX_MODULE_PARAMETERS:
            raise ValueError("module telescope exceeds the parameter limit")
    return tuple(parameters)


def _module_directives(source: str, masked: str) -> tuple[ModuleDirective, ...]:
    directives: list[ModuleDirective] = []
    alias_ranges: set[tuple[int, int]] = set()
    for match in _ALIAS_LINE.finditer(masked):
        start = match.start()
        end = _continued_layout_end(masked, match.end(), len(match.group("indent")))
        alias_ranges.add(match.span())
        target, arguments, public, using, hiding, renaming = _directive_body(
            source[match.start("body") : end]
        )
        directives.append(
            ModuleDirective(
                "open-module-alias" if match.group("open") else "module-alias",
                target,
                arguments,
                match.group("alias"),
                public,
                using,
                hiding,
                renaming,
                (start, end),
            )
        )
    for match in _OPEN_LINE.finditer(masked):
        start, end = match.span()
        if (start, end) in alias_ranges or masked[
            match.start("body") :
        ].lstrip().startswith("module "):
            continue
        end = _continued_layout_end(masked, end, len(match.group("indent")))
        body = source[match.start("body") : end]
        # ``open import M`` is one Agda directive whose opened module is M;
        # ``import`` is syntax, not a qualified module named "import".
        body = re.sub(r"^[ \t]*import[ \t]+", "", body, count=1)
        target, arguments, public, using, hiding, renaming = _directive_body(body)
        directives.append(
            ModuleDirective(
                "open",
                target,
                arguments,
                None,
                public,
                using,
                hiding,
                renaming,
                (start, end),
            )
        )
    directives.sort(key=lambda item: item.source_range)
    if len(directives) > MAX_MODULE_DIRECTIVES:
        raise ValueError("module source exceeds the directive limit")
    return tuple(directives)


def _continued_layout_end(masked: str, first_end: int, indentation: int) -> int:
    """Include more-indented continuation lines in one module directive."""

    cursor = first_end
    end = first_end
    while cursor < len(masked) and masked[cursor] == "\n":
        line_start = cursor + 1
        line_end = masked.find("\n", line_start)
        line_end = len(masked) if line_end < 0 else line_end
        if line_end - first_end > MAX_MODULE_HEADER_BYTES:
            raise ValueError("module directive exceeds its text budget")
        line = masked[line_start:line_end]
        if not line.strip():
            cursor = line_end
            continue
        current_indent = len(line) - len(line.lstrip(" \t"))
        if current_indent <= indentation:
            break
        end = line_end
        cursor = line_end
    return end


def _directive_body(
    body: str,
) -> tuple[str, str, bool, str | None, str | None, str | None]:
    stripped = body.strip()
    match = _PLAIN_QNAME.match(stripped)
    if match is None:
        raise ValueError("module directive has no target name")
    target = match.group(0)
    tail = stripped[match.end() :].strip()
    public = bool(re.search(r"(?:^|\s)public(?:\s|$)", tail))
    using = _directive_clause(tail, "using")
    hiding = _directive_clause(tail, "hiding")
    renaming = _directive_clause(tail, "renaming")
    marker_positions = [
        position
        for keyword in ("public", "using", "hiding", "renaming")
        if (position := _keyword_position(tail, keyword)) is not None
    ]
    arguments = tail[: min(marker_positions)].strip() if marker_positions else tail
    return target, arguments, public, using, hiding, renaming


def _keyword_position(text: str, keyword: str) -> int | None:
    match = re.search(rf"(?:^|\s){keyword}(?=\s|$)", text)
    return match.start() if match else None


def _directive_clause(text: str, keyword: str) -> str | None:
    position = _keyword_position(text, keyword)
    if position is None:
        return None
    start = text.find("(", position + len(keyword))
    if start < 0:
        return ""
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return text[start : index + 1]
    return text[start:]
