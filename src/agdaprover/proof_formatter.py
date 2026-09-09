"""Deterministic, bounded formatting for generated Agda proof expressions.

The formatter deliberately accepts only the expression-shaped surface fragment
emitted by AgdaProver.  It never formats surrounding user source, and it
preserves unsupported input byte-for-byte rather than guessing Agda syntax.
Fresh Agda validation remains the semantic authority for every applied patch.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Literal, TypeAlias

from .notation import binary_mixfix_notation, render_declaration_head

FORMATTER_SCHEMA_VERSION = "agdaprover.proof-formatter.v1"
FORMATTER_PROFILE = "agda-unimath-v1"
DEFAULT_LINE_WIDTH = 80
MAX_FORMAT_INPUT_CHARS = 1_000_000
MAX_FORMAT_WORK_CHARS = 2_000_000
MAX_FORMAT_TOKENS = 100_000
MAX_FORMAT_NESTING = 256


class _FormatError(ValueError):
    """An input is outside the deliberately small generated-term grammar."""


@dataclass
class _FormatBudget:
    """Shared parser work allowance, including nested record re-tokenization."""

    characters: int = MAX_FORMAT_WORK_CHARS
    tokens: int = MAX_FORMAT_TOKENS

    def charge_characters(self, count: int) -> None:
        self.characters -= count
        if self.characters < 0:
            raise _FormatError("proof term exceeds the formatter work limit")

    def charge_token(self) -> None:
        self.tokens -= 1
        if self.tokens < 0:
            raise _FormatError("proof term exceeds the formatter token limit")


@dataclass(frozen=True)
class FormattedProof:
    """One formatted proof term plus replayable formatter provenance."""

    text: str
    status: Literal["formatted", "preserved-unsupported"]
    changed: bool
    input_sha256: str
    output_sha256: str
    line_width: int

    @property
    def multiline(self) -> bool:
        return "\n" in self.text

    def metadata(self) -> dict[str, object]:
        return {
            "schema_version": FORMATTER_SCHEMA_VERSION,
            "profile": FORMATTER_PROFILE,
            "scope": "generated-proof-term",
            "status": self.status,
            "changed": self.changed,
            "line_width": self.line_width,
            "input_sha256": self.input_sha256,
            "output_sha256": self.output_sha256,
        }


@dataclass(frozen=True)
class _Atom:
    text: str


@dataclass(frozen=True)
class _Application:
    function: _Expr
    arguments: tuple[_Expr, ...]


@dataclass(frozen=True)
class _Infix:
    left: _Expr
    operator: str
    right: _Expr


@dataclass(frozen=True)
class _Lambda:
    binders: tuple[str, ...]
    body: _Expr


@dataclass(frozen=True)
class _Let:
    name: str
    value: _Expr
    body: _Expr


@dataclass(frozen=True)
class _Record:
    fields: tuple[tuple[str, _Expr], ...]


_Expr: TypeAlias = _Atom | _Application | _Infix | _Lambda | _Let | _Record


@dataclass(frozen=True)
class _GroupTokens:
    items: tuple[_TokenTree, ...]


@dataclass(frozen=True)
class _OpaqueToken:
    text: str


_TokenTree: TypeAlias = str | _GroupTokens | _OpaqueToken


@dataclass(frozen=True)
class _Text:
    value: str


@dataclass(frozen=True)
class _Line:
    pass


@dataclass(frozen=True)
class _Concat:
    parts: tuple[_Doc, ...]


@dataclass(frozen=True)
class _Nest:
    amount: int
    document: _Doc


@dataclass(frozen=True)
class _Group:
    document: _Doc


@dataclass(frozen=True)
class _IfBreak:
    broken: _Doc
    flat: _Doc


_Doc: TypeAlias = _Text | _Line | _Concat | _Nest | _Group | _IfBreak


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _concat(*parts: _Doc) -> _Doc:
    flattened: list[_Doc] = []
    for part in parts:
        if isinstance(part, _Concat):
            flattened.extend(part.parts)
        elif isinstance(part, _Text) and not part.value:
            continue
        else:
            flattened.append(part)
    if not flattened:
        return _Text("")
    if len(flattened) == 1:
        return flattened[0]
    return _Concat(tuple(flattened))


def _flatten_document(document: _Doc) -> _Doc:
    """Select the single-line branch of a document without rendering it."""

    if isinstance(document, _Text):
        return document
    if isinstance(document, _Line):
        return _Text(" ")
    if isinstance(document, _Concat):
        return _concat(*(_flatten_document(part) for part in document.parts))
    if isinstance(document, (_Nest, _Group)):
        return _flatten_document(document.document)
    return _flatten_document(document.flat)


def _parenthesize(document: _Doc, *, branch_spacing: bool = False) -> _Doc:
    if not branch_spacing:
        return _concat(_Text("("), document, _Text(")"))
    # In the broken tree layout the opening parenthesis is the branch marker.
    # Its subtree starts two columns later, and that column becomes the base
    # indentation for every descendant line in the branch.
    return _IfBreak(
        _concat(_Text("( "), _Nest(2, document), _Text(")")),
        _concat(_Text("("), document, _Text(")")),
    )


def _read_quoted(text: str, start: int) -> tuple[str, int]:
    quote = text[start]
    index = start + 1
    escaped = False
    while index < len(text):
        character = text[index]
        if escaped:
            escaped = False
        elif character == "\\":
            escaped = True
        elif character == quote:
            return text[start : index + 1], index + 1
        index += 1
    raise _FormatError("unterminated quoted literal")


def _read_opaque_delimiter(text: str, start: int) -> tuple[str, int]:
    pairs = {"{": "}", "[": "]"}
    opening = text[start]
    closing = pairs[opening]
    stack = [closing]
    index = start + 1
    while index < len(text):
        character = text[index]
        if character in {'"', "'"}:
            _quoted, index = _read_quoted(text, index)
            continue
        if character in pairs:
            stack.append(pairs[character])
        elif character == stack[-1]:
            stack.pop()
            if not stack:
                return text[start : index + 1], index + 1
        index += 1
    raise _FormatError(f"unterminated {opening!r} delimiter")


def _tokenize(text: str, budget: _FormatBudget) -> tuple[_TokenTree, ...]:
    budget.charge_characters(len(text))

    def parse_group(
        index: int, depth: int, closing: bool
    ) -> tuple[list[_TokenTree], int]:
        if depth > MAX_FORMAT_NESTING:
            raise _FormatError("proof term exceeds the formatter nesting limit")
        items: list[_TokenTree] = []
        while index < len(text):
            character = text[index]
            if character.isspace():
                index += 1
                continue
            if character == "-" and index + 1 < len(text) and text[index + 1] == "-":
                raise _FormatError(
                    "comments are outside generated proof-term formatting"
                )
            if character == "(":
                nested, index = parse_group(index + 1, depth + 1, True)
                items.append(_GroupTokens(tuple(nested)))
            elif character == ")":
                if not closing:
                    raise _FormatError("unmatched closing parenthesis")
                return items, index + 1
            elif character in "{[":
                token, index = _read_opaque_delimiter(text, index)
                items.append(_OpaqueToken(token))
            elif character in {'"', "'"}:
                token, index = _read_quoted(text, index)
                items.append(_OpaqueToken(token))
            else:
                end = index + 1
                while (
                    end < len(text)
                    and not text[end].isspace()
                    and text[end] not in "(){}[]"
                ):
                    end += 1
                items.append(text[index:end])
                index = end
            budget.charge_token()
        if closing:
            raise _FormatError("unterminated parenthesized expression")
        return items, index

    tokens, _end = parse_group(0, 0, False)
    return tuple(tokens)


def _flat_token(token: _TokenTree) -> str:
    if isinstance(token, str):
        return token
    if isinstance(token, _OpaqueToken):
        return token.text
    if not token.items:
        raise _FormatError("empty parentheses are outside generated proof terms")
    return f"({' '.join(_flat_token(item) for item in token.items)})"


def _is_surface_operator(text: str) -> bool:
    if text in {"=", ",", "-", "."}:
        return True
    if not text or "_" in text or text in {"λ", "→", "let", "in"}:
        return False
    identifier_characters = {"-", ".", "'", "′"}
    return any(
        not character.isalnum() and character not in identifier_characters
        for character in text
    )


def _parse_record(
    token: _OpaqueToken,
    budget: _FormatBudget,
    depth: int,
) -> _Record:
    text = token.text
    if not (text.startswith("{") and text.endswith("}")):
        raise _FormatError("record expression has malformed braces")
    content = _tokenize(text[1:-1], budget)
    fields: list[tuple[str, _Expr]] = []
    start = 0
    for index in range(len(content) + 1):
        if index < len(content) and content[index] != ";":
            continue
        field = content[start:index]
        start = index + 1
        equals = tuple(position for position, item in enumerate(field) if item == "=")
        if len(equals) != 1:
            raise _FormatError("record field has no unique assignment")
        equals_index = equals[0]
        if equals_index != 1 or not isinstance(field[0], str):
            raise _FormatError("record field name is outside the generated grammar")
        if equals_index + 1 >= len(field):
            raise _FormatError("record field has no value")
        fields.append(
            (
                field[0],
                _parse_expression(tuple(field[equals_index + 1 :]), budget, depth + 1),
            )
        )
    if not fields:
        raise _FormatError("empty record expression is outside generated proofs")
    return _Record(tuple(fields))


def _parse_expression(
    items: tuple[_TokenTree, ...],
    budget: _FormatBudget,
    depth: int = 0,
) -> _Expr:
    if depth > MAX_FORMAT_NESTING:
        raise _FormatError("proof term exceeds the formatter nesting limit")
    if not items:
        raise _FormatError("empty proof expression")

    if len(items) == 2 and items[0] == "record" and isinstance(items[1], _OpaqueToken):
        return _parse_record(items[1], budget, depth)

    if items[0] == "λ":
        try:
            arrow = items.index("→")
        except ValueError as error:
            raise _FormatError("lambda has no body arrow") from error
        binders = tuple(_flat_token(item) for item in items[1:arrow])
        if not binders or arrow + 1 >= len(items):
            raise _FormatError("lambda has no binder or body")
        return _Lambda(
            binders,
            _parse_expression(items[arrow + 1 :], budget, depth + 1),
        )

    if len(items) >= 5 and items[0] == "let" and isinstance(items[1], str):
        if items[2] == "=":
            try:
                separator = items.index("in", 3)
            except ValueError:
                separator = -1
            if separator > 3 and separator + 1 < len(items):
                return _Let(
                    items[1],
                    _parse_expression(items[3:separator], budget, depth + 1),
                    _parse_expression(items[separator + 1 :], budget, depth + 1),
                )

    operators = tuple(
        index
        for index, item in enumerate(items)
        if isinstance(item, str) and _is_surface_operator(item)
    )
    if len(operators) == 1:
        operator_index = operators[0]
        if 0 < operator_index < len(items) - 1:
            operator = items[operator_index]
            assert isinstance(operator, str)
            return _Infix(
                _parse_expression(items[:operator_index], budget, depth + 1),
                operator,
                _parse_expression(items[operator_index + 1 :], budget, depth + 1),
            )

    parsed = tuple(
        _parse_expression(item.items, budget, depth + 1)
        if isinstance(item, _GroupTokens)
        else _Atom(item.text if isinstance(item, _OpaqueToken) else item)
        for item in items
    )

    function, *arguments = parsed
    if not arguments:
        return function
    if isinstance(function, _Atom):
        notation = binary_mixfix_notation(function.text)
        if notation is not None and len(arguments) >= 2:
            infix: _Expr = _Infix(arguments[0], notation.surface_operator, arguments[1])
            if len(arguments) == 2:
                return infix
            return _Application(infix, tuple(arguments[2:]))
    return _Application(function, tuple(arguments))


def _atom_document(atom: _Atom, *, declaration_head: bool = False) -> _Doc:
    text = atom.text
    if (
        declaration_head
        and text != "_"
        and "_" in text
        and not text.startswith(("{", "["))
    ):
        text = render_declaration_head(text)
    return _Text(text)


def _semantic_parentheses(expression: _Expr, document: _Doc) -> _Doc:
    if isinstance(expression, _Atom):
        return document
    return _parenthesize(document, branch_spacing=True)


def _record_document(record: _Record) -> _Doc:
    field_documents: list[_Doc] = []
    for index, (name, value) in enumerate(record.fields):
        prefix = "{ " if index == 0 else "; "
        field_documents.append(
            _Group(
                _concat(
                    _Text(f"{prefix}{name} ="),
                    _Nest(2, _concat(_Line(), _expression_document(value))),
                )
            )
        )
    return _Group(
        _concat(
            _Text("record"),
            _Nest(
                2,
                _concat(
                    *(_concat(_Line(), field) for field in field_documents),
                    _Line(),
                    _Text("}"),
                ),
            ),
        )
    )


def _expression_document(
    expression: _Expr,
    parent_precedence: int = -1,
    *,
    branch_context: bool = False,
) -> _Doc:
    if isinstance(expression, _Atom):
        return _atom_document(expression)

    if isinstance(expression, _Lambda):
        prefix = _Text(f"λ {' '.join(expression.binders)} →")
        document = _Group(
            _concat(
                prefix,
                _Nest(2, _concat(_Line(), _expression_document(expression.body))),
            )
        )
        return _parenthesize(document) if parent_precedence > 0 else document

    if isinstance(expression, _Let):
        value = _expression_document(expression.value)
        body = _expression_document(expression.body)
        flat_document = _concat(
            _Text(f"let {expression.name} = "),
            value,
            _Text(" in "),
            body,
        )
        # A generated proof is often inserted into a hole late on an existing
        # clause line.  Agda's layout column for a broken inline ``let`` would
        # then depend on that physical source column.  Keep lets flat so the
        # formatter is context independent and cannot manufacture a malformed
        # layout block.  Their lambda/application children remain explicitly
        # parenthesized, so this changes presentation only.
        let_document = _flatten_document(flat_document)
        return _parenthesize(let_document) if parent_precedence > 0 else let_document

    if isinstance(expression, _Record):
        return _record_document(expression)

    if isinstance(expression, _Infix):
        left = _expression_document(expression.left, branch_context=True)
        right = _expression_document(expression.right, branch_context=True)
        # At precedence 2, lambdas, lets, and nested infix expressions need
        # semantic grouping in the flat form.  Reuse the same subtree document
        # for the broken form so preparing alternatives remains linear.
        flat_left = (
            _parenthesize(left)
            if isinstance(expression.left, (_Lambda, _Let, _Infix))
            else left
        )
        flat_right = (
            _parenthesize(right)
            if isinstance(expression.right, (_Lambda, _Let, _Infix))
            else right
        )
        broken_left = _parenthesize(
            left,
            branch_spacing=True,
        )
        broken_right = _parenthesize(
            right,
            branch_spacing=True,
        )
        document = _Group(
            _concat(
                _IfBreak(broken_left, flat_left),
                _Text(f" {expression.operator}"),
                _Line(),
                _IfBreak(broken_right, flat_right),
            )
        )
        return _parenthesize(document) if parent_precedence > 1 else document

    function = _expression_document(expression.function, 2)
    if isinstance(expression.function, _Atom):
        function = _atom_document(expression.function, declaration_head=True)
    arguments: list[_Doc] = []
    for argument in expression.arguments:
        rendered = _expression_document(argument, branch_context=branch_context)
        branch = _semantic_parentheses(argument, rendered)
        if branch_context and not isinstance(argument, _Atom):
            arguments.append(_concat(_Line(), branch))
        else:
            arguments.append(_Nest(2, _concat(_Line(), branch)))
    document = _Group(
        _concat(
            function,
            _concat(*arguments),
        )
    )
    return _parenthesize(document) if parent_precedence > 2 else document


_RenderFrame: TypeAlias = tuple[int, bool, _Doc]


def _fits(remaining: int, stack: list[_RenderFrame]) -> bool:
    pending = list(stack)
    while remaining >= 0 and pending:
        indentation, flat, document = pending.pop()
        if isinstance(document, _Text):
            remaining -= len(document.value)
        elif isinstance(document, _Line):
            if flat:
                remaining -= 1
            else:
                return True
        elif isinstance(document, _Concat):
            pending.extend(
                (indentation, flat, part) for part in reversed(document.parts)
            )
        elif isinstance(document, _Nest):
            pending.append((indentation + document.amount, flat, document.document))
        elif isinstance(document, _Group):
            pending.append((indentation, True, document.document))
        else:
            selected = document.flat if flat else document.broken
            pending.append((indentation, flat, selected))
    return remaining >= 0


def _render_document(
    document: _Doc,
    *,
    line_width: int,
    initial_column: int,
    base_indentation: int,
) -> str:
    output: list[str] = []
    column = initial_column
    stack: list[_RenderFrame] = [(base_indentation, False, document)]
    while stack:
        indentation, flat, current = stack.pop()
        if isinstance(current, _Text):
            output.append(current.value)
            column += len(current.value)
        elif isinstance(current, _Line):
            if flat:
                output.append(" ")
                column += 1
            else:
                output.append("\n" + " " * indentation)
                column = indentation
        elif isinstance(current, _Concat):
            stack.extend((indentation, flat, part) for part in reversed(current.parts))
        elif isinstance(current, _Nest):
            stack.append((indentation + current.amount, flat, current.document))
        elif isinstance(current, _Group):
            candidate = (indentation, True, current.document)
            stack.append(
                candidate
                if _fits(line_width - column, [*stack, candidate])
                else (indentation, False, current.document)
            )
        else:
            selected = current.flat if flat else current.broken
            stack.append((indentation, flat, selected))
    return "".join(output)


def format_proof_term(
    proof_term: str,
    *,
    line_width: int = DEFAULT_LINE_WIDTH,
    initial_column: int = 0,
    base_indentation: int = 0,
) -> FormattedProof:
    """Format one completed generated proof term or preserve it on uncertainty.

    ``initial_column`` accounts for an existing clause prefix on the first
    line.  ``base_indentation`` is used after every formatter-inserted newline.
    Both are explicit so rendering is stable and independent of editor state.
    """

    if line_width <= 0 or initial_column < 0 or base_indentation < 0:
        raise ValueError("formatter dimensions must be nonnegative")
    original = proof_term
    input_digest = _sha256(original)
    if not original.strip() or len(original) > MAX_FORMAT_INPUT_CHARS:
        return FormattedProof(
            original,
            "preserved-unsupported",
            False,
            input_digest,
            input_digest,
            line_width,
        )
    try:
        budget = _FormatBudget()
        expression = _parse_expression(_tokenize(original, budget), budget)
        rendered = _render_document(
            _expression_document(expression),
            line_width=line_width,
            initial_column=initial_column,
            base_indentation=base_indentation,
        )
    except (RecursionError, _FormatError, ValueError):
        return FormattedProof(
            original,
            "preserved-unsupported",
            False,
            input_digest,
            input_digest,
            line_width,
        )
    return FormattedProof(
        rendered,
        "formatted",
        rendered != original,
        input_digest,
        _sha256(rendered),
        line_width,
    )


def validate_formatter_metadata(
    value: object,
    *,
    output_text: str | None = None,
) -> None:
    """Reject malformed formatter provenance embedded in a source edit."""

    if not isinstance(value, dict):
        raise ValueError("proof formatter metadata must be an object")
    expected = {
        "schema_version",
        "profile",
        "scope",
        "status",
        "changed",
        "line_width",
        "input_sha256",
        "output_sha256",
    }
    if set(value) != expected:
        raise ValueError("proof formatter metadata fields differ from its schema")
    if value["schema_version"] != FORMATTER_SCHEMA_VERSION:
        raise ValueError("unsupported proof formatter metadata version")
    if value["profile"] != FORMATTER_PROFILE:
        raise ValueError("unsupported proof formatter profile")
    if value["scope"] != "generated-proof-term":
        raise ValueError("proof formatter metadata has the wrong scope")
    if value["status"] not in {"formatted", "preserved-unsupported"}:
        raise ValueError("proof formatter metadata has an invalid status")
    if not isinstance(value["changed"], bool):
        raise ValueError("proof formatter metadata changed flag is invalid")
    if not isinstance(value["line_width"], int) or value["line_width"] <= 0:
        raise ValueError("proof formatter metadata line width is invalid")
    for field in ("input_sha256", "output_sha256"):
        digest = value[field]
        if not isinstance(digest, str) or len(digest) != 64:
            raise ValueError(f"proof formatter metadata {field} is invalid")
        try:
            int(digest, 16)
        except ValueError as error:
            raise ValueError(f"proof formatter metadata {field} is invalid") from error
    if not value["changed"] and value["input_sha256"] != value["output_sha256"]:
        raise ValueError("unchanged proof formatter metadata has unequal digests")
    if value["status"] == "preserved-unsupported" and value["changed"]:
        raise ValueError("preserved proof formatter metadata claims a change")
    if output_text is not None and value["output_sha256"] != _sha256(output_text):
        raise ValueError("proof formatter output digest does not match its edit")


__all__ = [
    "DEFAULT_LINE_WIDTH",
    "FORMATTER_PROFILE",
    "FORMATTER_SCHEMA_VERSION",
    "FormattedProof",
    "MAX_FORMAT_INPUT_CHARS",
    "format_proof_term",
    "validate_formatter_metadata",
]
