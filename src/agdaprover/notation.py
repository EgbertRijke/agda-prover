"""Small, semantics-preserving Agda notation renderer.

Search keeps declaration heads and application arguments separate.  This
module uses the holes in an Agda name only when rendering a complete binary
application; Agda remains responsible for parsing and accepting the result.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass

_BINARY_MIXFIX = re.compile(
    r"^(?:(?P<qualifier>[^\s()]+)\.)?_(?P<operator>[^_\s().]+)_$"
)
_PLAIN_NAME = re.compile(
    r"[\w′₀-₉⁰-⁹-]+(?:\.[\w′₀-₉⁰-⁹-]+)*",
    re.UNICODE,
)
_ATOMIC_EXPRESSION = re.compile(r"[^\s(){}\[\],;]+")


@dataclass(frozen=True)
class BinaryMixfixNotation:
    """The two-hole surface notation encoded by one Agda declaration name."""

    name: str
    operator: str
    qualifier: str | None = None

    @property
    def surface_operator(self) -> str:
        """Return the operator token used between the two operands."""

        return (
            f"{self.qualifier}.{self.operator}"
            if self.qualifier is not None
            else self.operator
        )


def binary_mixfix_head(surface_operator: str) -> str:
    """Recover the declaration head denoted by a surface operator token.

    Agda qualifies an infix use as ``left Module.op right`` while the same
    declaration in prefix position is ``Module._op_``. Keeping this
    conversion beside the renderer prevents search code from manufacturing
    the invalid ``_Module.op_`` spelling.
    """

    operator = surface_operator.strip()
    if not operator or any(character.isspace() for character in operator):
        raise ValueError("an Agda surface operator must be one nonempty token")
    if "." not in operator:
        return f"_{operator}_"
    qualifier, unqualified = operator.rsplit(".", 1)
    if not qualifier or not unqualified or _PLAIN_NAME.fullmatch(qualifier) is None:
        raise ValueError("an Agda qualified surface operator is malformed")
    return f"{qualifier}._{unqualified}_"


def strip_outer_parentheses(text: str) -> str:
    """Remove only balanced parentheses enclosing the complete expression."""

    current = text.strip()
    while current.startswith("(") and current.endswith(")"):
        depth = 0
        closes_at_end = False
        for index, character in enumerate(current):
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth < 0:
                    return current
                if depth == 0:
                    closes_at_end = index == len(current) - 1
                    break
        if not closes_at_end:
            break
        current = current[1:-1].strip()
    return current


def binary_mixfix_notation(expression: str) -> BinaryMixfixNotation | None:
    """Recognize a possibly parenthesized, optionally qualified ``_op_`` head."""

    name = strip_outer_parentheses(expression)
    matched = _BINARY_MIXFIX.fullmatch(name)
    if matched is None:
        return None
    qualifier = matched.group("qualifier")
    if qualifier is not None and _PLAIN_NAME.fullmatch(qualifier) is None:
        return None
    return BinaryMixfixNotation(
        name=name,
        operator=matched.group("operator"),
        qualifier=qualifier,
    )


def render_declaration_head(name: str) -> str:
    """Render NAME in the prefix position accepted by Agda's parser."""

    unwrapped = strip_outer_parentheses(name)
    if not unwrapped:
        raise ValueError("an Agda declaration head cannot be empty")
    if _PLAIN_NAME.fullmatch(unwrapped) and "_" not in unwrapped:
        return unwrapped
    return f"({unwrapped})"


def _render_argument(expression: str) -> str:
    """Render one application argument with exactly the needed grouping."""

    unwrapped = strip_outer_parentheses(expression)
    if not unwrapped:
        raise ValueError("an Agda application argument cannot be empty")
    if unwrapped == "_" or (
        _ATOMIC_EXPRESSION.fullmatch(unwrapped)
        and binary_mixfix_notation(unwrapped) is None
    ):
        return unwrapped
    return f"({unwrapped})"


def render_application(
    head: str,
    arguments: Iterable[str],
    *,
    parenthesize_infix: bool = True,
) -> str:
    """Render a declaration application, using binary mixfix notation safely.

    Binary applications are grouped according to the explicit application
    tree rather than an inferred fixity.  Consequently the output preserves
    meaning even when the operator is declared left-, right-, or non-
    associative.  Partial and non-binary mixfix applications retain Agda's
    unambiguous parenthesized prefix form.
    """

    rendered_arguments = tuple(_render_argument(value) for value in arguments)
    notation = binary_mixfix_notation(head)
    if notation is not None and len(rendered_arguments) >= 2:
        expression = (
            f"{rendered_arguments[0]} {notation.surface_operator} "
            f"{rendered_arguments[1]}"
        )
        remaining = rendered_arguments[2:]
        if parenthesize_infix or remaining:
            expression = f"({expression})"
        if remaining:
            expression = " ".join((expression, *remaining))
        return expression
    rendered_head = render_declaration_head(head)
    if not rendered_arguments:
        return rendered_head
    return " ".join((rendered_head, *rendered_arguments))


__all__ = [
    "BinaryMixfixNotation",
    "binary_mixfix_head",
    "binary_mixfix_notation",
    "render_application",
    "render_declaration_head",
    "strip_outer_parentheses",
]
