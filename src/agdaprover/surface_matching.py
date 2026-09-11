"""Source-preserving proposals from Agda's displayed terms.

This is not an Agda parser or a type equality decision procedure. Matching
uses a delimiter tree with source spans; bindings always carry balanced source
slices. Lossy ranking tokens must never be rendered as proof terms. Agda checks
every proposal, including scope, fixity, implicit arguments and conversion.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass

from .type_syntax import parse_named_binder

_LEXEME = re.compile(
    r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'|'
    r'[^\s()\[\]{}:;,→λ∀⦃⦄"]+|[()\[\]{}:;,→λ∀⦃⦄]'
)
_PAIRS = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}


@dataclass(frozen=True)
class SurfaceTerm:
    """A balanced original expression, not a token sequence to concatenate."""

    text: str

    @property
    def key(self) -> tuple[str, ...]:
        view = SurfaceView.parse(self.text)
        if view is None:
            return (self.text,)
        tokens = tuple(token for token, _, _ in view.lexemes)
        # Only discard parentheses enclosing the entire expression.
        while tokens and tokens[0] == "(" and tokens[-1] == ")":
            depth = 0
            for _index, token in enumerate(tokens):
                depth += (token == "(") - (token == ")")
                if depth == 0:
                    break
            if _index != len(tokens) - 1:
                break
            tokens = tokens[1:-1]
        return tokens


@dataclass(frozen=True)
class SurfaceView:
    source: str
    lexemes: tuple[tuple[str, int, int], ...]

    @classmethod
    def parse(cls, text: str) -> SurfaceView | None:
        lexemes: list[tuple[str, int, int]] = []
        stack: list[str] = []
        end = 0
        for match in _LEXEME.finditer(text):
            if text[end : match.start()].strip():
                return None
            token = match.group()
            start, end = match.span()
            if token in {"let", "where", "--"} or text[start : start + 2] == "{-":
                return None
            lexemes.append((token, start, end))
            if token in _PAIRS:
                stack.append(token)
            elif token in _PAIRS.values():
                if not stack or _PAIRS[stack[-1]] != token:
                    return None
                stack.pop()
        if stack or text[end:].strip():
            return None
        return cls(text, tuple(lexemes))


@dataclass(frozen=True)
class _Node:
    token: str
    start: int
    end: int
    children: tuple[_Node, ...] | None = None


def _nodes(view: SurfaceView) -> tuple[_Node, ...]:
    stack: list[tuple[str, int, list[_Node]]] = []
    current: list[_Node] = []
    for token, start, end in view.lexemes:
        if token in _PAIRS:
            stack.append((token, start, current))
            current = []
        elif token in _PAIRS.values():
            opening, begin, parent = stack.pop()
            parent.append(_Node(opening, begin, end, tuple(current)))
            current = parent
        else:
            current.append(_Node(token, start, end))
    return tuple(current)


def _ungroup(nodes: tuple[_Node, ...]) -> tuple[_Node, ...]:
    while len(nodes) == 1 and nodes[0].token == "(" and nodes[0].children is not None:
        nodes = nodes[0].children
    return nodes


def match_surface(
    pattern_text: str,
    target_text: str,
    variables: frozenset[str],
    *,
    longest_first: frozenset[str] = frozenset(),
    step_limit: int = 4096,
) -> dict[str, SurfaceTerm] | None:
    """Match balanced expression trees; return exact source substitutions.

    A wildcard consumes whole siblings, never part of a grouped argument.
    Redundant parentheses enclosing a whole expression may be ignored, but
    inner application grouping and hidden/instance delimiters are retained.
    """
    pattern_view = SurfaceView.parse(pattern_text)
    target_view = SurfaceView.parse(target_text)
    if pattern_view is None or target_view is None:
        return None
    # Bound this optional hint, not the solver's proof search.
    if max(len(pattern_view.lexemes), len(target_view.lexemes)) > 256:
        return None
    steps = 0

    def visit(
        pattern: tuple[_Node, ...],
        target: tuple[_Node, ...],
        bindings: dict[str, SurfaceTerm],
    ) -> Iterator[dict[str, SurfaceTerm]]:
        nonlocal steps
        steps += 1
        if steps > step_limit:
            return
        pattern, target = _ungroup(pattern), _ungroup(target)
        if not pattern:
            if not target:
                yield bindings
            return
        if not target:
            return
        node = pattern[0]
        if node.children is None and node.token in variables:
            ends = range(1, len(target) + 1)
            for stop in reversed(ends) if node.token in longest_first else ends:
                value = SurfaceTerm(target_text[target[0].start : target[stop - 1].end])
                previous = bindings.get(node.token)
                if previous is not None and previous.key != value.key:
                    continue
                yield from visit(
                    pattern[1:], target[stop:], {**bindings, node.token: value}
                )
                if steps > step_limit:
                    return
            return
        other = target[0]
        if node.children is not None or other.children is not None:
            if (
                node.token != other.token
                or node.children is None
                or other.children is None
            ):
                # A parenthesized atom is the same operand; do not flatten
                # groups into adjacent application operands.
                left, right = _ungroup((node,)), _ungroup((other,))
                if left == (node,) and right == (other,):
                    return
            else:
                left, right = node.children, other.children
            for extended in visit(left, right, bindings):
                yield from visit(pattern[1:], target[1:], extended)
                if steps > step_limit:
                    return
            return
        if node.token != other.token:
            return
        yield from visit(pattern[1:], target[1:], bindings)

    return next(visit(_nodes(pattern_view), _nodes(target_view), {}), None)


def substitute_surface(text: str, bindings: dict[str, SurfaceTerm]) -> str | None:
    """Substitute into a binder-free template without losing its delimiters.

    Binder-bearing templates need scoped substitution, not textual replacement;
    decline those hints rather than capture variables. The unchanged template
    and ordinary kernel-driven refinement remain available to search.
    """
    view = SurfaceView.parse(text)
    if view is None:
        return None
    if not any(token in bindings for token, _, _ in view.lexemes):
        return text
    if any(token in {"λ", "∀", ":", "→"} for token, _, _ in view.lexemes):
        return None
    pieces: list[str] = []
    position = 0
    for index, (token, start, end) in enumerate(view.lexemes):
        value = bindings.get(token)
        if value is None:
            continue
        if index + 1 < len(view.lexemes) and view.lexemes[index + 1][0] == "=":
            # Named argument/record-field labels are not variable occurrences.
            continue
        pieces.append(text[position:start])
        pieces.append(value.text if len(value.key) == 1 else f"({value.text})")
        position = end
    pieces.append(text[position:])
    return "".join(pieces)


def scoped_shape_matches(
    pattern: str, target: str, variables: frozenset[str] = frozenset()
) -> bool:
    """A scheduling hint that respects lambda/Pi scope and repeated parameters.

    Only named telescopes and variable lambdas are understood. Unsupported
    patterns lose the hint, not ordinary kernel search. Canonical names never
    become substitutions, proof text, type equality, or cache identities.
    """
    views = (SurfaceView.parse(pattern), SurfaceView.parse(target))
    if any(view is None or len(view.lexemes) > 256 for view in views):
        return False
    prefix = "agdaprover-shape-bound-"
    while prefix in pattern or prefix in target or any(prefix in v for v in variables):
        prefix += "b"

    def canonical(view: SurfaceView) -> str:
        serial = 0

        def bind(name: str, scope: dict[str, str]) -> str:
            nonlocal serial
            value = f"{prefix}{serial}"
            serial += 1
            if name != "_":
                scope[name] = value
            return value

        def visit(nodes: tuple[_Node, ...], scope: dict[str, str]) -> str:
            nodes = _ungroup(nodes)
            arrow = next(
                (
                    i
                    for i, n in enumerate(nodes)
                    if n.children is None and n.token == "→"
                ),
                None,
            )
            if arrow is not None:
                before, after = nodes[:arrow], nodes[arrow + 1 :]
                local = dict(scope)
                is_lambda = bool(before and before[0].token == "λ")
                inputs = before[1:] if is_lambda else before
                rendered: list[str] = []
                for node in inputs:
                    binder = (
                        parse_named_binder(view.source[node.start : node.end])
                        if node.children is not None
                        else None
                    )
                    if binder is not None:
                        bindings = binder.bindings
                        if bindings is None:
                            raise ValueError("unsupported binder")
                        # These nodes need offsets in the original view.
                        colon = next(
                            i
                            for i, n in enumerate(node.children or ())
                            if n.token == ":"
                        )
                        domain = visit((node.children or ())[colon + 1 :], local)
                        names = " ".join(bind(name, local) for _, name in bindings)
                        rendered.append(
                            f"{node.token}{names} : {domain}{_PAIRS[node.token]}"
                        )
                    elif is_lambda:
                        if node.children is not None or node.token in {
                            "λ",
                            "∀",
                            ":",
                            "=",
                            ";",
                            ",",
                        }:
                            raise ValueError("unsupported lambda pattern")
                        rendered.append(bind(node.token, local))
                    else:
                        # An ordinary arrow domain does not bind names.
                        rendered.append(visit((node,), scope))
                return " ".join(
                    (
                        *(("λ",) if is_lambda else ()),
                        *rendered,
                        "→",
                        visit(after, local),
                    )
                )
            rendered = []
            for node in nodes:
                if node.children is not None:
                    rendered.append(
                        f"{node.token}{visit(node.children, scope)}{_PAIRS[node.token]}"
                    )
                elif node.token in {"λ", "∀", ":", "="}:
                    raise ValueError("unsupported scoped syntax")
                else:
                    rendered.append(scope.get(node.token, node.token))
            return " ".join(rendered)

        return visit(_nodes(view), {})

    try:
        left, right = views
        assert left is not None and right is not None
        return match_surface(canonical(left), canonical(right), variables) is not None
    except (ValueError, StopIteration, RecursionError):
        return False
