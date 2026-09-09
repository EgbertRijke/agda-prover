"""Bounded proof-relevant rewriting from algebraic laws visible in Agda.

The engine recognizes laws by the shape of their result types, never by a
declaration, datatype, constructor, or operator name.  It retains an explicit
proof for every edge and uses caller-supplied congruence, symmetry, and
transitivity combinators.  Agda validates the resulting term afterwards.
"""

from __future__ import annotations

import re
from collections import deque
from dataclasses import dataclass

from .notation import render_application, strip_outer_parentheses
from .relation_path import parse_relation
from .type_syntax import (
    normalize_type_text,
    parse_named_binder,
    split_adjacent_binders,
    split_top_level_arrows,
)


@dataclass(frozen=True)
class _Term:
    atom: str | None = None
    left: _Term | None = None
    operator: str | None = None
    right: _Term | None = None

    @property
    def is_node(self) -> bool:
        return self.operator is not None

    @property
    def key(self) -> str:
        return normalize_type_text(self.render())

    def render(self) -> str:
        if not self.is_node:
            return self.atom or ""
        assert self.left is not None and self.right is not None
        return f"({self.left.render()} {self.operator} {self.right.render()})"


@dataclass(frozen=True)
class _Law:
    expression: str
    operator: str
    association: str
    kind: str


@dataclass(frozen=True)
class _Step:
    term: _Term
    proof: str
    nodes: int


def _top_level_operator_positions(text: str, operator: str) -> tuple[int, ...]:
    positions: list[int] = []
    stack: list[str] = []
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    index = 0
    while index < len(text):
        character = text[index]
        if character in pairs:
            stack.append(pairs[character])
            index += 1
            continue
        if character in closing:
            if stack and stack[-1] == character:
                stack.pop()
            index += 1
            continue
        if not stack and text.startswith(operator, index):
            end = index + len(operator)
            left_ok = index == 0 or text[index - 1].isspace()
            right_ok = end == len(text) or text[end].isspace()
            if left_ok and right_ok:
                positions.append(index)
                index = end
                continue
        index += 1
    return tuple(positions)


def _parse_term(text: str, operator: str, association: str) -> _Term:
    surface = strip_outer_parentheses(text)
    positions = _top_level_operator_positions(surface, operator)
    if not positions:
        return _Term(atom=surface)
    position = positions[-1] if association == "left" else positions[0]
    left = surface[:position].strip()
    right = surface[position + len(operator) :].strip()
    if not left or not right:
        return _Term(atom=surface)
    return _Term(
        left=_parse_term(left, operator, association),
        operator=operator,
        right=_parse_term(right, operator, association),
    )


def _explicit_binders(type_text: str) -> tuple[str, ...]:
    try:
        domains = split_top_level_arrows(type_text)[:-1]
    except ValueError:
        return ()
    names: list[str] = []
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is not None and parsed.visibility == "explicit":
                names.extend(parsed.names)
    return tuple(names)


def _operator_candidates(
    left: str, right: str, binders: tuple[str, ...]
) -> tuple[str, ...]:
    tokens = re.findall(r"[^\s()\[\]{}⦃⦄]+", f"{left} {right}")
    return tuple(
        dict.fromkeys(
            token
            for token in tokens
            if token not in binders
            and token not in {"=", ":", "→"}
            and (tokens.count(token) >= 2 or not token[0].isalnum())
        )
    )


def _is_atom(term: _Term, value: str) -> bool:
    return not term.is_node and normalize_type_text(term.atom or "") == value


def _classify_law(
    expression: str,
    type_text: str,
    relation_operator: str,
) -> _Law | None:
    try:
        result = split_top_level_arrows(type_text)[-1]
    except ValueError:
        return None
    relation = parse_relation(result, expected_operator=relation_operator)
    if relation is None:
        return None
    binders = _explicit_binders(type_text)
    for operator in _operator_candidates(relation.left, relation.right, binders):
        for association in ("left", "right"):
            left = _parse_term(relation.left, operator, association)
            right = _parse_term(relation.right, operator, association)
            if len(binders) == 2 and left.is_node and right.is_node:
                assert left.left is not None and left.right is not None
                assert right.left is not None and right.right is not None
                first = normalize_type_text(binders[0])
                second = normalize_type_text(binders[1])
                if (
                    _is_atom(left.left, first)
                    and _is_atom(left.right, second)
                    and _is_atom(right.left, second)
                    and _is_atom(right.right, first)
                ):
                    return _Law(expression, operator, association, "commutative")
            if len(binders) == 3 and left.is_node and right.is_node:
                first, second, third = map(normalize_type_text, binders)
                if left.left is None or left.right is None:
                    continue
                if right.left is None or right.right is None:
                    continue
                if not left.left.is_node or not right.right.is_node:
                    continue
                assert left.left.left is not None and left.left.right is not None
                assert right.right.left is not None and right.right.right is not None
                if (
                    _is_atom(left.left.left, first)
                    and _is_atom(left.left.right, second)
                    and _is_atom(left.right, third)
                    and _is_atom(right.left, first)
                    and _is_atom(right.right.left, second)
                    and _is_atom(right.right.right, third)
                ):
                    return _Law(expression, operator, association, "associative")
    return None


def _replace_child(
    parent: _Term,
    *,
    left: _Term | None = None,
    right: _Term | None = None,
) -> _Term:
    assert parent.left is not None and parent.right is not None
    return _Term(
        left=left or parent.left,
        operator=parent.operator,
        right=right or parent.right,
    )


def proof_relevant_ac_path(
    *,
    left: str,
    right: str,
    relation_operator: str,
    evidence: tuple[tuple[str, str], ...],
    declarations: tuple[tuple[str, str], ...],
    lift_name: str,
    sym_name: str,
    trans_name: str,
    context_variable: str = "agdaprover-value",
    max_states: int = 256,
    max_nodes: int = 15,
) -> str | None:
    """Find a bounded evidence path using learned AC laws and concrete edges."""

    laws = tuple(
        law
        for expression, type_text in declarations
        if (law := _classify_law(expression, type_text, relation_operator)) is not None
    )
    associative = next((law for law in laws if law.kind == "associative"), None)
    commutative = next((law for law in laws if law.kind == "commutative"), None)
    if associative is None or commutative is None:
        return None
    if (
        associative.operator != commutative.operator
        or associative.association != commutative.association
    ):
        return None
    operator = associative.operator
    association = associative.association
    start = _parse_term(left, operator, association)
    target = _parse_term(right, operator, association)
    if start.key == target.key:
        return None

    concrete: list[tuple[_Term, _Term, str]] = []
    for expression, type_text in evidence:
        relation = parse_relation(type_text, expected_operator=relation_operator)
        if relation is None:
            continue
        concrete.append(
            (
                _parse_term(relation.left, operator, association),
                _parse_term(relation.right, operator, association),
                expression,
            )
        )

    marker = context_variable

    def root_steps(term: _Term) -> tuple[_Step, ...]:
        generated: list[_Step] = []
        for edge_left, edge_right, expression in concrete:
            if term.key == edge_left.key:
                generated.append(_Step(edge_right, expression, 1))
            if term.key == edge_right.key:
                generated.append(_Step(edge_left, f"{sym_name} ({expression})", 2))
        if term.is_node:
            assert term.left is not None and term.right is not None
            generated.append(
                _Step(
                    _Term(
                        left=term.right,
                        operator=operator,
                        right=term.left,
                    ),
                    render_application(
                        commutative.expression,
                        (term.left.render(), term.right.render()),
                    ),
                    1,
                )
            )
            if term.left.is_node:
                assert term.left.left is not None and term.left.right is not None
                application = render_application(
                    associative.expression,
                    (
                        term.left.left.render(),
                        term.left.right.render(),
                        term.right.render(),
                    ),
                )
                generated.append(
                    _Step(
                        _Term(
                            left=term.left.left,
                            operator=operator,
                            right=_Term(
                                left=term.left.right,
                                operator=operator,
                                right=term.right,
                            ),
                        ),
                        application,
                        1,
                    )
                )
            if term.right.is_node:
                assert term.right.left is not None and term.right.right is not None
                application = render_application(
                    associative.expression,
                    (
                        term.left.render(),
                        term.right.left.render(),
                        term.right.right.render(),
                    ),
                )
                generated.append(
                    _Step(
                        _Term(
                            left=_Term(
                                left=term.left,
                                operator=operator,
                                right=term.right.left,
                            ),
                            operator=operator,
                            right=term.right.right,
                        ),
                        f"{sym_name} ({application})",
                        2,
                    )
                )
        return tuple(generated)

    def steps(term: _Term) -> tuple[_Step, ...]:
        generated = list(root_steps(term))
        if not term.is_node:
            return tuple(generated)
        assert term.left is not None and term.right is not None
        for child in steps(term.left):
            outer = _replace_child(term, left=child.term)
            body = _replace_child(term, left=_Term(atom=marker)).render()
            generated.append(
                _Step(
                    outer,
                    f"{lift_name} (λ {marker} → {body}) ({child.proof})",
                    child.nodes + 2,
                )
            )
        for child in steps(term.right):
            outer = _replace_child(term, right=child.term)
            body = _replace_child(term, right=_Term(atom=marker)).render()
            generated.append(
                _Step(
                    outer,
                    f"{lift_name} (λ {marker} → {body}) ({child.proof})",
                    child.nodes + 2,
                )
            )
        return tuple(generated)

    queue: deque[tuple[_Term, str | None, int]] = deque([(start, None, 0)])
    best = {start.key: 0}
    while queue and len(best) <= max_states:
        current, proof, nodes = queue.popleft()
        for step in steps(current):
            total = nodes + step.nodes + (1 if proof is not None else 0)
            if total > max_nodes:
                continue
            combined = (
                step.proof
                if proof is None
                else f"{trans_name} ({proof}) ({step.proof})"
            )
            if step.term.key == target.key:
                return combined
            previous = best.get(step.term.key)
            if previous is not None and previous <= total:
                continue
            best[step.term.key] = total
            queue.append((step.term, combined, total))
    return None


__all__ = ["proof_relevant_ac_path"]
