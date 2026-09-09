"""Bounded, datatype-neutral path search for proof-relevant binary relations.

The search learns a relation token from the live goal, obtains every term type
from Agda, and treats accepted inhabitants as directed edges.  Unary and
binary declarations visible at the interaction are merely typed operators on
those edges.  No datatype, constructor, equality, inverse, congruence, or
composition name has a distinguished meaning here.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass
from typing import Protocol

from .bridge.contracts import StateToken
from .contracts import GoalInfo
from .notation import (
    binary_mixfix_notation,
    render_application,
    strip_outer_parentheses,
)
from .type_syntax import (
    normalize_type_text,
    parse_named_binder,
    split_adjacent_binders,
    split_top_level_arrows,
)

_WORD = re.compile(r"^[^\W\d]\w*$", re.UNICODE)
_EXCLUDED_OPERATORS = frozenset({"→", "=", ":", "::", "∀"})


class TypeInference(Protocol):
    def infer_type(
        self,
        state: StateToken,
        *,
        goal_id: int,
        expression: str,
    ) -> str | None: ...


@dataclass(frozen=True)
class RelationView:
    left: str
    operator: str
    right: str

    @property
    def key(self) -> tuple[str, str]:
        return (_endpoint_key(self.left), _endpoint_key(self.right))


@dataclass(frozen=True)
class RelationHead:
    expression: str
    type_text: str
    order: int

    @property
    def arity(self) -> int:
        return explicit_arity(self.type_text)


@dataclass(frozen=True)
class RelationTerm:
    expression: str
    type_text: str
    edge: RelationView
    generators: frozenset[str]
    node_count: int


@dataclass
class RelationPathStats:
    detected: bool = False
    operator: str | None = None
    inference_queries: int = 0
    terms_inferred: int = 0
    edges_retained: int = 0
    applications_generated: int = 0
    applications_pruned: int = 0
    composition_rounds: int = 0
    frontier_peak: int = 0
    seed_terms: int = 0
    elapsed_ms: float = 0.0

    def to_dict(self) -> dict[str, object]:
        return {key: value for key, value in self.__dict__.items() if value is not None}


@dataclass(frozen=True)
class RelationPathResult:
    expression: str | None
    stats: RelationPathStats


def explicit_arity(type_text: str) -> int:
    """Count displayed explicit binders in an Agda declaration type."""

    try:
        domains = split_top_level_arrows(type_text)[:-1]
    except ValueError:
        return 0
    count = 0
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is None:
                if not group.lstrip().startswith(("{", "⦃")):
                    count += 1
            elif parsed.visibility == "explicit":
                count += len(parsed.names)
    return count


def mixfix_binary_operator(expression: str) -> str | None:
    """Recover the token of a simple binary mixfix declaration."""

    notation = binary_mixfix_notation(expression)
    return notation.operator if notation is not None else None


def _top_level_tokens(text: str) -> tuple[tuple[str, int, int], ...]:
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    stack: list[str] = []
    tokens: list[tuple[str, int, int]] = []
    start: int | None = None
    for index, character in enumerate(text):
        if character in pairs:
            stack.append(pairs[character])
        elif character in closing and stack and stack[-1] == character:
            stack.pop()
        if character.isspace() and not stack:
            if start is not None:
                tokens.append((text[start:index], start, index))
                start = None
        elif start is None:
            start = index
    if start is not None:
        tokens.append((text[start:], start, len(text)))
    return tuple(tokens)


def parse_relation(
    type_text: str,
    *,
    allowed_operators: frozenset[str] = frozenset(),
    expected_operator: str | None = None,
) -> RelationView | None:
    """Parse one top-level infix relation without assigning it semantics."""

    text = " ".join(type_text.strip().split())
    tokens = _top_level_tokens(text)
    if len(tokens) < 3:
        return None
    candidates: list[tuple[tuple[int, int, int, int], int, str]] = []
    middle = (len(tokens) - 1) / 2
    token_counts = {
        token: sum(1 for candidate, _start, _end in tokens if candidate == token)
        for token, _start, _end in tokens
    }
    for index, (token, _start, _end) in enumerate(tokens[1:-1], start=1):
        if token in _EXCLUDED_OPERATORS:
            continue
        if any(character in "()[]{}⦃⦄" for character in token):
            # Parenthesized endpoint applications are single top-level terms,
            # not operator tokens.  Treating one as a symbolic relation head
            # corrupts both endpoints as soon as a recursive law nests an
            # application on the right.
            continue
        if expected_operator is not None and token != expected_operator:
            continue
        admitted = token in allowed_operators
        symbolic = _WORD.fullmatch(token) is None
        if not admitted and not symbolic:
            continue
        candidates.append(
            (
                (
                    0 if expected_operator == token else 1,
                    token_counts[token],
                    0 if admitted else 1,
                    int(abs(index - middle) * 2),
                ),
                index,
                token,
            )
        )
    if not candidates:
        return None
    _priority, index, operator = min(candidates)
    left = text[: tokens[index][1]].strip()
    right = text[tokens[index][2] :].strip()
    if not left or not right:
        return None
    return RelationView(left, operator, right)


def _endpoint_key(text: str) -> str:
    return normalize_type_text(strip_outer_parentheses(text))


def _application(head: RelationHead, arguments: tuple[RelationTerm, ...]) -> str:
    return render_application(
        head.expression,
        (argument.expression for argument in arguments),
    )


def _endpoint_overlap(edge: RelationView, goal: RelationView) -> int:
    goal_tokens = set(re.findall(r"[^\W_]+|[^\w\s]", goal.left + " " + goal.right))
    edge_tokens = set(re.findall(r"[^\W_]+|[^\w\s]", edge.left + " " + edge.right))
    return len(goal_tokens & edge_tokens)


def solve_relation_path(
    session: TypeInference,
    state: StateToken,
    goal: GoalInfo,
    heads: tuple[RelationHead, ...],
    *,
    query_budget: int,
    deadline: float,
    max_terms: int = 128,
    seed_terms: tuple[tuple[str, str], ...] = (),
) -> RelationPathResult:
    """Search a small kernel-typed relation graph for the goal edge."""

    started = time.monotonic()
    stats = RelationPathStats()
    allowed = frozenset(
        operator
        for head in heads
        if (operator := mixfix_binary_operator(head.expression)) is not None
    )
    target = parse_relation(goal.target, allowed_operators=allowed)
    if target is None or query_budget <= 0:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return RelationPathResult(None, stats)
    stats.detected = True
    stats.operator = target.operator
    usable_heads = tuple(
        head
        for head in heads
        if head.arity in {1, 2} and target.operator in head.type_text
    )
    terms: list[RelationTerm] = []
    expressions: set[str] = set()
    edge_expressions: dict[tuple[str, str], list[RelationTerm]] = {}

    def retain(term: RelationTerm) -> str | None:
        if term.expression in expressions:
            return None
        bucket = edge_expressions.get(term.edge.key, [])
        if len(bucket) >= 2 and all(
            existing.node_count <= term.node_count for existing in bucket
        ):
            stats.applications_pruned += 1
            expressions.add(term.expression)
            return None
        expressions.add(term.expression)
        terms.append(term)
        edge_expressions.setdefault(term.edge.key, []).append(term)
        stats.edges_retained += 1
        stats.frontier_peak = max(stats.frontier_peak, len(terms))
        if term.edge.key == target.key:
            return term.expression
        return None

    initial_entries = (
        *(
            (entry.name, entry.type)
            for entry in goal.context
            if entry.in_scope and entry.name
        ),
        *seed_terms,
    )
    for expression, type_text in initial_entries:
        edge = parse_relation(type_text, expected_operator=target.operator)
        if edge is None:
            continue
        if (expression, type_text) in seed_terms:
            stats.seed_terms += 1
        solved = retain(
            RelationTerm(
                expression,
                type_text,
                edge,
                frozenset({expression}),
                1,
            )
        )
        if solved is not None:
            stats.elapsed_ms = (time.monotonic() - started) * 1000.0
            return RelationPathResult(solved, stats)
    initial = tuple(terms)
    if not initial:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return RelationPathResult(None, stats)
    if not usable_heads:
        stats.elapsed_ms = (time.monotonic() - started) * 1000.0
        return RelationPathResult(None, stats)

    attempted: set[str] = set(expressions)

    def infer(head: RelationHead, arguments: tuple[RelationTerm, ...]) -> str | None:
        if (
            stats.inference_queries >= query_budget
            or time.monotonic() >= deadline
            or len(terms) >= max_terms
        ):
            stats.applications_pruned += 1
            return None
        expression = _application(head, arguments)
        stats.applications_generated += 1
        if expression in attempted or len(expression.encode("utf-8")) > 4096:
            stats.applications_pruned += 1
            return None
        attempted.add(expression)
        inferred = session.infer_type(
            state,
            goal_id=goal.goal_id,
            expression=expression,
        )
        stats.inference_queries += 1
        if inferred is None:
            return None
        stats.terms_inferred += 1
        edge = parse_relation(inferred, expected_operator=target.operator)
        if edge is None:
            return None
        return retain(
            RelationTerm(
                expression,
                inferred,
                edge,
                frozenset().union(*(argument.generators for argument in arguments)),
                1 + sum(argument.node_count for argument in arguments),
            )
        )

    unary_heads = tuple(head for head in usable_heads if head.arity == 1)
    binary_heads = tuple(head for head in usable_heads if head.arity == 2)

    # First observe how the visible declarations act on the local generators.
    unary_terms: list[RelationTerm] = []
    for head in unary_heads:
        before = len(terms)
        for term in initial:
            if (solved := infer(head, (term,))) is not None:
                stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                return RelationPathResult(solved, stats)
        unary_terms.extend(terms[before:])
    for head in binary_heads:
        for left in initial:
            for right in initial:
                if (solved := infer(head, (left, right))) is not None:
                    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                    return RelationPathResult(solved, stats)

    # Congruence-like operators become visible from pairs of useful unary
    # observations.  Endpoint overlap and generator coverage bound the cross
    # product; Agda remains the only applicability test.
    generator_names = frozenset(term.expression for term in initial)
    ranked_unary = tuple(
        sorted(
            (*initial, *unary_terms),
            key=lambda term: (
                -len(term.generators),
                0
                if _endpoint_key(term.edge.left) in generator_names
                or _endpoint_key(term.edge.right) in generator_names
                else 1,
                -_endpoint_overlap(term.edge, target),
                term.node_count,
                term.expression,
            ),
        )[:12]
    )
    second_layer: list[RelationTerm] = []
    observed_boundaries = tuple(
        boundary for term in terms for boundary in term.edge.key
    )

    def bridge_score(pair: tuple[RelationTerm, RelationTerm]) -> int:
        pieces = frozenset((*pair[0].edge.key, *pair[1].edge.key))
        return max(
            (
                sum(1 for piece in pieces if piece and piece in boundary)
                for boundary in observed_boundaries
            ),
            default=0,
        )

    unordered_pairs = sorted(
        (
            (ranked_unary[left], ranked_unary[right])
            for left in range(len(ranked_unary))
            for right in range(left, len(ranked_unary))
        ),
        key=lambda pair: (
            -len(pair[0].generators | pair[1].generators),
            -bridge_score(pair),
            0
            if _endpoint_key(pair[0].edge.left) in generator_names
            or _endpoint_key(pair[0].edge.right) in generator_names
            else 1,
            0
            if _endpoint_key(pair[1].edge.left) in generator_names
            or _endpoint_key(pair[1].edge.right) in generator_names
            else 1,
            -(
                _endpoint_overlap(pair[0].edge, target)
                + _endpoint_overlap(pair[1].edge, target)
            ),
            pair[0].node_count + pair[1].node_count,
            pair[0].expression,
            pair[1].expression,
        ),
    )
    pair_candidates = tuple(
        oriented
        for left, right in unordered_pairs
        for oriented in (
            ((left, right),)
            if left.expression == right.expression
            else ((left, right), (right, left))
        )
    )
    before_second = len(terms)
    second_layer_stop = min(query_budget, stats.inference_queries + 48)
    for left, right in pair_candidates:
        for head in binary_heads:
            if (solved := infer(head, (left, right))) is not None:
                stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                return RelationPathResult(solved, stats)
            if stats.inference_queries >= second_layer_stop or len(terms) >= max_terms:
                break
        if stats.inference_queries >= second_layer_stop or len(terms) >= max_terms:
            break
    second_layer.extend(terms[before_second:])

    # Unary operations can reverse or otherwise transform the edges just
    # discovered.  Their meaning is learned solely from the inferred type.
    ranked_second = tuple(
        sorted(
            second_layer,
            key=lambda term: (
                0
                if target.key[0] in term.edge.key or target.key[1] in term.edge.key
                else 1,
                -_endpoint_overlap(term.edge, target),
                term.node_count,
                term.expression,
            ),
        )[:6]
    )
    for term in ranked_second:
        for head in unary_heads:
            if (solved := infer(head, (term,))) is not None:
                stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                return RelationPathResult(solved, stats)

    # Saturate only composable edges.  This is the small-category/path-algebra
    # core: binary declarations are proposed at matching boundaries, their
    # inferred result decides whether they really are composition-like.
    for _round in range(3):
        stats.composition_rounds += 1
        round_stop = min(query_budget, stats.inference_queries + 24)
        snapshot = tuple(terms)
        composable = [
            (left, right)
            for left in snapshot
            for right in snapshot
            if left.edge.key[1] == right.edge.key[0]
        ]
        composable.sort(
            key=lambda pair: (
                0 if pair[0].edge.key[0] == target.key[0] else 1,
                0 if pair[1].edge.key[1] == target.key[1] else 1,
                pair[0].node_count + pair[1].node_count,
                pair[0].expression,
                pair[1].expression,
            )
        )
        before_round = len(terms)
        for left, right in composable:
            for head in binary_heads:
                if (solved := infer(head, (left, right))) is not None:
                    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
                    return RelationPathResult(solved, stats)
                if stats.inference_queries >= round_stop or len(terms) >= max_terms:
                    break
            if stats.inference_queries >= round_stop or len(terms) >= max_terms:
                break
        if len(terms) == before_round:
            break

    stats.elapsed_ms = (time.monotonic() - started) * 1000.0
    return RelationPathResult(None, stats)


__all__ = [
    "RelationHead",
    "RelationPathResult",
    "RelationPathStats",
    "RelationTerm",
    "RelationView",
    "explicit_arity",
    "mixfix_binary_operator",
    "parse_relation",
    "solve_relation_path",
]
