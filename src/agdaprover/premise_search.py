"""Datatype-neutral ranking of kernel-visible declaration refinements.

Agda supplies the scope catalogue and remains responsible for every implicit
argument, unification constraint, generated subgoal, and final type judgment.
This module only bounds, filters, orders, and serializes possible declaration
heads. It does not recognize any logical connective or datatype.
"""

from __future__ import annotations

import heapq
import itertools
import re
from collections.abc import Iterable
from dataclasses import dataclass, replace
from functools import cache
from typing import Any

from .contracts import GoalInfo
from .notation import (
    binary_mixfix_head,
    render_application,
    render_declaration_head,
    strip_outer_parentheses,
)
from .relation_path import parse_relation
from .retrieval import RetrievalResult, ScopedPremises
from .surface_matching import SurfaceTerm, match_surface, substitute_surface
from .type_syntax import (
    DEFAULT_UNIVERSE_NAMES,
    binder_domain,
    binder_domains,
    has_universe_codomain,
    is_universe_head,
    normalize_type_text,
    parse_named_binder,
    result_head,
    split_adjacent_binders,
    split_top_level_arrows,
    strip_outer_delimiters,
    syntax_scan_batch,
    top_level_arrow_count,
)

PREMISE_ACTION_SCHEMA = "agdaprover.scope-premise-action.v2"
LIVE_PREMISE_ACTION_SCHEMA = "agdaprover.scope-premise-action.v3"
DEFAULT_SCOPE_PREMISE_LIMIT = 64
_RESULT_MATCH_STEP_LIMIT = 4096

# Agda identifiers may freely mix letters and operator characters (for
# example ``_+A_`` or ``_*Carrier_``).  Split only on syntax delimiters and
# whitespace; dividing at the Unicode word/non-word boundary corrupts such
# names and later renders ill-scoped premise applications.
_TOKEN = re.compile(r"[^\s()\[\]{}:;,→λ∀⦃⦄]+|[()\[\]{}:;,→λ∀⦃⦄]", re.UNICODE)
_PLAIN_NAME = re.compile(r"[\w′₀-₉⁰-⁹-]+(?:\.[\w′₀-₉⁰-⁹-]+)*", re.UNICODE)
_INTERNAL_META = re.compile(r"_[^\s(){}]+_\d+")


def _top_level_terms(text: str) -> tuple[str, ...]:
    """Split whitespace-separated terms without crossing delimiters."""

    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closing = frozenset(pairs.values())
    stack: list[str] = []
    terms: list[str] = []
    start: int | None = None
    for index, character in enumerate(text.strip()):
        if character in pairs:
            stack.append(pairs[character])
        elif character in closing and stack and stack[-1] == character:
            stack.pop()
        if character.isspace() and not stack:
            if start is not None:
                terms.append(text.strip()[start:index])
                start = None
        elif start is None:
            start = index
    stripped = text.strip()
    if start is not None:
        terms.append(stripped[start:])
    return tuple(terms)


def _observed_application_arities(
    expressions: tuple[str, ...],
) -> dict[str, int]:
    """Recover the largest surface arity at which each head occurs."""

    observed: dict[str, int] = {}

    def retain(head: str, arity: int) -> None:
        if head:
            observed[head] = max(arity, observed.get(head, 0))

    def visit(expression: str) -> None:
        stripped = strip_outer_parentheses(expression)
        terms = _top_level_terms(stripped)
        if not terms:
            return
        operator_positions = tuple(
            index
            for index, term in enumerate(terms[1:-1], start=1)
            if _PLAIN_NAME.fullmatch(term) is None
            and "_" not in term
            and not any(character in term for character in "()[]{}")
        )
        if len(operator_positions) == 1:
            position = operator_positions[0]
            operator = terms[position]
            retain(operator, 2)
            try:
                retain(binary_mixfix_head(operator), 2)
            except ValueError:
                pass
            visit(" ".join(terms[:position]))
            visit(" ".join(terms[position + 1 :]))
            return
        if len(terms) > 1:
            retain(strip_outer_parentheses(terms[0]), len(terms) - 1)
        for term in terms:
            nested = strip_outer_parentheses(term)
            if nested != stripped and (
                " " in nested or any(character in nested for character in "()")
            ):
                visit(nested)

    for expression in expressions:
        visit(expression)
    return observed


def _shared_mixfix_result_binding(
    goal: GoalInfo,
    action: ScopePremiseAction,
) -> dict[str, SurfaceTerm] | None:
    """Bind a repeated result head from a shared binary surface operator."""

    binders = _binder_names(action.type_text)
    result = _expression_tokens(_result_type(action.type_text))
    repeated = tuple(name for name in binders if result.count(name) >= 2)
    if not repeated:
        return None
    fixed = tuple(token for token in result if token not in binders)
    target_terms = _top_level_terms(goal.target)
    separators = tuple(
        (index, token) for index, token in enumerate(target_terms) if token in fixed
    )
    if len(separators) != 1:
        return None
    separator, _relation = separators[0]
    left = target_terms[:separator]
    right = target_terms[separator + 1 :]
    shared_operators = tuple(
        token
        for token in left[1:-1]
        if left.count(token) == 1
        and right.count(token) == 1
        and token in right[1:-1]
        and _PLAIN_NAME.fullmatch(token) is None
        and "_" not in token
    )
    if len(shared_operators) != 1:
        return None
    try:
        operation = binary_mixfix_head(shared_operators[0])
    except ValueError:
        return None
    return {repeated[0]: SurfaceTerm(operation)}


@dataclass(frozen=True)
class ScopePremiseAction:
    """Refine a goal with one declaration already authorized by Agda scope."""

    name: str
    type_text: str
    expression: str
    module_scope_id: str | None = None
    schema_version: str = PREMISE_ACTION_SCHEMA
    scope_authority: str = "agda-module-contents"

    def __post_init__(self) -> None:
        if (self.schema_version, self.scope_authority) not in (
            (PREMISE_ACTION_SCHEMA, "agda-module-contents"),
            (LIVE_PREMISE_ACTION_SCHEMA, "agda-interaction-meta-closure"),
        ):
            raise ValueError("unsupported scope-premise action schema")
        if (
            self.schema_version == LIVE_PREMISE_ACTION_SCHEMA
            and self.module_scope_id is None
        ):
            raise ValueError("live premise requires its exact scope identity")
        if (
            not self.name
            or not self.type_text
            or not self.expression
            or len(self.name.encode()) > 4096
            or len(self.type_text.encode()) > (1 << 20)
            or any(character.isspace() for character in self.name)
            or any(character in '(){}[];"' for character in self.name)
        ):
            raise ValueError("malformed or over-budget scope premise")
        if self.module_scope_id is not None and not (
            len(self.module_scope_id) == 64
            and all(
                character in "0123456789abcdef" for character in self.module_scope_id
            )
        ):
            raise ValueError("scope premise module identity must be SHA-256")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "tag": "refine-visible-declaration",
            "name": self.name,
            "type": self.type_text,
            "expression": self.expression,
            "scope_authority": self.scope_authority,
            "module_scope_id": self.module_scope_id,
            "elaboration": "agda-refine",
        }

    @classmethod
    def from_dict(cls, value: dict[str, Any]) -> ScopePremiseAction:
        if set(value) != {
            "schema_version",
            "tag",
            "name",
            "type",
            "expression",
            "scope_authority",
            "module_scope_id",
            "elaboration",
        }:
            raise ValueError("malformed scope-premise action fields")
        if value.get("schema_version") not in (
            PREMISE_ACTION_SCHEMA,
            LIVE_PREMISE_ACTION_SCHEMA,
        ):
            raise ValueError("unsupported scope-premise action schema")
        if value.get("tag") != "refine-visible-declaration":
            raise ValueError("unsupported scope-premise action tag")
        if value.get("scope_authority") not in (
            "agda-module-contents",
            "agda-interaction-meta-closure",
        ):
            raise ValueError("scope premise lacks Agda scope authority")
        if value.get("elaboration") != "agda-refine":
            raise ValueError("unsupported scope-premise elaboration")
        name = value.get("name")
        type_text = value.get("type")
        expression = value.get("expression")
        module_scope_id = value.get("module_scope_id")
        if (
            not isinstance(name, str)
            or not isinstance(type_text, str)
            or not isinstance(expression, str)
            or (module_scope_id is not None and not isinstance(module_scope_id, str))
        ):
            raise ValueError("scope-premise action fields must be text")
        if expression != _render_head(name):
            raise ValueError("scope-premise expression does not match its scoped name")
        return cls(
            name=name,
            type_text=type_text,
            expression=expression,
            module_scope_id=module_scope_id,
            schema_version=value["schema_version"],
            scope_authority=value["scope_authority"],
        )


def scoped_premise_actions(
    scoped: ScopedPremises, ranked: RetrievalResult
) -> tuple[ScopePremiseAction, ...]:
    """Convert only this exact checked scope's ranking to ordinary Agda actions.

    No type applicability is asserted. Agda elaborates even a matching head.
    The shortest representable legal alias is selected deterministically.
    """
    if (
        ranked.scope_id != scoped.allowed.scope_id
        or ranked.index_id != scoped.index_id
        or ranked.query_id != scoped.query_id
    ):
        raise ValueError("retrieved actions belong to a different state/index/query")
    types = dict(scoped.type_views)
    members = {p.declaration_id: p for p in scoped.allowed.premises}
    actions = []
    for item in ranked.items:
        premise = item.premise
        if members.get(premise.declaration_id) != premise:
            raise ValueError("retrieved action is not in the allowed set")
        for alias in sorted(premise.aliases, key=lambda a: (len(a), a)):
            try:
                action = ScopePremiseAction(
                    alias,
                    normalize_type_text(types[premise.declaration_id]),
                    _render_head(alias),
                    scoped.allowed.scope_id,
                    LIVE_PREMISE_ACTION_SCHEMA,
                    "agda-interaction-meta-closure",
                )
            except ValueError:
                continue
            actions.append(action)
            break
    return tuple(actions)


def _tokens(text: str) -> frozenset[str]:
    return frozenset(_TOKEN.findall(normalize_type_text(text)))


@syntax_scan_batch()
def scoped_premise_admission(
    goal: GoalInfo,
    ranked: RetrievalResult,
    entries: tuple[tuple[int, ScopePremiseAction], ...],
) -> tuple[int, ...]:
    """Order the pinned retrieval pool for progressive structural search.

    Retrieval bounds membership; this second, proposal-only key preserves the
    existing structural search's preference for directly supported or simple
    applications before truncating to a small batch. A known matching result
    head precedes unknown/different heads, which remain available on widening.
    Neither component is a unification or impossibility judgment.

    Return original one-based retrieval ranks, including unrenderable members
    at the end. Thus admission never expands scope, loses a ranked identity or
    confuses the structural admission position with the retrieval score.
    """
    keys: dict[int, tuple[object, ...]] = {}
    for rank, action in entries:
        if not 1 <= rank <= len(ranked.items):
            raise ValueError("scoped action rank is outside the retrieved pool")
        key = (
            0,
            -ranked.items[rank - 1].head_match,
            *premise_static_priority(goal, action),
            rank,
        )
        if rank not in keys or key < keys[rank]:
            keys[rank] = key
    return tuple(
        sorted(
            range(1, len(ranked.items) + 1),
            key=lambda rank: keys.get(rank, (1, rank)),
        )
    )


def _render_head(name: str) -> str:
    """Render a declaration as an Agda prefix expression."""

    return render_declaration_head(name)


def _result_type(type_text: str) -> str:
    try:
        return strip_outer_delimiters(split_top_level_arrows(type_text)[-1])
    except ValueError:
        return type_text


def premise_result_overlap(goal: GoalInfo, action: ScopePremiseAction) -> int:
    """Count generic result-symbol overlap for transition ordering."""

    return len(_tokens(goal.target) & _tokens(_result_type(action.type_text)))


def _binder_names(type_text: str) -> frozenset[str]:
    """Collect displayed telescope names without assigning them semantics."""

    names: set[str] = set()
    try:
        domains = split_top_level_arrows(type_text)[:-1]
    except ValueError:
        return frozenset()
    for domain in domains:
        groups = split_adjacent_binders(domain) or (domain,)
        for group in groups:
            try:
                binder = parse_named_binder(group)
            except ValueError:
                continue
            if binder is None:
                continue
            names.update(binder.names)
    return frozenset(names)


def _type_binder_names(
    type_text: str, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> frozenset[str]:
    """Collect telescope variables whose codomain is a universe."""

    names: set[str] = set()
    try:
        domains = split_top_level_arrows(type_text)[:-1]
    except ValueError:
        return frozenset()
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            try:
                binder = parse_named_binder(group)
            except ValueError:
                continue
            if binder is None:
                continue
            codomain = normalize_type_text(_result_type(binder.domain))
            if has_universe_codomain(codomain, universe_names):
                names.update(binder.names)
    return frozenset(names)


def _expression_tokens(text: str) -> tuple[str, ...]:
    """Lossy shape features for ranking only; never render these as terms."""
    try:
        surface = strip_outer_delimiters(text)
    except ValueError:
        # Scope pretty-printing can contain syntax outside this deliberately
        # small surface parser.  Ranking is heuristic, so retain raw tokens
        # and leave acceptance to Agda instead of rejecting the whole task.
        surface = text
    return tuple(
        token
        for token in _TOKEN.findall(surface)
        if token not in {"(", ")", "{", "}", "[", "]"}
    )


def _ordered_overlap(left: tuple[str, ...], right: tuple[str, ...]) -> int:
    """Return the longest common subsequence length for two small skeletons."""

    previous = [0] * (len(right) + 1)
    for left_token in left:
        current = [0]
        for index, right_token in enumerate(right, start=1):
            current.append(
                previous[index - 1] + 1
                if left_token == right_token
                else max(previous[index], current[-1])
            )
        previous = current
    return previous[-1]


def _glob_matches(pattern: tuple[str, ...], target: tuple[str, ...]) -> bool:
    """Match a declaration skeleton where telescope variables are wildcards."""

    @cache
    def visit(pattern_index: int, target_index: int) -> bool:
        if pattern_index == len(pattern):
            return target_index == len(target)
        token = pattern[pattern_index]
        if token == "*":
            return any(
                visit(pattern_index + 1, next_index)
                for next_index in range(target_index + 1, len(target) + 1)
            )
        return bool(
            target_index < len(target)
            and token == target[target_index]
            and visit(pattern_index + 1, target_index + 1)
        )

    return visit(0, 0)


def premise_result_matches(goal: GoalInfo, action: ScopePremiseAction) -> bool:
    """Whether a declaration's result pattern covers the complete goal shape."""

    binders = _binder_names(action.type_text)
    pattern: list[str] = []
    for token in _expression_tokens(_result_type(action.type_text)):
        rendered = "*" if token in binders else token
        if not pattern or rendered != "*" or pattern[-1] != "*":
            pattern.append(rendered)
    return _glob_matches(tuple(pattern), _expression_tokens(goal.target))


def _result_bindings(
    goal: GoalInfo, action: ScopePremiseAction
) -> dict[str, SurfaceTerm] | None:
    """Match a result while retaining telescope-variable substitutions."""

    variables = _binder_names(action.type_text)
    function_variables: set[str] = set()
    try:
        telescope = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        telescope = ()
    for part in telescope:
        for group in split_adjacent_binders(part) or (part,):
            parsed = parse_named_binder(group)
            if (
                parsed is not None
                and top_level_arrow_count(parsed.domain)
                and parsed.visibility in {"explicit", "implicit", "instance"}
            ):
                function_variables.update(parsed.names)
    return match_surface(
        _result_type(action.type_text),
        goal.target,
        variables,
        longest_first=frozenset(function_variables),
        step_limit=_RESULT_MATCH_STEP_LIMIT,
    )


def _shape_bindings(
    pattern: tuple[str, ...],
    target: tuple[str, ...],
    variables: frozenset[str],
) -> dict[str, tuple[str, ...]] | None:
    """Approximate type-shape compatibility; bindings are not proof source."""

    if len(pattern) > 128 or len(target) > 128:
        return None
    steps = 0

    def visit(
        pattern_index: int,
        target_index: int,
        bindings: dict[str, tuple[str, ...]],
    ) -> dict[str, tuple[str, ...]] | None:
        nonlocal steps
        steps += 1
        if steps > _RESULT_MATCH_STEP_LIMIT:
            return None
        if pattern_index == len(pattern):
            return bindings if target_index == len(target) else None
        token = pattern[pattern_index]
        if token not in variables:
            if target_index >= len(target) or target[target_index] != token:
                return None
            return visit(pattern_index + 1, target_index + 1, bindings)
        previous = bindings.get(token)
        if previous is not None:
            end = target_index + len(previous)
            if target[target_index:end] != previous:
                return None
            return visit(pattern_index + 1, end, bindings)
        for end in range(target_index + 1, len(target) + 1):
            matched = visit(
                pattern_index + 1,
                end,
                {**bindings, token: target[target_index:end]},
            )
            if matched is not None:
                return matched
        return None

    return visit(0, 0, {})


def _application_from_bindings(
    action: ScopePremiseAction,
    bindings: dict[str, SurfaceTerm],
) -> str | None:
    """Render a complete explicit application from matched result variables."""

    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return None
    arguments: list[str] = []
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is not None:
                if parsed.visibility != "explicit":
                    continue
                for name in parsed.names:
                    value = bindings.get(name)
                    if value is None:
                        return None
                    arguments.append(value.text)
            elif not group.lstrip().startswith(("{", "⦃")):
                return None
    if not arguments:
        return None
    return render_application(action.expression, arguments)


def premise_relation_endpoint_applications(
    action: ScopePremiseAction,
    *,
    relation_operator: str,
    endpoints: tuple[str, ...],
) -> tuple[str, ...]:
    """Instantiate a relation theorem from either known endpoint.

    A law used in the middle of a proof chain usually shares only one endpoint
    with the current obligation.  Matching that endpoint can nevertheless fix
    every explicit parameter of the law.  This routine performs only bounded
    first-order surface matching; callers must infer and validate every
    proposed application with Agda.
    """

    variables = _binder_names(action.type_text)
    result = parse_relation(
        _result_type(action.type_text),
        expected_operator=relation_operator,
        allowed_operators=frozenset({relation_operator}),
    )
    if result is None:
        return ()
    applications: list[str] = []
    for endpoint in endpoints:
        for pattern in (result.left, result.right):
            bindings = match_surface(pattern, endpoint, variables)
            if bindings is None:
                continue
            application = _application_from_bindings(action, bindings)
            if application is not None:
                applications.append(application)
    return tuple(dict.fromkeys(applications))


def premise_relation_ground_applications(
    action: ScopePremiseAction,
    *,
    relation_operator: str,
    endpoints: tuple[str, ...],
    arguments: tuple[str, ...],
    max_applications: int = 12,
) -> tuple[str, ...]:
    """Ground a small relation law over live carrier terms.

    Surface endpoint matching cannot see reductions that occur only after a
    missing argument is supplied.  This finite fallback instantiates at most
    three explicit binders from locals and visible nullary inhabitants, ranks
    the resulting relation skeletons by endpoint overlap, and leaves all type
    inference and acceptance to Agda.
    """

    if max_applications <= 0 or not arguments:
        return ()
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return ()
    binders: list[str] = []
    binder_domains: list[str] = []
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is not None and parsed.visibility == "explicit":
                binders.extend(parsed.names)
                binder_domains.extend(
                    normalize_type_text(parsed.domain) for _name in parsed.names
                )
            elif parsed is None and not group.lstrip().startswith(("{", "⦃")):
                return ()
    if not 1 <= len(binders) <= 3:
        return ()
    # ARGUMENTS is an intentionally untyped pool of live carrier terms.  A
    # Cartesian grounding is therefore meaningful only for a homogeneous
    # explicit telescope.  Heterogeneous declarations (constructor
    # computation laws and dependent eliminators in particular) remain
    # available through result-determined endpoint matching, which recovers
    # their correctly typed arguments instead of speculating across domains.
    if len(set(binder_domains)) != 1:
        return ()
    try:
        result = split_top_level_arrows(action.type_text)[-1]
    except ValueError:
        return ()
    relation = parse_relation(result, expected_operator=relation_operator)
    if relation is None:
        return ()
    endpoint_tokens = tuple(_expression_tokens(endpoint) for endpoint in endpoints)
    unique_arguments = tuple(dict.fromkeys(arguments))

    # Preserve the order in which live arguments occur at each endpoint.
    # Aggregate overlap alone can let the larger endpoint monopolize every
    # candidate, even when a law becomes useful after its last parameter is a
    # visible nullary inhabitant.  These terms are only proposals: Agda still
    # infers and validates each application.
    resident_orders: list[tuple[str, ...]] = []
    for endpoint in endpoint_tokens:
        positions: list[tuple[int, str]] = []
        for argument in unique_arguments:
            tokens = _expression_tokens(argument)
            if not tokens or len(tokens) > len(endpoint):
                continue
            position = next(
                (
                    index
                    for index in range(len(endpoint) - len(tokens) + 1)
                    if endpoint[index : index + len(tokens)] == tokens
                ),
                None,
            )
            if position is not None:
                positions.append((position, argument))
        order = tuple(argument for _position, argument in sorted(positions))
        if order and order not in resident_orders:
            resident_orders.append(order)
    residents = frozenset(argument for order in resident_orders for argument in order)
    bridge_arguments = tuple(
        argument for argument in unique_arguments if argument not in residents
    )
    guided: list[str] = []
    complete_resident_guided: list[str] = []
    fallback_guided: list[str] = []
    one_hole_orders: list[tuple[list[str], tuple[int, ...]]] = []
    for order in resident_orders:
        values = list(order[: len(binders)])
        if len(values) == len(binders):
            complete_resident_guided.append(
                render_application(action.expression, tuple(values))
            )
            continue
        if len(values) + 1 == len(binders) and bridge_arguments:
            # A theorem that bridges two resident endpoint terms often has
            # one distinguished constant or parameter between them.  Preserve
            # their observed order and try interior insertion before either
            # edge.  This finds the missing argument without permuting the
            # resident terms or widening the kernel-query budget.
            interior = tuple(range(1, len(values)))
            # A compound resident commonly denotes the recursive child and
            # leaves an algebraic unit between the outer carrier and that
            # child.  Atomic residents more often follow the theorem's
            # telescope directly, so preserve the established append-first
            # ordering for that case.
            compound_resident = any(
                len(_expression_tokens(value)) > 1 for value in values
            )
            insertion_positions = (
                (*interior, 0, len(values))
                if compound_resident
                else (len(values), *interior, 0)
            )
            one_hole_orders.append((values, insertion_positions))
            continue
        for fill_index in range(max(1, len(bridge_arguments))):
            filled = values.copy()
            while len(filled) < len(binders):
                pool = bridge_arguments or unique_arguments
                if not pool:
                    break
                filled.append(pool[min(fill_index, len(pool) - 1)])
            if len(filled) == len(binders):
                fallback_guided.append(
                    render_application(action.expression, tuple(filled))
                )

    # For each live bridge, interleave endpoint orders before trying a
    # different insertion shape.  Keeping the bridge outermost makes the
    # bounded prefix cover both telescope-preserving and interior placements
    # of the most relevant nullary inhabitant.  This is important when two
    # laws use the same unit on opposite sides of a recursive child.  For
    # atomic residents the telescope-preserving append position comes first;
    # compound residents retain the interior-bridge preference used by
    # W-like constructor fields.
    maximum_positions = max(
        (len(positions) for _values, positions in one_hole_orders),
        default=0,
    )
    for bridge in bridge_arguments:
        # Tile two endpoint orientations with all insertion shapes before
        # moving to resident orders discovered through later inferred edges.
        # This retains endpoint diversity without allowing incidental terms
        # from a growing proof component to postpone the alternate telescope
        # position beyond the bounded prefix.
        for order_start in range(0, len(one_hole_orders), 2):
            order_group = one_hole_orders[order_start : order_start + 2]
            for position_index in range(maximum_positions):
                for values, insertion_positions in order_group:
                    if position_index >= len(insertion_positions):
                        continue
                    inserted = values.copy()
                    inserted.insert(insertion_positions[position_index], bridge)
                    guided.append(
                        render_application(action.expression, tuple(inserted))
                    )
    # A complete resident tuple may combine incidental terms exposed by a
    # previously inferred edge.  Prefer the deliberate one-hole bridge
    # proposals, which retain two terms from the original proof component and
    # introduce exactly one live inhabitant.  Complete resident applications
    # remain in the same bounded candidate stream immediately afterwards.
    guided.extend(complete_resident_guided)
    guided.extend(fallback_guided)

    ranked: list[tuple[tuple[int, int, int, int, str], str]] = []
    for product_values in itertools.product(unique_arguments, repeat=len(binders)):
        mapping = dict(zip(binders, product_values, strict=True))

        def instantiate(
            expression: str, substitutions: dict[str, str] = mapping
        ) -> str:
            rendered = expression
            for name in sorted(substitutions, key=len, reverse=True):
                rendered = re.sub(
                    rf"(?<![\w′₀-₉⁰-⁹-]){re.escape(name)}"
                    rf"(?![\w′₀-₉⁰-⁹-])",
                    substitutions[name],
                    rendered,
                )
            return rendered

        instantiated = (instantiate(relation.left), instantiate(relation.right))
        overlaps = tuple(
            max(
                (
                    _ordered_overlap(_expression_tokens(candidate), endpoint)
                    for candidate in instantiated
                ),
                default=0,
            )
            for endpoint in endpoint_tokens
        )
        score = max(
            (
                _ordered_overlap(_expression_tokens(candidate), endpoint)
                for candidate in instantiated
                for endpoint in endpoint_tokens
            ),
            default=0,
        )
        balanced_score = sum(overlaps)
        exact = max(
            (
                int(normalize_type_text(candidate) in normalize_type_text(endpoint))
                for candidate in instantiated
                for endpoint in endpoints
            ),
            default=0,
        )
        application = render_application(action.expression, product_values)
        repeated = len(product_values) - len(set(product_values))
        ranked.append(
            (
                (-exact, -balanced_score, repeated, -score, application),
                application,
            )
        )
    ordered = (
        *guided,
        *(
            application
            for _key, application in heapq.nsmallest(
                max_applications,
                ranked,
                key=lambda item: item[0],
            )
        ),
    )
    return tuple(dict.fromkeys(ordered))[:max_applications]


def premise_relation_evidence_applications(
    action: ScopePremiseAction,
    *,
    relation_operator: str,
    term_arguments: tuple[str, ...],
    evidence_arguments: tuple[str, ...],
    evidence_types: tuple[str, ...] = (),
    endpoint_contexts: tuple[str, ...] = (),
    max_applications: int = 16,
) -> tuple[str, ...]:
    """Apply one relation-valued declaration to terms and explicit evidence.

    This is the proof-relevant counterpart of ground application.  A visible
    declaration may consume an inhabitant of the live relation (for example a
    generic congruence principle) before producing another inhabitant.  The
    displayed domains decide which finite pool is used; Agda infers all hidden
    parameters and validates every proposal.  No relation, datatype, or
    declaration name is assigned a special role.
    """

    if max_applications <= 0:
        return ()
    try:
        parts = split_top_level_arrows(action.type_text)
    except ValueError:
        return ()
    if parse_relation(parts[-1], expected_operator=relation_operator) is None:
        return ()
    domains: list[str] = []
    for part in parts[:-1]:
        for group in split_adjacent_binders(part) or (part,):
            parsed = parse_named_binder(group)
            if parsed is not None:
                if parsed.visibility == "explicit":
                    domains.extend((parsed.domain,) * len(parsed.names))
                continue
            if group.lstrip().startswith(("{", "⦃")):
                continue
            try:
                domains.append(binder_domain(group))
            except ValueError:
                return ()
    if not 1 <= len(domains) <= 3:
        return ()
    terms = tuple(dict.fromkeys(term_arguments))[:16]
    # Keep the complete bounded evidence layer available while ranking pairs.
    # Derived congruence edges can easily outnumber the recursive hypotheses;
    # truncating before contextual ranking then makes the useful induction
    # evidence disappear merely because it was discovered earlier.  The
    # caller already bounds this layer, and only ``max_applications`` terms
    # are returned to the kernel.
    evidence = tuple(dict.fromkeys(evidence_arguments))[:48]
    pools: list[tuple[str, ...]] = []
    for domain in domains:
        if parse_relation(domain, expected_operator=relation_operator) is not None:
            pool = evidence
        elif top_level_arrow_count(domain):
            # Callers provide endpoint subterms in preorder.  Keeping that
            # order prioritizes the actual surrounding function contexts over
            # unrelated short identifiers.  Atomic heads precede compound
            # endpoint terms, which cannot usually inhabit a function domain.
            # Inference still rejects locals that have the wrong function
            # type.
            surface_functions = tuple(
                (
                    *(term for term in terms if not _top_level_terms(term)[1:]),
                    *(term for term in terms if _top_level_terms(term)[1:]),
                )
            )

            def prefix_function(term: str) -> str:
                if (
                    len(_top_level_terms(term)) == 1
                    and _PLAIN_NAME.fullmatch(term) is None
                    and "_" not in term
                ):
                    try:
                        return binary_mixfix_head(term)
                    except ValueError:
                        pass
                return term

            ordered_functions = tuple(
                dict.fromkeys(prefix_function(term) for term in surface_functions)
            )
            normalized_contexts = tuple(
                normalize_type_text(context) for context in endpoint_contexts
            )

            def contextual_score(
                function: str,
                contexts: tuple[str, ...] = normalized_contexts,
            ) -> int:
                score = 0
                for type_text in evidence_types:
                    edge = parse_relation(
                        type_text, expected_operator=relation_operator
                    )
                    if edge is None:
                        continue
                    for endpoint in (edge.left, edge.right):
                        lifted = normalize_type_text(
                            render_application(function, (endpoint,))
                        )
                        score += sum(lifted in context for context in contexts)
                return score

            function_order = {
                function: index for index, function in enumerate(ordered_functions)
            }
            pool = tuple(
                sorted(
                    ordered_functions,
                    key=lambda function: (
                        -contextual_score(function),
                        function_order[function],
                    ),
                )
            )
        else:
            # A term-only relation law used inside a larger endpoint usually
            # applies to a proper application subterm.  Put the smallest such
            # subterms first, while retaining atomic locals as a complete
            # bounded fallback.
            pool = tuple(
                sorted(
                    terms,
                    key=lambda term: (
                        not bool(_top_level_terms(term)[1:]),
                        len(term),
                        term,
                    ),
                )
            )
        if not pool:
            return ()
        pools.append(pool)
    relation_positions = tuple(
        index
        for index, domain in enumerate(domains)
        if parse_relation(domain, expected_operator=relation_operator) is not None
    )
    function_positions = tuple(
        index for index, domain in enumerate(domains) if top_level_arrow_count(domain)
    )
    if (
        len(function_positions) == 1
        and relation_positions
        and len(relation_positions) + 1 == len(domains)
    ):
        function_position = function_positions[0]
        evidence_type_by_expression = dict(
            zip(evidence_arguments, evidence_types, strict=False)
        )
        normalized_contexts = tuple(
            normalize_type_text(context) for context in endpoint_contexts
        )
        observed_arities = _observed_application_arities(endpoint_contexts)
        expected_function_arity = top_level_arrow_count(domains[function_position])
        ranked_pools = list(pools)
        if len(relation_positions) > 1 and len(evidence) > 16:
            ranked_evidence: list[tuple[tuple[int, int, int, int], str]] = []
            for evidence_index, expression in enumerate(evidence):
                edge = parse_relation(
                    evidence_type_by_expression.get(expression, ""),
                    expected_operator=relation_operator,
                )
                exact = 0
                ordered = 0
                shared = 0
                if edge is not None:
                    for endpoint in (edge.left, edge.right):
                        normalized = normalize_type_text(endpoint)
                        exact += sum(
                            normalized in context for context in normalized_contexts
                        )
                        endpoint_ordered, endpoint_shared = (
                            premise_application_context_score(
                                endpoint,
                                endpoint_contexts=endpoint_contexts,
                            )
                        )
                        ordered += endpoint_ordered
                        shared += endpoint_shared
                ranked_evidence.append(
                    ((-exact, -ordered, -shared, evidence_index), expression)
                )
            selected_evidence = tuple(
                expression
                for _priority, expression in heapq.nsmallest(
                    16,
                    ranked_evidence,
                    key=lambda item: item[0],
                )
            )
            for position in relation_positions:
                ranked_pools[position] = selected_evidence
        ranked: list[tuple[tuple[int, int, int, int, int, int], tuple[str, ...]]] = []
        combination_order = 0
        for arguments in itertools.product(*ranked_pools):
            edges = tuple(
                parse_relation(
                    evidence_type_by_expression.get(arguments[position], ""),
                    expected_operator=relation_operator,
                )
                for position in relation_positions
            )
            exact_hits = 0
            ordered_score = 0
            shared_score = 0
            if all(edge is not None for edge in edges):
                function = arguments[function_position]
                lifted_endpoints = (
                    render_application(
                        function,
                        tuple(
                            getattr(edge, side) for edge in edges if edge is not None
                        ),
                    )
                    for side in ("left", "right")
                )
                for endpoint in lifted_endpoints:
                    lifted = normalize_type_text(endpoint)
                    exact_hits += sum(
                        lifted in context for context in normalized_contexts
                    )
                    ordered, shared = premise_application_context_score(
                        endpoint,
                        endpoint_contexts=endpoint_contexts,
                    )
                    ordered_score += ordered
                    shared_score += shared
            function = arguments[function_position]
            # Atomic declaration heads and operator sections are far more
            # likely to inhabit the displayed function domain than an
            # arbitrary compound endpoint subterm.  Keep compound functions
            # as a bounded fallback for genuine partial applications.
            compound_function = int(bool(_top_level_terms(function)[1:]))
            arity_mismatch = int(
                observed_arities.get(strip_outer_parentheses(function), 0)
                < expected_function_arity
            )
            ranked.append(
                (
                    (
                        compound_function,
                        arity_mismatch,
                        -exact_hits,
                        -ordered_score,
                        -shared_score,
                        combination_order,
                    ),
                    arguments,
                )
            )
            combination_order += 1
        return tuple(
            render_application(action.expression, arguments)
            for _priority, arguments in heapq.nsmallest(
                max_applications, ranked, key=lambda item: item[0]
            )
        )
    return tuple(
        render_application(action.expression, arguments)
        for arguments in itertools.islice(itertools.product(*pools), max_applications)
    )


def premise_application_context_score(
    expression: str,
    *,
    endpoint_contexts: tuple[str, ...],
) -> tuple[int, int]:
    """Measure how much a proposed application occurs in live endpoints.

    This deliberately uses only surface syntax.  It is a cheap, deterministic
    scheduler for a bounded proposal layer; Agda still infers and validates
    every selected application.  Ordered overlap rewards an application whose
    arguments follow a target branch, while token overlap recognizes useful
    subcontexts even when a declaration head is absent from the target.
    """

    candidate = _expression_tokens(expression)
    if not candidate:
        return (0, 0)
    contexts = tuple(_expression_tokens(context) for context in endpoint_contexts)
    ordered = max(
        (_ordered_overlap(candidate, context) for context in contexts),
        default=0,
    )
    candidate_tokens = frozenset(candidate)
    shared = max(
        (len(candidate_tokens.intersection(context)) for context in contexts),
        default=0,
    )
    return (ordered, shared)


def premise_relation_evidence_arity(
    action: ScopePremiseAction, *, relation_operator: str
) -> int | None:
    """Count explicit relation-valued inputs of a relation-valued premise."""

    try:
        parts = split_top_level_arrows(action.type_text)
    except ValueError:
        return None
    if parse_relation(parts[-1], expected_operator=relation_operator) is None:
        return None
    count = 0
    for part in parts[:-1]:
        for group in split_adjacent_binders(part) or (part,):
            parsed = parse_named_binder(group)
            if parsed is not None:
                if (
                    parsed.visibility == "explicit"
                    and parse_relation(
                        parsed.domain, expected_operator=relation_operator
                    )
                    is not None
                ):
                    count += len(parsed.names)
                continue
            if group.lstrip().startswith(("{", "⦃")):
                continue
            try:
                domain = binder_domain(group)
            except ValueError:
                return None
            if parse_relation(domain, expected_operator=relation_operator) is not None:
                count += 1
    return count


def premise_relation_function_arity(
    action: ScopePremiseAction, *, relation_operator: str
) -> int | None:
    """Count displayed function inputs of a relation-valued premise."""

    try:
        parts = split_top_level_arrows(action.type_text)
    except ValueError:
        return None
    if parse_relation(parts[-1], expected_operator=relation_operator) is None:
        return None
    count = 0
    for part in parts[:-1]:
        for group in split_adjacent_binders(part) or (part,):
            parsed = parse_named_binder(group)
            if parsed is not None:
                if parsed.visibility == "explicit" and top_level_arrow_count(
                    parsed.domain
                ):
                    count += len(parsed.names)
                continue
            if group.lstrip().startswith(("{", "⦃")):
                continue
            try:
                domain = binder_domain(group)
            except ValueError:
                return None
            if top_level_arrow_count(domain):
                count += 1
    return count


def premise_reflexive_arguments(goal: GoalInfo, action: ScopePremiseAction) -> int:
    """Count explicit result-instantiated premises of the form ``t R t``."""

    bindings = _result_bindings(goal, action)
    if bindings is None:
        return 0
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return 0
    binder_names = _binder_names(action.type_text)
    count = 0
    for domain in domains:
        groups = split_adjacent_binders(domain) or (domain,)
        for group in groups:
            stripped = group.strip()
            if stripped.startswith(("{", "⦃")):
                continue
            body = stripped
            if stripped.startswith("(") and ":" in stripped:
                body = stripped.split(":", 1)[1].rsplit(")", 1)[0]
            instantiated: list[str] = []
            unresolved = False
            for token in _expression_tokens(body):
                if token in bindings:
                    instantiated.extend(_expression_tokens(bindings[token].text))
                elif token in binder_names:
                    unresolved = True
                    break
                else:
                    instantiated.append(token)
            if unresolved:
                continue
            for split in range(1, len(instantiated) - 1):
                if instantiated[:split] == instantiated[split + 1 :]:
                    count += 1
                    break
    return count


def premise_expected_arguments(
    goal: GoalInfo, action: ScopePremiseAction
) -> tuple[str, ...]:
    """Instantiate explicit premise shapes from a successful result match."""

    bindings = _result_bindings(goal, action)
    if bindings is None:
        return ()
    binders = _binder_names(action.type_text)
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return ()
    expected: list[str] = []
    for domain in domains:
        groups = split_adjacent_binders(domain) or (domain,)
        for group in groups:
            stripped = group.strip()
            if stripped.startswith(("{", "⦃")):
                continue
            body = stripped
            if stripped.startswith("(") and ":" in stripped:
                body = stripped.split(":", 1)[1].rsplit(")", 1)[0]
            if any(
                token in binders and token not in bindings
                for token in _expression_tokens(body)
            ):
                return ()
            rendered = substitute_surface(body, bindings)
            if not rendered:
                return ()
            expected.append(rendered)
    return tuple(expected)


def premise_result_arguments(
    goal: GoalInfo, action: ScopePremiseAction
) -> tuple[str, ...] | None:
    """Recover explicit argument terms fixed by the declaration result.

    This is first-order surface matching only. It is useful when a theorem's
    result contains its explicit argument (for example ``rule t : F t``).
    Missing or unnamed arguments fail closed; Agda still checks the completed
    application before search may use it.
    """

    bindings = _result_bindings(goal, action)
    if bindings is None:
        return None
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return None
    arguments: list[str] = []
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is not None:
                if parsed.visibility != "explicit":
                    continue
                for name in parsed.names:
                    value = bindings.get(name)
                    if value is None:
                        return None
                    arguments.append(value.text)
            elif not group.lstrip().startswith(("{", "⦃")):
                return None
    return tuple(arguments)


def _result_arguments_allowed(
    goal: GoalInfo,
    action: ScopePremiseAction,
    arguments: Iterable[str],
    excluded_names: frozenset[str],
) -> bool:
    """Keep excluded declarations out of terms copied from a result type.

    A dependent result can mention an unfinished definition through its earlier
    projections. That occurrence is not permission to use the whole definition
    as a premise argument. This conservative surface filter mirrors catalogue
    name exclusions; ordinary refinement and explicit recursive actions remain
    separate. It does not establish scope or resolve aliases.
    """
    if not excluded_names:
        return True
    if (
        action.name in excluded_names
        or action.name.rsplit(".", 1)[-1] in excluded_names
    ):
        return False
    # Include the printed spelling of a unary/binary mixfix name. Keep complete
    # identifier tokens: an exclusion of f must not also exclude f₁ or f-tail.
    spellings = excluded_names | frozenset(
        name.rpartition(".")[0] + "." + name.rpartition(".")[2].strip("_")
        if "." in name
        else name.strip("_")
        for name in excluded_names
    )
    locals_in_scope = {entry.name for entry in goal.context if entry.in_scope}
    return not any(
        token not in locals_in_scope
        and (token in spellings or token.rsplit(".", 1)[-1] in spellings)
        for argument in arguments
        # Unlike the type-pattern tokenizer, keep punctuation within names
        # (for example _:::_). This is a name filter, not telescope parsing.
        for token in re.findall(r"[^\s()[\]{}⦃⦄]+", argument)
    )


def premise_result_application(
    goal: GoalInfo,
    action: ScopePremiseAction,
    *,
    excluded_names: frozenset[str] = frozenset(),
) -> str | None:
    """Render a complete application when the result fixes every argument.

    Result matching can mention hidden context entries printed by Agda but not
    accepted as source-level names at the interaction. Those terms are replaced
    by inference placeholders; the kernel remains responsible for reconstructing
    and checking them.
    """

    arguments = premise_result_arguments(goal, action)
    if not arguments or not _result_arguments_allowed(
        goal, action, arguments, excluded_names
    ):
        return None
    inaccessible = tuple(
        entry.name for entry in goal.context if entry.name and not entry.in_scope
    )
    visible_arguments = tuple(
        "_"
        if any(
            re.search(rf"(?<!\w){re.escape(name)}(?!\w)", argument)
            for name in inaccessible
        )
        else argument
        for argument in arguments
    )
    return render_application(action.expression, visible_arguments)


def premise_inferred_application(
    goal: GoalInfo,
    action: ScopePremiseAction,
    *,
    excluded_names: frozenset[str] = frozenset(),
) -> str | None:
    """Render a result-matched application with inferred telescope entries.

    A dependent theorem's conclusion often determines only the first and last
    entries of its telescope.  The intervening entries are nevertheless
    uniquely constrained by their dependent types.  Supplying Agda inference
    placeholders for precisely those entries lets the kernel solve the whole
    application in one transaction instead of making proof search rediscover
    the telescope one goal at a time.  This rule is datatype-neutral and fails
    closed unless the complete declaration result matches the current goal.
    """

    bindings = _result_bindings(goal, action)
    if bindings is None or not _result_arguments_allowed(
        goal, action, (value.text for value in bindings.values()), excluded_names
    ):
        return None
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return None
    inaccessible = tuple(
        entry.name for entry in goal.context if entry.name and not entry.in_scope
    )
    arguments: list[str] = []
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is None:
                if not group.lstrip().startswith(("{", "⦃")):
                    return None
                continue
            if parsed.visibility != "explicit":
                continue
            for name in parsed.names:
                value = bindings.get(name)
                argument = "_" if value is None else value.text
                if any(
                    re.search(rf"(?<!\w){re.escape(hidden)}(?!\w)", argument)
                    for hidden in inaccessible
                ):
                    argument = "_"
                arguments.append(argument)
    if not arguments or "_" not in arguments:
        return None
    return render_application(action.expression, tuple(arguments))


@dataclass(frozen=True)
class ExpectedApplication:
    """A result-determined prefix to check against the whole expected type."""

    expression: str
    arguments: tuple[str, ...]
    remaining_arguments: int


def premise_expected_application(
    goal: GoalInfo,
    action: ScopePremiseAction,
    *,
    excluded_names: frozenset[str] = frozenset(),
) -> ExpectedApplication | None:
    """Recover a complete or partial application without inventing operands.

    Match the codomain and leave the expected function's telescope unapplied.
    Supplied arguments must be fixed by the result, independent of that local
    telescope. Agda checks the residual dependent domains and hidden arguments;
    this surface hint never confers type correctness or closes inferred metas.
    """
    try:
        goal_parts = split_top_level_arrows(goal.target)
        action_parts = split_top_level_arrows(action.type_text)
        remaining = 0
        for part in goal_parts[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder is None:
                    remaining += 1
                elif binder.visibility == "explicit":
                    remaining += len(binder.names)
        operands: list[str | None] = []
        for part in action_parts[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder is None:
                    operands.append(None)
                elif binder.visibility == "explicit":
                    operands.extend(binder.names)
    except ValueError:
        return None
    supplied = len(operands) - remaining
    if supplied <= 0:
        return None
    bindings = _result_bindings(replace(goal, target=goal_parts[-1]), action)
    if bindings is None:
        return None
    arguments: list[str] = []
    future_names = _binder_names(goal.target)
    inaccessible = frozenset(
        entry.name for entry in goal.context if entry.name and not entry.in_scope
    )
    for name in operands[:supplied]:
        if name is None or name not in bindings:
            return None
        value = bindings[name]
        # A prefix cannot mention the arguments of its residual function.
        # Decline instead of moving a term across a binder or capturing it.
        if future_names.intersection(_expression_tokens(value.text)):
            return None
        arguments.append(value.text)
    if not _result_arguments_allowed(goal, action, arguments, excluded_names):
        return None
    visible = tuple(
        "_" if inaccessible.intersection(_expression_tokens(arg)) else arg
        for arg in arguments
    )
    return ExpectedApplication(
        render_application(action.expression, visible), visible, remaining
    )


def _premise_result_prefix(
    goal: GoalInfo,
    action: ScopePremiseAction,
    *,
    excluded_names: frozenset[str] = frozenset(),
) -> tuple[str, bool] | None:
    """Render the longest leading application fixed by the result shape.

    A higher-order rule can have an operation argument followed by proof
    premises, as in ``(f : A -> B -> C) -> ... -> f x y R f x' y'``.  The
    result determines ``f`` even though it cannot determine the later proof
    arguments.  Applying that prefix before refinement preserves the common
    operation selected by the goal and avoids searching arbitrary lambda
    bodies.  This is purely surface matching; Agda validates the application.
    """

    bindings = _result_bindings(goal, action)
    one_sided = False
    if bindings is None:
        bindings = _shared_mixfix_result_binding(goal, action)
        one_sided = bindings is not None
    if bindings is None:
        # A single endpoint metavariable can hide the second occurrence of a
        # higher-order argument.  Match the rigid endpoint alone so
        # ``f rigid R ?m`` may still determine the leading ``f``.  The
        # resulting partial application is only a proposal to Agda.
        fixed_tokens = frozenset(
            _expression_tokens(_result_type(action.type_text))
        ) - _binder_names(action.type_text)
        result_relation = parse_relation(
            _result_type(action.type_text), allowed_operators=fixed_tokens
        )
        target_relation = (
            parse_relation(
                goal.target,
                expected_operator=result_relation.operator,
                allowed_operators=fixed_tokens,
            )
            if result_relation is not None
            else None
        )
        if result_relation is not None and target_relation is not None:
            for pattern, rigid, other in (
                (result_relation.left, target_relation.left, target_relation.right),
                (result_relation.right, target_relation.right, target_relation.left),
            ):
                if _INTERNAL_META.fullmatch(other.strip()):
                    bindings = match_surface(
                        pattern, rigid, _binder_names(action.type_text)
                    )
                    one_sided = bindings is not None
                    if bindings is not None:
                        break
    if bindings is None:
        return None
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        return None
    arguments: list[str] = []
    stopped = False
    for domain in domains:
        for group in split_adjacent_binders(domain) or (domain,):
            parsed = parse_named_binder(group)
            if parsed is None:
                if not group.lstrip().startswith(("{", "⦃")):
                    stopped = True
                    break
                continue
            if parsed.visibility != "explicit":
                continue
            for name in parsed.names:
                value = bindings.get(name)
                if value is None:
                    stopped = True
                    break
                arguments.append(value.text)
            if stopped:
                break
        if stopped:
            break
    if (
        not arguments
        or (not stopped and not one_sided)
        or not _result_arguments_allowed(goal, action, arguments, excluded_names)
    ):
        return None
    return render_application(action.expression, arguments), not stopped


def premise_result_prefix_application(
    goal: GoalInfo,
    action: ScopePremiseAction,
    *,
    excluded_names: frozenset[str] = frozenset(),
) -> str | None:
    """Return a result-determined leading application, when one exists."""

    result = _premise_result_prefix(goal, action, excluded_names=excluded_names)
    return None if result is None else result[0]


def premise_result_prefix_priority(goal: GoalInfo, action: ScopePremiseAction) -> int:
    """Rank complete, partial, and absent result-determined prefixes."""

    result = _premise_result_prefix(goal, action)
    if result is None:
        return 2
    return 0 if result[1] else 1


def premise_result_bindings_consistent(
    goal: GoalInfo, action: ScopePremiseAction
) -> bool:
    """Whether one substitution covers the declaration's complete result."""

    return _result_bindings(goal, action) is not None


def premise_reorients_goal(goal: GoalInfo, action: ScopePremiseAction) -> bool:
    """Whether a unary premise merely reverses one binary obligation.

    Reorientation is never removed: it is essential in many proof chains.  It
    is, however, a poor first recursive move because applying the same premise
    again returns to the parent state.  The structural comparison is entirely
    name- and datatype-independent.
    """

    expected = premise_expected_arguments(goal, action)
    if len(expected) != 1:
        return False
    target = _expression_tokens(goal.target)
    premise = _expression_tokens(expected[0])
    if len(target) != len(premise) or len(target) < 3:
        return False
    for separator in range(1, len(target) - 1):
        token = target[separator]
        if premise.count(token) != 1:
            continue
        premise_separator = premise.index(token)
        if (
            target[:separator] == premise[premise_separator + 1 :]
            and target[separator + 1 :] == premise[:premise_separator]
        ):
            return True
    return False


def premise_flexible_priority(
    goal: GoalInfo, action: ScopePremiseAction
) -> tuple[int, ...] | None:
    """Score a declaration result against a one-sided flexible goal.

    This is a datatype-neutral higher-order unification heuristic.  For
    ``rigid R ?m`` it first prefers a result that introduces little invented
    structure.  For ``?m R rigid`` it prefers a result whose rigid side has
    the same operator skeleton and whose two sides share fewer telescope
    variables.  The latter avoids prematurely constraining an unknown
    intermediate.  Agda still decides applicability and all substitutions.
    """

    target = _expression_tokens(goal.target)
    meta_positions = tuple(
        index for index, token in enumerate(target) if _INTERNAL_META.fullmatch(token)
    )
    if len(meta_positions) != 1 or len(target) < 3:
        return None
    meta_index = meta_positions[0]
    if meta_index == 0:
        separator = target[1]
        rigid = target[2:]
        orientation = "left"
    elif meta_index == len(target) - 1:
        separator = target[-2]
        rigid = target[:-2]
        orientation = "right"
    else:
        return None

    result = _expression_tokens(_result_type(action.type_text))
    separator_positions = tuple(
        index for index, token in enumerate(result) if token == separator
    )
    if len(separator_positions) != 1:
        return None
    split = separator_positions[0]
    left, right = result[:split], result[split + 1 :]
    binders = _binder_names(action.type_text)
    context_names = {entry.name for entry in goal.context if entry.in_scope}

    def skeleton(
        tokens: tuple[str, ...], variables: set[str] | frozenset[str]
    ) -> tuple[str, ...]:
        return tuple(
            token for token in tokens if token not in variables and token not in {"Set"}
        )

    left_skeleton = skeleton(left, binders)
    right_skeleton = skeleton(right, binders)
    rigid_skeleton = skeleton(rigid, context_names)
    shared_variables = len((set(left) & set(right)) & set(binders))
    if orientation == "right":
        exact_rigid_shape = int(
            bool(rigid_skeleton) and left_skeleton == rigid_skeleton
        )
        preserves_outer_shape = int(
            bool(rigid_skeleton) and rigid_skeleton[0] in left_skeleton
        )
        overlap = _ordered_overlap(left_skeleton, rigid_skeleton)
        extraneous = sum(token not in rigid_skeleton for token in left_skeleton)
        return (
            # With a flexible right endpoint, a low-structure orientation
            # change exposes the opposite directed obligation without
            # guessing an intermediate term.  Structured constructors remain
            # available immediately afterwards.
            len(left_skeleton) + len(right_skeleton),
            -exact_rigid_shape,
            -preserves_outer_shape,
            -overlap,
            extraneous,
            -len(right_skeleton),
            shared_variables,
        )
    exact_rigid_shape = int(bool(rigid_skeleton) and right_skeleton == rigid_skeleton)
    preserves_outer_shape = int(
        bool(rigid_skeleton) and rigid_skeleton[0] in right_skeleton
    )
    overlap = _ordered_overlap(right_skeleton, rigid_skeleton)
    result_size = len(left_skeleton) + len(right_skeleton)
    return (
        int(result_size == 0),
        result_size,
        -exact_rigid_shape,
        -preserves_outer_shape,
        -overlap,
        -len(left_skeleton),
        shared_variables,
    )


def premise_static_priority(
    goal: GoalInfo, action: ScopePremiseAction
) -> tuple[object, ...]:
    """Order declaration checks before paying for an Agda refinement query."""

    binders = _binder_names(action.type_text)
    result_tokens = _expression_tokens(_result_type(action.type_text))
    result_structure = sum(
        token not in binders and token != "Set" for token in result_tokens
    )
    bare_result_variable = int(
        bool(result_tokens) and all(token in binders for token in result_tokens)
    )
    try:
        domains = split_top_level_arrows(action.type_text)[:-1]
    except ValueError:
        domains = ()
    rigid_premise_structure = 0
    explicit_premises = 0
    for domain in domains:
        groups = split_adjacent_binders(domain) or (domain,)
        for group in groups:
            stripped = group.strip()
            if stripped.startswith(("{", "⦃")):
                continue
            explicit_premises += 1
            body = stripped
            if stripped.startswith("(") and ":" in stripped:
                body = stripped.split(":", 1)[1].rsplit(")", 1)[0]
            rigid_premise_structure += sum(
                token not in binders and token != "Set"
                for token in _expression_tokens(body)
            )
    flexible = premise_flexible_priority(goal, action)
    if flexible is not None:
        return (
            0,
            *flexible,
            bare_result_variable,
            explicit_premises,
            -rigid_premise_structure,
            result_structure,
            action.name,
        )

    if bare_result_variable and _has_independent_explicit_domain(action.type_text):
        # A declaration whose polymorphic result is supported by an input
        # independent of that result is an eliminator.  It is applicable to a
        # wider class of rigid targets than an unrelated constant, so let Agda
        # check it before enumerating declarations with incompatible heads.
        return (
            1,
            0,
            explicit_premises,
            -rigid_premise_structure,
            result_structure,
            action.name,
        )

    meta_count = len(set(_INTERNAL_META.findall(goal.target)))
    if meta_count >= 2:
        return (
            1,
            bare_result_variable,
            -rigid_premise_structure,
            explicit_premises,
            result_structure,
            action.name,
        )
    # On a rigid target, generic relations and eliminators are cheap probes;
    # highly structured results are retained but checked later.  Recursive
    # constructor search can locally promote a result-determined structural
    # prefix when it has actual induction hypotheses in hand.
    direct_support = premise_reflexive_arguments(goal, action)
    direct = int(premise_result_matches(goal, action) and direct_support > 0)
    return (
        2,
        -direct,
        -direct_support,
        int(premise_reorients_goal(goal, action)),
        bare_result_variable,
        explicit_premises,
        -result_structure if direct else result_structure,
        action.name,
    )


def _is_type_constructor(
    type_text: str, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> bool:
    result = normalize_type_text(_result_type(type_text))
    try:
        return has_universe_codomain(result, universe_names)
    except ValueError:
        # Unsupported scope renderings are not grounds to invalidate a task.
        # This is only a ranking classification; Agda still checks any use.
        return False


def _has_bare_polymorphic_result(type_text: str) -> bool:
    result = _expression_tokens(_result_type(type_text))
    return len(result) == 1 and result[0] in _binder_names(type_text)


def premise_independent_result_domains(type_text: str) -> tuple[str, ...]:
    """Return explicit inputs independent of a bare polymorphic result."""

    result = _expression_tokens(_result_type(type_text))
    if len(result) != 1 or result[0] not in _binder_names(type_text):
        return ()
    result_name = result[0]
    try:
        domains = split_top_level_arrows(type_text)[:-1]
    except ValueError:
        return ()
    try:
        explicit_domains = tuple(
            binder_domain(group)
            for domain in domains
            for group in split_adjacent_binders(domain) or (domain,)
            if not group.lstrip().startswith(("{", "⦃"))
        )
        result_dependent = any(
            result_name in _expression_tokens(domain) for domain in explicit_domains
        )
    except ValueError:
        return ()
    if not explicit_domains or result_dependent:
        return ()
    return explicit_domains


def premise_eliminator_source_domains(
    type_text: str, *, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> tuple[str, ...]:
    """Return concrete source domains of a result-polymorphic eliminator.

    An eliminator may have result-dependent branch arguments while its final
    scrutinee is independent of the result family.  For example, the branch
    functions of a coproduct recursor mention its codomain, but the coproduct
    argument itself does not.  Exposing only non-function source domains lets
    a controller plug in an existing value before asking Agda to infer the
    motive and branch obligations.
    """

    result = _expression_tokens(_result_type(type_text))
    binders = _binder_names(type_text)
    # The result must be the codomain parameter itself.  Merely starting with
    # a parameter is insufficient: constructors such as ``B → A + B`` and
    # dependent eliminators ending in ``C t`` have different search shapes.
    if len(result) != 1 or result[0] not in binders:
        return ()
    result_name = result[0]
    try:
        explicit_domains = tuple(
            binder_domain(group)
            for domain in split_top_level_arrows(type_text)[:-1]
            for group in split_adjacent_binders(domain) or (domain,)
            if not group.lstrip().startswith(("{", "⦃"))
        )
    except ValueError:
        return ()
    source_domains = tuple(
        domain
        for domain in explicit_domains
        if result_name not in _expression_tokens(domain)
        and not top_level_arrow_count(domain)
        and not has_universe_codomain(domain, universe_names)
        and result_head(domain) != "Level"
    )

    def is_nonrecursive_branch(domain: str) -> bool:
        if not top_level_arrow_count(domain):
            return False
        try:
            inputs = split_top_level_arrows(domain)[:-1]
        except ValueError:
            return False
        return not any(
            result_name in _expression_tokens(input_type) for input_type in inputs
        )

    return tuple(
        source
        for source in source_domains
        if all(
            domain == source
            or (
                is_nonrecursive_branch(domain)
                and result_name in _expression_tokens(domain)
            )
            for domain in explicit_domains
        )
    )


def premise_type_pattern_matches(
    type_text: str,
    pattern_type: str,
    concrete_type: str,
) -> bool:
    """Match a telescope-parametric type against a concrete local type.

    Bound telescope names are wildcards, while constructors, type operators,
    and repeated variables remain rigid.  This recognizes both prefix forms
    such as ``List A`` and mixfix forms such as ``A + B`` without assigning
    any datatype-specific meaning to either notation.
    """

    pattern = _expression_tokens(normalize_type_text(pattern_type))
    concrete = _expression_tokens(normalize_type_text(concrete_type))
    if not pattern or not concrete:
        return False
    return (
        _shape_bindings(
            pattern,
            concrete,
            frozenset(_binder_names(type_text)),
        )
        is not None
    )


def premise_has_local_source(
    goal: GoalInfo, type_text: str, source_domains: tuple[str, ...]
) -> bool:
    """Recognize a source already available for an early eliminator attempt.

    This is scheduling evidence, not applicability or a proof of irrelevance.
    A surface mismatch (including an unrecognized alias) must leave ordinary
    premise search available. Bindings are scoped to this goal, never inherited
    from a sibling whose source may have a different type or module instance.
    """

    return any(
        premise_type_pattern_matches(type_text, domain, entry.type)
        for entry in goal.context
        if entry.in_scope
        and entry.name
        and not top_level_arrow_count(entry.type)
        and not has_universe_codomain(entry.type, goal.sort_names)
        and result_head(entry.type) != "Level"
        for domain in source_domains
    )


def premise_function_shape_matches(goal: GoalInfo, action: ScopePremiseAction) -> bool:
    """Propose reusing a supplied function at its complete expected telescope.

    Hidden parameters are left to Agda; matching the explicit domains and
    result together preserves repeated-variable relationships in the proposal.
    This deliberately limited surface check is neither type equality nor a
    reason to prune ordinary introduction when it does not recognize a shape.
    """

    def explicit_core(type_text: str) -> tuple[int, str]:
        parts = split_top_level_arrows(type_text)
        domains = tuple(
            domain
            for part in parts[:-1]
            for group in split_adjacent_binders(part) or (part,)
            if not group.lstrip().startswith(("{", "⦃"))
            for domain in binder_domains(group)
        )
        return len(domains), " → ".join((*domains, parts[-1]))

    try:
        arity, target = explicit_core(goal.target)
        candidate_arity, pattern = explicit_core(action.type_text)
        return bool(
            arity
            and arity == candidate_arity
            and not _INTERNAL_META.search(goal.target)
            and premise_type_pattern_matches(action.type_text, pattern, target)
        )
    except ValueError:
        return False


def _has_independent_explicit_domain(type_text: str) -> bool:
    """Recognize a generic eliminator without naming its source datatype."""

    return bool(premise_independent_result_domains(type_text))


def premise_structured_result_domains(type_text: str) -> tuple[str, ...]:
    """Return inputs from which a flexible polymorphic result is projected.

    Unlike a generic eliminator, a projection's input mentions its result
    variable inside a richer type (for example ``Σ A B → A``).  Keeping the
    domains makes it possible for search controllers to recognize when a
    matching structured value is already available, without assigning any
    meaning to a particular record or projection name.
    """

    result = _expression_tokens(_result_type(type_text))
    # The checked signature already places the result in type position. Its
    # governing binder may be annotated through an arbitrary universe alias;
    # recognizing its dependency must not require that alias to print as Set.
    if (
        not result
        or result[0] not in _binder_names(type_text)
        or parse_relation(_result_type(type_text)) is not None
    ):
        return ()
    result_name = result[0]
    try:
        explicit_domains = tuple(
            binder_domain(group)
            for domain in split_top_level_arrows(type_text)[:-1]
            for group in split_adjacent_binders(domain) or (domain,)
            if not group.lstrip().startswith(("{", "⦃"))
        )
    except ValueError:
        return ()
    return tuple(
        domain
        for domain in explicit_domains
        if result_name in _expression_tokens(domain)
        and not top_level_arrow_count(domain)
        and normalize_type_text(strip_outer_parentheses(domain)) != result_name
    )


def _has_structured_result_domain(type_text: str) -> bool:
    """Whether a bare polymorphic result is extracted from richer input."""

    return bool(premise_structured_result_domains(type_text))


def premise_has_shallow_support(
    type_text: str, *, universe_names: frozenset[str] = DEFAULT_UNIVERSE_NAMES
) -> bool:
    """Whether the existing small composition fragment supports this head.

    Type formation and result-polymorphic operations which need that same
    result as input belong to broader search. This is a scheduling hint, not
    a judgment that an application is ill typed or a goal is impossible.
    In particular, folds may be useful once their higher-order inputs have
    been constructed. The live retriever must retain them for later search.
    """

    return not (
        _is_type_constructor(type_text, universe_names)
        or (
            _has_bare_polymorphic_result(type_text)
            and not _has_independent_explicit_domain(type_text)
            and not _has_structured_result_domain(type_text)
            and not premise_eliminator_source_domains(
                type_text, universe_names=universe_names
            )
        )
    )


def shallow_composition_actions(
    goal: GoalInfo, actions: tuple[ScopePremiseAction, ...]
) -> tuple[ScopePremiseAction, ...]:
    """Select the small pre-case grammar without changing retrieved scope.

    Unknown/metavariable and universe targets keep all ingredients. The
    classification deliberately shares the legacy fragment's conservative
    syntax rather than inventing datatype- or declaration-specific rules.
    Ordinary, non-deferred search must still receive the complete input.
    """

    target_head = result_head(goal.target)
    if _INTERNAL_META.search(goal.target) or is_universe_head(
        target_head, goal.sort_names
    ):
        return actions
    return tuple(
        a
        for a in actions
        if premise_has_shallow_support(a.type_text, universe_names=goal.sort_names)
    )


@syntax_scan_batch()
def rank_scope_premises(
    goal: GoalInfo,
    declarations: tuple[tuple[str, str], ...],
    *,
    excluded_names: frozenset[str] = frozenset(),
    max_candidates: int = DEFAULT_SCOPE_PREMISE_LIMIT,
    shallow_only: bool = True,
) -> tuple[ScopePremiseAction, ...]:
    """Return a deterministic bounded declaration-head batch.

    Ranking uses only generic lexical overlap and telescope/result complexity.
    It cannot mark a declaration applicable; the caller must submit every
    retained head to Agda's refinement command.

    Observational composition can set ``shallow_only=False`` to retain type
    formers and other heads excluded from shallow refinement. It must apply
    its own support filter and kernel checks. Scope, exclusions, and the
    candidate limit are unchanged.
    """

    if max_candidates <= 0:
        return ()
    goal_tokens = _tokens(goal.target)
    actions: list[ScopePremiseAction] = []
    seen: set[str] = set()
    for name, type_text in declarations:
        short_name = name.rsplit(".", 1)[-1]
        if (
            not name
            or not type_text
            or name in seen
            or name in excluded_names
            or short_name in excluded_names
            or (
                shallow_only
                and not premise_has_shallow_support(
                    type_text, universe_names=goal.sort_names
                )
            )
        ):
            continue
        seen.add(name)
        try:
            action = ScopePremiseAction(
                name=name,
                type_text=normalize_type_text(type_text),
                expression=_render_head(name),
                module_scope_id=(
                    goal.module_scope.scope_id
                    if goal.module_scope is not None
                    else None
                ),
            )
        except ValueError:
            # The scope catalogue can include pretty-printed internal entries
            # that are not valid source declaration heads.  They are outside
            # this action schema and must not invalidate otherwise sound
            # search state.
            continue
        actions.append(action)

    def priority(action: ScopePremiseAction) -> tuple[int, int, int, str]:
        try:
            parts = split_top_level_arrows(action.type_text)
        except ValueError:
            parts = (action.type_text,)
        result = _result_type(action.type_text)
        overlap = len(goal_tokens & _tokens(f"{action.name} {result}"))
        result_size = len(_tokens(result))
        return (-overlap, len(parts) - 1, -result_size, action.name)

    return tuple(heapq.nsmallest(max_candidates, actions, key=priority))
