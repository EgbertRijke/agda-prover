"""Kernel-checked lifting of unary recursive evidence through a constructor.

This bounded P1 rule is derived from the current clause and live Agda types.
It recognizes no datatype, relation, or constructor name. When a recursive
call returns evidence for a parametric reflexive binary family and the current
goal applies the clause's constructor to both endpoints, it proposes the
family's generic action on functions. Agda must accept the generated helper.

The rule is one small instance of the general constructor-action synthesis
planned for Stage 2. Keeping it metadata-driven avoids the former legacy
implementation, which embedded Agda's identity notation and constructor.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from difflib import SequenceMatcher
from functools import lru_cache
from itertools import chain, product

from .algebraic_rewriting import proof_relevant_ac_path
from .contracts import GoalInfo
from .graph_search import bounded_shortest_path
from .notation import render_application, strip_outer_parentheses
from .presentation import reconstruct_case_split
from .relation_path import explicit_arity, parse_relation
from .type_syntax import normalize_type_text, split_top_level_arrows

_HOLE = re.compile(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])")


@dataclass(frozen=True)
class UnaryRecursiveClause:
    lhs: str
    constructor_name: str
    descendant_name: str

    def recursive_call(self, root_name: str) -> str:
        return f"{root_name} {self.descendant_name}"


@dataclass(frozen=True)
class ContextualRelationEvidence:
    """Relation evidence lifted through a syntactically discovered context.

    ``expression`` proves a relation between values of ``inner_type``.
    ``context_body`` is a carrier-valued expression containing ``variable``.
    The closure emits the local action-on-functions eliminator required to
    turn that evidence into the recorded carrier endpoints.  Agda validates
    both the relation's parametricity and the context's type; neither is
    assumed from a datatype or relation name.
    """

    expression: str
    inner_type: str
    outer_left: str
    outer_right: str
    context_body: str
    variable: str


def recursive_clause_lhs(source: str, goal: GoalInfo) -> str | None:
    """Return the generated clause left-hand side containing ``goal``.

    Agda owns the concrete pattern syntax, including mixfix heads and every
    dependent index.  Keeping that text intact makes the recursive lifting
    rule independent of the arity and notation of the definition.
    """

    hole_start, hole_end = (value - 1 for value in goal.source_range)
    line_start = source.rfind("\n", 0, hole_start) + 1
    line_end = source.find("\n", hole_end)
    if line_end < 0:
        line_end = len(source)
    line = source[line_start:line_end]
    matched_hole = _HOLE.search(line)
    if matched_hole is None or _HOLE.search(line, matched_hole.end()) is not None:
        return None
    prefix = line[: matched_hole.start()]
    equals = prefix.rfind("=")
    if equals < 0 or prefix[equals + 1 :].strip():
        return None
    lhs = prefix[:equals].rstrip()
    return lhs if lhs.strip() else None


def unary_recursive_clause(
    source: str,
    goal: GoalInfo,
    *,
    root_name: str | None,
    root_domain: str | None,
) -> UnaryRecursiveClause | None:
    """Parse the narrow unary recursive clause supported by this P1 rule."""

    if root_name is None or root_domain is None:
        return None
    hole_start, hole_end = (value - 1 for value in goal.source_range)
    line_start = source.rfind("\n", 0, hole_start) + 1
    line_end = source.find("\n", hole_end)
    if line_end < 0:
        line_end = len(source)
    line = source[line_start:line_end]
    matched_hole = _HOLE.search(line)
    if matched_hole is None or _HOLE.search(line, matched_hole.end()) is not None:
        return None
    prefix = line[: matched_hole.start()]
    equals = prefix.rfind("=")
    if equals < 0 or prefix[equals + 1 :].strip():
        return None
    lhs = prefix[:equals].rstrip()
    stripped = lhs.strip()
    if not stripped.startswith(root_name):
        return None
    pattern = stripped[len(root_name) :].strip()
    recursive_pattern = re.fullmatch(r"\(([^\s()]+)\s+([^\s()]+)\)", pattern)
    if recursive_pattern is None:
        return None
    constructor_name, descendant_name = recursive_pattern.groups()
    domain = normalize_type_text(root_domain)
    if not any(
        entry.in_scope
        and entry.name == descendant_name
        and normalize_type_text(entry.type) == domain
        for entry in goal.context
    ):
        return None
    return UnaryRecursiveClause(lhs, constructor_name, descendant_name)


def reflexive_family_constructors(
    declarations: tuple[tuple[str, str], ...],
) -> tuple[tuple[str, str], ...]:
    """Find nullary constructor-shaped reflexive inhabitants and operators.

    Constructor declarations are only proposals. Requiring no explicit
    premises and identical result endpoints sharply limits the rule; the
    generated definition remains subject to Agda's full scope, coverage,
    positivity, termination, and type checks.
    """

    candidates: list[tuple[str, str]] = []
    for name, type_text in declarations:
        if explicit_arity(type_text) != 0:
            continue
        try:
            result = split_top_level_arrows(type_text)[-1]
        except ValueError:
            continue
        relation = parse_relation(result)
        if relation is None:
            continue
        if normalize_type_text(relation.left) != normalize_type_text(relation.right):
            continue
        candidates.append((name, relation.operator))
    return tuple(dict.fromkeys(candidates))


def recursive_result_lifting_edit(
    source: str,
    goal: GoalInfo,
    *,
    root_name: str,
    carrier_type: str,
    clause: UnaryRecursiveClause,
    recursive_result_type: str,
    relation_constructor: str,
    relation_operator: str,
) -> dict[str, object] | None:
    """Propose a datatype-derived recursive lifting helper.

    Both the recursive result and current target must be applications of the
    same live binary family. The helper's operator and pattern constructor are
    copied from live Agda metadata; no family receives special semantics.
    """

    recursive_relation = parse_relation(
        recursive_result_type,
        expected_operator=relation_operator,
    )
    if recursive_relation is None:
        return None
    target_relation = parse_relation(
        goal.target,
        expected_operator=recursive_relation.operator,
    )
    if target_relation is None:
        return None
    constructor = clause.constructor_name
    expected_left = normalize_type_text(
        render_application(constructor, (recursive_relation.left,))
    )
    expected_right = normalize_type_text(
        render_application(constructor, (recursive_relation.right,))
    )
    if (
        normalize_type_text(target_relation.left) != expected_left
        or normalize_type_text(target_relation.right) != expected_right
    ):
        return None

    helper = "agdaprover-lift"
    suffix = 0
    while re.search(rf"(?<![\w-]){re.escape(helper)}(?![\w-])", source):
        suffix += 1
        helper = f"agdaprover-lift-{suffix}"
    operator = recursive_relation.operator
    replacement = (
        f"{clause.lhs} = {helper} {constructor} "
        f"({clause.recursive_call(root_name)})\n"
        "  where\n"
        f"  {helper} : {{x y : {carrier_type}}} → "
        f"(f : {carrier_type} → {carrier_type}) → "
        f"x {operator} y → f x {operator} f y\n"
        f"  {helper} f {relation_constructor} = {relation_constructor}"
    )
    return reconstruct_case_split(source, goal, (replacement,))


def recursive_action_lifting_edit(
    source: str,
    goal: GoalInfo,
    *,
    clause_lhs: str,
    carrier_type: str,
    recursive_expression: str,
    recursive_result_type: str,
    relation_constructor: str,
    relation_operator: str,
    carrier_constructor: str,
) -> dict[str, object] | None:
    """Lift an arbitrary-arity recursive proof through a live constructor.

    Only the current recursive result, target, and constructor catalogue are
    consulted.  The local eliminator is accepted later by Agda under the
    source module's options, so proof relevance is preserved and any use that
    would require K/UIP is rejected by the kernel.
    """

    recursive_relation = parse_relation(
        recursive_result_type,
        expected_operator=relation_operator,
    )
    if recursive_relation is None:
        return None
    target_relation = parse_relation(
        goal.target,
        expected_operator=recursive_relation.operator,
    )
    if target_relation is None:
        return None
    expected_left = normalize_type_text(
        render_application(carrier_constructor, (recursive_relation.left,))
    )
    expected_right = normalize_type_text(
        render_application(carrier_constructor, (recursive_relation.right,))
    )
    if (
        normalize_type_text(target_relation.left) != expected_left
        or normalize_type_text(target_relation.right) != expected_right
    ):
        return None

    helper = "agdaprover-lift"
    suffix = 0
    while re.search(rf"(?<![\w-]){re.escape(helper)}(?![\w-])", source):
        suffix += 1
        helper = f"agdaprover-lift-{suffix}"
    operator = recursive_relation.operator
    replacement = (
        f"{clause_lhs} = {helper} {carrier_constructor} "
        f"({recursive_expression})\n"
        "  where\n"
        f"  {helper} : {{x y : {carrier_type}}} → "
        f"(f : {carrier_type} → {carrier_type}) → "
        f"x {operator} y → f x {operator} f y\n"
        f"  {helper} f {relation_constructor} = {relation_constructor}"
    )
    return reconstruct_case_split(source, goal, (replacement,))


@dataclass(frozen=True)
class _RelationProof:
    left: str
    right: str
    expression: str
    nodes: int

    @property
    def key(self) -> tuple[str, str]:
        return (
            _alpha_surface_key(self.left),
            _alpha_surface_key(self.right),
        )


def _unary_context_body(
    inner_left: str,
    inner_right: str,
    outer_left: str,
    outer_right: str,
    variable: str,
    *,
    allow_unparenthesized_compounds: bool = False,
) -> str | None:
    """Recover one common one-hole context from two endpoint pairs.

    This is syntactic anti-unification, not an interpretation of any operator.
    Parentheses are retained because they encode the term tree.  Only a pair
    immediately surrounding the hole itself is ignored: ``C (x)`` and
    ``C x`` denote the same context, while ``(x op y) op z`` and
    ``x op (y op z)`` remain distinct.  The resulting lambda is later
    type-checked in the original module.
    """

    marker = "AGDAPROVER-HOLE"

    def unambiguous_occurrence(
        haystack: str,
        needle: str,
        index: int,
        end: int,
    ) -> bool:
        """Reject compound text that is not visibly a parsed subterm.

        Without Agda's fixity table, a substring such as ``x + y`` in
        ``suc x + y`` cannot soundly be interpreted as the argument of
        ``suc``.  Parentheses provide the required surface certificate.
        Atomic names remain safe at ordinary token boundaries.
        """

        if allow_unparenthesized_compounds or not any(
            character.isspace() for character in needle
        ):
            return True
        return (
            index > 0
            and end < len(haystack)
            and haystack[index - 1] == "("
            and haystack[end] == ")"
        )

    def contexts(inner: str, outer: str) -> dict[str, str]:
        needle = normalize_type_text(strip_outer_parentheses(inner))
        haystack = normalize_type_text(strip_outer_parentheses(outer))
        if not needle:
            return {}
        found: dict[str, str] = {}
        start = 0
        while True:
            index = haystack.find(needle, start)
            if index < 0:
                break
            end = index + len(needle)
            left_boundary = (
                index == 0
                or not needle[0].isalnum()
                or not haystack[index - 1].isalnum()
            )
            right_boundary = (
                end == len(haystack)
                or not needle[-1].isalnum()
                or not haystack[end].isalnum()
            )
            if (
                left_boundary
                and right_boundary
                and unambiguous_occurrence(haystack, needle, index, end)
                and not (index == 0 and end == len(haystack))
            ):
                rendered = haystack[:index] + marker + haystack[end:]
                canonical = normalize_type_text(rendered)
                previous = None
                while previous != canonical:
                    previous = canonical
                    canonical = canonical.replace(f"({marker})", marker)
                found[canonical] = canonical.replace(marker, variable)
            start = index + 1
        return found

    left_contexts = contexts(inner_left, outer_left)
    right_contexts = contexts(inner_right, outer_right)
    common = set(left_contexts) & set(right_contexts)
    if not common:
        return None
    selected = min(common, key=lambda value: (len(value), value))
    return left_contexts[selected]


def common_unary_relation_context(
    inner_left: str,
    inner_right: str,
    outer_left: str,
    outer_right: str,
    variable: str,
    *,
    allow_unparenthesized_compounds: bool = False,
) -> str | None:
    """Expose datatype-neutral one-hole context recovery to case search."""

    return _unary_context_body(
        inner_left,
        inner_right,
        outer_left,
        outer_right,
        variable,
        allow_unparenthesized_compounds=allow_unparenthesized_compounds,
    )


@lru_cache(maxsize=8192)
def _alpha_surface_key(text: str) -> str:
    """Canonicalize displayed lambda names for finite relation-graph keys.

    Agda often preserves the source binder in one endpoint and prints a fresh
    interaction binder in a definitionally equal endpoint.  The closure graph
    only uses this key to propose an explicit proof term, which the kernel
    subsequently validates, so alpha-normalizing these surface names is both
    sound and substantially more selective than another case split.
    """

    normalized = normalize_type_text(strip_outer_parentheses(text))
    binders = tuple(
        match.group(1)
        for match in re.finditer(r"λ ([^\s{}():→]+) →", normalized)
        if match.group(1) != "_"
    )
    for index, binder in enumerate(dict.fromkeys(binders)):
        normalized = re.sub(
            rf"(?<![\w-]){re.escape(binder)}(?![\w-])",
            f"agdaprover-bound-{index}",
            normalized,
        )
    return normalized


def _unary_context_replacements(
    inner_left: str,
    inner_right: str,
    outer: str,
    variable: str,
    *,
    allow_unparenthesized_compounds: bool = False,
) -> tuple[tuple[str, str], ...]:
    """Rewrite each proper occurrence and retain its explicit lambda body."""

    marker = "AGDAPROVER-HOLE"
    needle = normalize_type_text(strip_outer_parentheses(inner_left))
    replacement = normalize_type_text(strip_outer_parentheses(inner_right))
    haystack = normalize_type_text(strip_outer_parentheses(outer))
    if not needle:
        return ()

    def unambiguous_occurrence(index: int, end: int) -> bool:
        if allow_unparenthesized_compounds or not any(
            character.isspace() for character in needle
        ):
            return True
        return (
            index > 0
            and end < len(haystack)
            and haystack[index - 1] == "("
            and haystack[end] == ")"
        )

    found: list[tuple[str, str]] = []
    start = 0
    while True:
        index = haystack.find(needle, start)
        if index < 0:
            break
        end = index + len(needle)
        left_boundary = (
            index == 0 or not needle[0].isalnum() or not haystack[index - 1].isalnum()
        )
        right_boundary = (
            end == len(haystack)
            or not needle[-1].isalnum()
            or not haystack[end].isalnum()
        )
        if (
            left_boundary
            and right_boundary
            and unambiguous_occurrence(index, end)
            and not (index == 0 and end == len(haystack))
        ):
            marked = haystack[:index] + marker + haystack[end:]
            canonical = normalize_type_text(marked)
            previous = None
            while previous != canonical:
                previous = canonical
                canonical = canonical.replace(f"({marker})", marker)
            body = canonical.replace(marker, variable)
            rendered_replacement = (
                f"({replacement})"
                if any(character.isspace() for character in replacement)
                else replacement
            )
            rewritten = canonical.replace(marker, rendered_replacement)
            found.append((rewritten, body))
        start = index + 1
    return tuple(dict.fromkeys(found))


def common_outer_relation_context(
    left: str,
    right: str,
    variable: str,
) -> tuple[str, str, str] | None:
    """Extract one shared surface context around the differing subterms.

    The operation is deliberately syntactic and proposes only a lambda body;
    the reconstructed clause is subsequently checked by Agda.  Keeping the
    maximal common prefix and suffix lets relation closure reason inside
    arbitrary constructor, record, and operation applications instead of
    requiring the outer symbol to have a particular arity.
    """

    left_text = normalize_type_text(strip_outer_parentheses(left))
    right_text = normalize_type_text(strip_outer_parentheses(right))
    if not left_text or not right_text or left_text == right_text:
        return None
    prefix = 0
    prefix_limit = min(len(left_text), len(right_text))
    while prefix < prefix_limit and left_text[prefix] == right_text[prefix]:
        prefix += 1
    suffix = 0
    suffix_limit = min(len(left_text), len(right_text)) - prefix
    while (
        suffix < suffix_limit
        and left_text[len(left_text) - suffix - 1]
        == right_text[len(right_text) - suffix - 1]
    ):
        suffix += 1

    # Never splice through a name token.  Punctuation, whitespace, and
    # parenthesis boundaries are safe candidates for an Agda expression hole.
    while (
        prefix
        and prefix < prefix_limit
        and (left_text[prefix - 1].isalnum() and left_text[prefix].isalnum())
    ):
        prefix -= 1
    while suffix and (
        len(left_text) - suffix > 0
        and len(right_text) - suffix > 0
        and left_text[len(left_text) - suffix - 1].isalnum()
        and left_text[len(left_text) - suffix].isalnum()
    ):
        suffix -= 1
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}

    def balanced(text: str) -> bool:
        stack: list[str] = []
        for character in text:
            if character in pairs:
                stack.append(pairs[character])
            elif character in pairs.values():
                if not stack or stack.pop() != character:
                    return False
        return not stack

    while suffix:
        left_end = len(left_text) - suffix
        right_end = len(right_text) - suffix
        if balanced(left_text[prefix:left_end]) and balanced(
            right_text[prefix:right_end]
        ):
            break
        suffix -= 1
    if prefix == 0 and suffix == 0:
        return None
    left_end = len(left_text) - suffix if suffix else len(left_text)
    right_end = len(right_text) - suffix if suffix else len(right_text)
    inner_left = left_text[prefix:left_end].strip()
    inner_right = right_text[prefix:right_end].strip()
    if not inner_left or not inner_right:
        return None
    context = left_text[:prefix] + variable + (left_text[left_end:] if suffix else "")
    return inner_left, inner_right, context


def recursive_relation_closure_edit(
    source: str,
    goal: GoalInfo,
    *,
    clause_lhs: str,
    carrier_type: str,
    recursive_results: tuple[tuple[str, str], ...],
    relation_constructor: str,
    relation_operator: str,
    carrier_constructors: tuple[str, ...],
    rewrite_declarations: tuple[tuple[str, str], ...] = (),
    contextual_evidence: tuple[ContextualRelationEvidence, ...] = (),
    max_lift_depth: int = 3,
    max_path_nodes: int = 16,
    max_context_edges: int = 64,
    max_context_pair_checks: int = 4096,
    allow_term_contexts: bool = True,
    allow_unparenthesized_contexts: bool = False,
    allow_implicit_fixity_grouping: bool = False,
    allow_kernel_endpoint_conversion: bool = False,
) -> dict[str, object] | None:
    """Close a recursive relation goal by bounded proof-relevant saturation.

    Recursive calls provide directed evidence edges.  For a live reflexive
    one-constructor family we derive, locally, its symmetry, transitivity, and
    action under unary carrier constructors, then search a finite graph.  No
    equation is collapsed and no proof is identified with another: the
    emitted expression explicitly retains every evidence term.
    """

    target = parse_relation(goal.target, expected_operator=relation_operator)
    if target is None or (not recursive_results and not contextual_evidence):
        return None
    path_node_limit = max_path_nodes

    def fresh(base: str) -> str:
        candidate = base
        suffix = 0
        while re.search(rf"(?<![\w-]){re.escape(candidate)}(?![\w-])", source):
            suffix += 1
            candidate = f"{base}-{suffix}"
        return candidate

    lift_name = fresh("agdaprover-lift")
    sym_name = fresh("agdaprover-sym")
    trans_name = fresh("agdaprover-trans")
    context_variable = fresh("agdaprover-value")
    # Avoid collisions among helpers selected against the same original text.
    while sym_name == lift_name:
        sym_name += "-1"
    while trans_name in {lift_name, sym_name}:
        trans_name += "-1"

    best: dict[tuple[str, str], _RelationProof] = {}
    contextual_helpers: list[tuple[str, ContextualRelationEvidence]] = []
    endpoint_keys: dict[str, str] = {}
    proof_keys: dict[tuple[str, str], tuple[str, str]] = {}

    def endpoint_key(text: str) -> str:
        cached = endpoint_keys.get(text)
        if cached is not None:
            return cached
        key = _alpha_surface_key(text)
        if allow_implicit_fixity_grouping:
            # This mode is used only for candidates that receive an immediate
            # fresh Agda check.  Ignore grouping parentheses in the finite
            # graph so that the same fixity-parsed term printed explicitly in
            # one edge and implicitly in another can meet.  The proof term
            # retains its parentheses; a genuinely different association is
            # therefore rejected by the kernel rather than accepted here.
            key = normalize_type_text(key.replace("(", "").replace(")", ""))
        endpoint_keys[text] = key
        return key

    def proof_key(proof: _RelationProof) -> tuple[str, str]:
        raw = (proof.left, proof.right)
        cached = proof_keys.get(raw)
        if cached is not None:
            return cached
        key = (endpoint_key(proof.left), endpoint_key(proof.right))
        proof_keys[raw] = key
        return key

    target_key = (endpoint_key(target.left), endpoint_key(target.right))

    def retain(proof: _RelationProof) -> bool:
        key = proof_key(proof)
        previous = best.get(key)
        if previous is not None and previous.nodes <= proof.nodes:
            return False
        best[key] = proof
        return True

    def path_between(
        start: str,
        wanted: str,
        start_text: str,
        wanted_text: str,
    ) -> _RelationProof | None:
        direct = best.get((start, wanted))
        if direct is not None:
            return direct
        if start == wanted:
            return _RelationProof(start_text, wanted_text, relation_constructor, 1)
        proofs = tuple(
            sorted(
                best.values(),
                key=lambda proof: (
                    proof_key(proof)[0],
                    proof.nodes,
                    proof.expression,
                    proof_key(proof)[1],
                ),
            )
        )
        endpoints = tuple(
            sorted(
                {endpoint for proof in proofs for endpoint in proof_key(proof)}
                | {start, wanted}
            )
        )
        endpoint_index = {endpoint: index for index, endpoint in enumerate(endpoints)}
        # Charging one extra unit per edge and raising the bound by one is
        # exactly ``sum(edge.nodes) + joins`` for a nonempty path.
        path = bounded_shortest_path(
            len(endpoints),
            tuple(
                (
                    endpoint_index[proof_key(proof)[0]],
                    endpoint_index[proof_key(proof)[1]],
                    proof.nodes + 1,
                )
                for proof in proofs
            ),
            endpoint_index[start],
            endpoint_index[wanted],
            path_node_limit + 1,
        )
        if path is None or not path:
            return None
        selected = tuple(proofs[index] for index in path)
        expression = selected[0].expression
        nodes = selected[0].nodes
        for proof in selected[1:]:
            expression = f"{trans_name} ({expression}) ({proof.expression})"
            nodes += proof.nodes + 1
        return _RelationProof(
            start_text,
            wanted_text,
            expression,
            nodes,
        )

    def shortest_path() -> _RelationProof | None:
        """Find a bounded evidence path without saturating all endpoint pairs."""

        return path_between(*target_key, target.left, target.right)

    def reachable_paths(start: str, start_text: str) -> dict[str, _RelationProof]:
        endpoints = {
            endpoint for proof in best.values() for endpoint in proof_key(proof)
        }
        return {
            endpoint: path
            for endpoint in sorted(endpoints)
            if endpoint != start
            and (
                path := path_between(
                    start,
                    endpoint,
                    start_text,
                    next(
                        (
                            text
                            for proof in best.values()
                            for text in (proof.left, proof.right)
                            if endpoint_key(text) == endpoint
                        ),
                        endpoint,
                    ),
                )
            )
            is not None
        }

    for expression, type_text in recursive_results:
        edge = parse_relation(type_text, expected_operator=relation_operator)
        if edge is not None:
            edge_key = (endpoint_key(edge.left), endpoint_key(edge.right))
            if (
                not contextual_evidence
                or edge_key[0] != edge_key[1]
                or edge_key == target_key
            ):
                retain(_RelationProof(edge.left, edge.right, expression, 1))
    for index, evidence in enumerate(contextual_evidence):
        helper_name = fresh(
            "agdaprover-context-lift"
            if index == 0
            else f"agdaprover-context-lift-{index}"
        )
        context_function = f"(λ {evidence.variable} → {evidence.context_body})"
        retain(
            _RelationProof(
                evidence.outer_left,
                evidence.outer_right,
                f"{helper_name} {context_function} ({evidence.expression})",
                2,
            )
        )
        contextual_helpers.append((helper_name, evidence))
    if not best:
        return None

    # A reversed hypothesis may need to be lifted under one or more contexts.
    # Orient seeds before contextual closure; ambiguous surface occurrences
    # have already been rejected by ``_unary_context_replacements``.
    for proof in tuple(best.values()):
        retain(
            _RelationProof(
                proof.right,
                proof.left,
                f"{sym_name} ({proof.expression})",
                proof.nodes + 1,
            )
        )

    # Constructor congruence is finite here: depth is explicit and small, and
    # terms exceeding the target's surface size cannot form a useful shortest
    # path back because the only generated maps add outer constructors.
    surface_limit = len(normalize_type_text(goal.target)) + 64
    frontier = tuple(best.values())
    for _depth in range(max_lift_depth):
        generated: list[_RelationProof] = []
        for proof in frontier:
            for constructor in carrier_constructors:
                left = render_application(constructor, (proof.left,))
                right = render_application(constructor, (proof.right,))
                if len(normalize_type_text(left + " " + right)) > surface_limit:
                    continue
                lifted = _RelationProof(
                    left,
                    right,
                    f"{lift_name} {constructor} ({proof.expression})",
                    proof.nodes + 1,
                )
                if retain(lifted):
                    generated.append(lifted)
        frontier = tuple(generated)
        if not frontier:
            break

    # A constructor is only one possible term context.  Recover other unary
    # contexts by syntactic anti-unification of already known boundaries.  In
    # an algebraic law this discovers contexts such as ``λ w → op w z``;
    # in dependent code it can equally discover a record constructor or an
    # indexed family application.  The locally generated action-on-functions
    # principle is the same in every case and Agda rejects ill-typed contexts.
    context_solved = shortest_path()
    if allow_term_contexts and context_solved is None:
        generated_contexts = 0
        pair_checks = 0
        for _context_depth in range(max_lift_depth):
            boundary_text: dict[str, str] = {
                normalize_type_text(strip_outer_parentheses(endpoint)): endpoint
                for proof in best.values()
                for endpoint in (proof.left, proof.right)
            }
            for endpoint in (target.left, target.right):
                boundary_text.setdefault(
                    normalize_type_text(strip_outer_parentheses(endpoint)), endpoint
                )
            # Target endpoints are the only boundaries known a priori to be
            # useful.  Put them before the wider evidence graph so a small
            # context budget cannot be monopolized by relations among
            # unrelated recursive applications.
            boundaries = tuple(
                dict.fromkeys((target.left, target.right, *boundary_text.values()))
            )
            generated_this_round = 0
            normalized_targets = tuple(
                normalize_type_text(strip_outer_parentheses(endpoint))
                for endpoint in (target.left, target.right)
            )

            def target_occurrences(
                proof: _RelationProof,
                targets: tuple[str, ...] = normalized_targets,
            ) -> int:
                endpoints = tuple(
                    normalize_type_text(strip_outer_parentheses(endpoint))
                    for endpoint in (proof.left, proof.right)
                )
                return sum(
                    bool(endpoint) and endpoint in outer
                    for endpoint in endpoints
                    for outer in targets
                )

            proofs = tuple(
                sorted(
                    best.values(),
                    key=lambda proof: (
                        -target_occurrences(proof),
                        proof.nodes,
                        proof.expression,
                    ),
                )
            )
            # First exhaust direct occurrence rewrites for every edge.  These
            # preserve one visible context and are both cheaper and more
            # precise than pairwise anti-unification.
            for proof in proofs:
                for outer in boundaries:
                    for rewritten, context_body in _unary_context_replacements(
                        proof.left,
                        proof.right,
                        outer,
                        context_variable,
                        allow_unparenthesized_compounds=(
                            allow_unparenthesized_contexts
                        ),
                    ):
                        if (
                            len(normalize_type_text(outer + " " + rewritten))
                            > surface_limit
                        ):
                            continue
                        contextual = _RelationProof(
                            outer,
                            rewritten,
                            f"{lift_name} (λ {context_variable} → {context_body}) "
                            f"({proof.expression})",
                            proof.nodes + 2,
                        )
                        if proof_key(contextual) not in best and retain(contextual):
                            generated_contexts += 1
                            generated_this_round += 1
                        if generated_contexts >= max_context_edges:
                            break
                    if generated_contexts >= max_context_edges:
                        break
                if generated_contexts >= max_context_edges:
                    break
            context_solved = shortest_path()
            if context_solved is not None:
                break
            if generated_contexts >= max_context_edges:
                break
            if generated_this_round:
                # Newly exposed boundaries can support another exact direct
                # lift.  Reach that fixed point before spending the cap on
                # the quadratic pairwise phase.
                continue
            # Only then use the broader two-boundary recovery.  Keeping this
            # as a second phase prevents early edges from monopolizing the
            # finite context cap before later recursive hypotheses are lifted.
            preferred_pairs = (
                (target.left, target.right),
                (target.right, target.left),
            )
            for proof in proofs:
                if (
                    generated_contexts >= max_context_edges
                    or pair_checks >= max_context_pair_checks
                ):
                    break
                boundary_pairs = chain(
                    preferred_pairs,
                    product(boundaries, repeat=2),
                )
                for outer_left, outer_right in boundary_pairs:
                    pair_checks += 1
                    boundary_context_body = _unary_context_body(
                        proof.left,
                        proof.right,
                        outer_left,
                        outer_right,
                        context_variable,
                        allow_unparenthesized_compounds=(
                            allow_unparenthesized_contexts
                        ),
                    )
                    if boundary_context_body is None:
                        if pair_checks >= max_context_pair_checks:
                            break
                        continue
                    contextual = _RelationProof(
                        outer_left,
                        outer_right,
                        f"{lift_name} (λ {context_variable} → "
                        f"{boundary_context_body}) "
                        f"({proof.expression})",
                        proof.nodes + 2,
                    )
                    # Constructor lifts are structurally exact and must not be
                    # displaced by a shorter surface anti-unification that only
                    # becomes meaningful after fixity parsing. Contextual edges
                    # therefore fill missing graph edges rather than replacing
                    # already justified ones.
                    if proof_key(contextual) not in best and retain(contextual):
                        generated_contexts += 1
                        generated_this_round += 1
                    if (
                        generated_contexts >= max_context_edges
                        or pair_checks >= max_context_pair_checks
                    ):
                        break
                if pair_checks >= max_context_pair_checks:
                    break
            context_solved = shortest_path()
            if (
                context_solved is not None
                or generated_contexts >= max_context_edges
                or pair_checks >= max_context_pair_checks
                or generated_this_round == 0
            ):
                break

    solved: _RelationProof | None
    if rewrite_declarations:
        algebraic = proof_relevant_ac_path(
            left=target.left,
            right=target.right,
            relation_operator=relation_operator,
            evidence=recursive_results,
            declarations=rewrite_declarations,
            lift_name=lift_name,
            sym_name=sym_name,
            trans_name=trans_name,
            context_variable=context_variable,
            max_nodes=max(24, path_node_limit + 12),
        )
        if algebraic is not None:
            solved = _RelationProof(target.left, target.right, algebraic, 1)
        else:
            contextual_target = common_outer_relation_context(
                target.left,
                target.right,
                context_variable,
            )
            contextual_algebraic = (
                proof_relevant_ac_path(
                    left=contextual_target[0],
                    right=contextual_target[1],
                    relation_operator=relation_operator,
                    evidence=recursive_results,
                    declarations=rewrite_declarations,
                    lift_name=lift_name,
                    sym_name=sym_name,
                    trans_name=trans_name,
                    context_variable=context_variable,
                    max_nodes=max(24, path_node_limit + 12),
                )
                if contextual_target is not None
                else None
            )
            solved = (
                _RelationProof(
                    target.left,
                    target.right,
                    f"{lift_name} (λ {context_variable} → "
                    f"{contextual_target[2]}) ({contextual_algebraic})",
                    3,
                )
                if contextual_target is not None and contextual_algebraic is not None
                else context_solved
            )
    else:
        solved = context_solved

    # Symmetry remains explicit evidence; adding it once is involutive at the
    # graph level, so a second round cannot improve a shortest path.
    for proof in tuple(best.values()):
        retain(
            _RelationProof(
                proof.right,
                proof.left,
                f"{sym_name} ({proof.expression})",
                proof.nodes + 1,
            )
        )

    solved = solved or shortest_path()
    if solved is None and allow_kernel_endpoint_conversion:
        # A completed earlier clause can make a graph endpoint definitionally
        # equal to the displayed target without giving the surface search a
        # safe rewrite rule.  Retain only paths sharing one exact target
        # endpoint, rank the other endpoint by structural surface proximity,
        # and let the caller immediately ask Agda whether conversion closes
        # the interaction point.  This is proposal generation, never an
        # equality assumption.
        convertible = tuple(
            {
                proof.expression: proof
                for proof in chain(
                    reachable_paths(target_key[0], target.left).values(),
                    (
                        proof
                        for proof in best.values()
                        if proof_key(proof)[0] == target_key[0]
                        or proof_key(proof)[1] == target_key[1]
                    ),
                )
            }.values()
        )
        if convertible:

            def conversion_priority(proof: _RelationProof) -> tuple[float, int, str]:
                key = proof_key(proof)
                compared = key[1] if key[0] == target_key[0] else key[0]
                wanted = target_key[1] if key[0] == target_key[0] else target_key[0]
                similarity = SequenceMatcher(None, compared, wanted).ratio()
                return (-similarity, proof.nodes, proof.expression)

            solved = min(convertible, key=conversion_priority)
    if solved is None:
        return None

    clause_indent = clause_lhs[: len(clause_lhs) - len(clause_lhs.lstrip())]
    local_indent = f"{clause_indent}  "
    helper_lines: list[str] = [
        f"{local_indent}{lift_name} : {{x y : {carrier_type}}} → "
        f"(f : {carrier_type} → {carrier_type}) → "
        f"x {relation_operator} y → f x {relation_operator} f y",
        f"{local_indent}{lift_name} f {relation_constructor} = {relation_constructor}",
        f"{local_indent}{sym_name} : {{x y : {carrier_type}}} → "
        f"x {relation_operator} y → y {relation_operator} x",
        f"{local_indent}{sym_name} {relation_constructor} = {relation_constructor}",
        f"{local_indent}{trans_name} : {{x y z : {carrier_type}}} → "
        f"x {relation_operator} y → y {relation_operator} z → "
        f"x {relation_operator} z",
        f"{local_indent}{trans_name} {relation_constructor} q = q",
    ]
    for helper_name, evidence in contextual_helpers:
        if helper_name not in solved.expression:
            continue
        helper_lines.extend(
            (
                f"{local_indent}{helper_name} : "
                f"{{x y : {evidence.inner_type}}} → "
                f"(f : ({evidence.inner_type}) → {carrier_type}) → "
                f"x {relation_operator} y → "
                f"f x {relation_operator} f y",
                f"{local_indent}{helper_name} f {relation_constructor} = "
                f"{relation_constructor}",
            )
        )
    replacement = (
        f"{clause_lhs} = {solved.expression}"
        f"\n{local_indent}where\n" + "\n".join(helper_lines)
    )
    return reconstruct_case_split(source, goal, (replacement,))
