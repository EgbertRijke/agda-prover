"""Pure proposals connecting dependent fields and contextual functions.

Types are observations supplied by the caller, not Python substitutions.
Every application remains a proposal until the kernel infers its actual type.
No kernel state, scope acquisition, datatype names or algebraic laws live here.
"""

from __future__ import annotations

import re
from collections.abc import Iterator
from dataclasses import dataclass, field
from itertools import product

from ..notation import binary_mixfix_head, render_application, strip_outer_parentheses
from ..relation_path import parse_relation
from ..resource_budget import checkpoint
from ..type_syntax import (
    binder_domains,
    normalize_type_text,
    parse_named_binder,
    result_head,
    split_adjacent_binders,
    split_top_level_application,
    split_top_level_arrows,
    top_level_arrow_count,
)
from ..type_syntax import (
    telescope_introduction as telescope_introduction,
)


@dataclass(frozen=True)
class EvidenceTerm:
    expression: str
    type_text: str
    depth: int = 0


@dataclass(frozen=True)
class EvidenceApplication:
    """Typed inputs to a proposal; its result type is not yet known."""

    function: EvidenceTerm
    arguments: tuple[EvidenceTerm, ...]
    expression: str = field(init=False)
    depth: int = field(init=False)
    type_text: str = field(default="", init=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "expression",
            render_application(
                self.function.expression, tuple(a.expression for a in self.arguments)
            ),
        )
        object.__setattr__(
            self, "depth", 1 + max(t.depth for t in (self.function, *self.arguments))
        )


@dataclass(frozen=True)
class IndexedEvidence:
    value: EvidenceTerm
    source: str
    target: str


def transport_index_labels(
    type_text: str, families: dict[str, int]
) -> tuple[str, str] | None:
    """Read the supplied operation's hidden endpoint labels, if unambiguous."""
    domains = explicit_domains(type_text)
    if len(domains) != 3:
        return None
    relation = parse_relation(domains[1], prefix_heads=families)
    if relation is None:
        return None
    labels: set[str] = set()
    try:
        for part in split_top_level_arrows(type_text)[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder and binder.visibility == "implicit":
                    if "=" in binder.names:
                        continue
                    labels.update(binder.names)
    except ValueError:
        return None
    if relation.left in labels and relation.right in labels:
        return relation.left, relation.right
    return None


def is_family_transport(type_text: str, families: dict[str, int]) -> bool:
    """Recognize a supplied ``F x → F y`` operation requiring an ``R x y``.

    This records telescope wiring only. It assigns no transport law to R;
    the named operation must be supplied, and its application kernel-checked.
    """
    parts = split_top_level_arrows(type_text)
    groups = tuple(
        group
        for part in parts[:-1]
        for group in split_adjacent_binders(part) or (part,)
        if not group.lstrip().startswith(("{", "⦃"))
    )
    domains = explicit_domains(type_text)
    if len(domains) != 3 or not groups:
        return False
    motive = parse_named_binder(groups[0])
    if (
        motive is None
        or len(motive.names) != 1
        or not result_head(motive.domain).startswith("Set")
    ):
        return False
    relation = parse_relation(domains[1], prefix_heads=families)
    source = split_top_level_application(domains[2])
    target = split_top_level_application(parts[-1])
    return bool(
        relation
        and len(source) == len(target) == 2
        and source[0] == target[0] == motive.names[0]
        and normalize_type_text(source[1]) == normalize_type_text(relation.left)
        and normalize_type_text(target[1]) == normalize_type_text(relation.right)
    )


def indexed_evidence_inputs(
    goal_type: str, terms: tuple[EvidenceTerm, ...]
) -> Iterator[IndexedEvidence]:
    """Find ready values whose type varies along a visible contextual index."""

    def names(text: str) -> set[str]:
        return set(re.findall(r"[^\s(){}⦃⦄:→]+", text))

    indices = tuple(
        t
        for t in terms
        if not top_level_arrow_count(t.type_text)
        and not result_head(t.type_text).startswith("Set")
    )
    target_names = names(goal_type)
    for value in indices:
        if result_head(value.type_text) != result_head(
            goal_type
        ) or normalize_type_text(value.type_text) == normalize_type_text(goal_type):
            continue
        source_names = names(value.type_text)
        for a in indices:
            for b in indices:
                checkpoint()
                if (
                    a.expression in source_names
                    and b.expression in target_names
                    and a.expression != b.expression
                    and normalize_type_text(a.type_text)
                    == normalize_type_text(b.type_text)
                ):
                    yield IndexedEvidence(value, a.expression, b.expression)


def structured_combinator_applications(
    goal_type: str,
    terms: tuple[EvidenceTerm, ...],
    declarations: tuple[tuple[str, str], ...],
    *,
    shallow_functions: bool = False,
) -> Iterator[str]:
    """Specialize supplied structured builders before rebuilding their output.

    A ready first argument and a later function-valued input make this a
    constrained backward step. The expected result still needs Agda's
    unification; a shared printed head alone is never acceptance evidence.
    """
    head = result_head(goal_type)
    for name, ty in declarations:
        checkpoint()
        domains = explicit_domains(ty)
        if (
            not domains
            or result_head(ty) != head
            or top_level_arrow_count(domains[0])
            or len(split_top_level_application(domains[0])) < 2
            or not any(top_level_arrow_count(d) for d in domains[1:])
        ):
            continue
        for term in terms:
            checkpoint()
            if not top_level_arrow_count(term.type_text) and result_head(
                term.type_text
            ) == result_head(domains[0]):
                if shallow_functions:
                    for index, domain in enumerate(domains[1:], 1):
                        groups = tuple(
                            group
                            for part in split_top_level_arrows(domain)[:-1]
                            for group in split_adjacent_binders(part) or (part,)
                        )
                        if not groups or any(
                            group.lstrip().startswith(("{", "⦃")) for group in groups
                        ):
                            continue
                        arity = len(explicit_domains(domain))
                        for value in terms:
                            checkpoint()
                            if top_level_arrow_count(value.type_text) or result_head(
                                value.type_text
                            ) != result_head(domain):
                                continue
                            # Do not substitute into a dependent telescope.
                            # Give Agda a complete constant-function proposal;
                            # its expected type decides whether dependency,
                            # modality and the ambient value really fit.
                            arguments = [term.expression, *("?" for _ in domains[1:])]
                            arguments[index] = (
                                f"λ {' '.join('_' for _ in range(arity))} → "
                                f"{value.expression}"
                            )
                            yield render_application(name, tuple(arguments))
                yield render_application(
                    name, (term.expression, *("?" for _ in domains[1:]))
                )


def evidence_consequences(
    goal_type: str,
    terms: tuple[EvidenceTerm, ...],
    declarations: tuple[tuple[str, str], ...],
) -> Iterator[str]:
    """Close a supplied relational eliminator with structured evidence.

    A result such as an opaque proposition need not constrain the relation's
    hidden endpoints. Propose visible inhabitants for its hidden value binders;
    checking the complete application determines their actual types. No
    refutation or constructor disjointness is assumed by this generator.
    """
    families = family_names(declarations)
    if parse_relation(goal_type, prefix_heads=families):
        return
    values = tuple(
        term
        for term in terms
        if not top_level_arrow_count(term.type_text)
        and not result_head(term.type_text).startswith("Set")
    )
    for name, ty in declarations:
        checkpoint()
        domains = explicit_domains(ty)
        if len(domains) != 1 or result_head(ty) != result_head(goal_type):
            continue
        relation = parse_relation(domains[0], prefix_heads=families)
        if relation is None:
            continue
        referenced = set(re.findall(r"[^\s(){}⦃⦄:→]+", domains[0]))
        labels: list[str] = []
        for part in split_top_level_arrows(ty)[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if (
                    binder is None
                    or binder.visibility != "implicit"
                    or top_level_arrow_count(binder.domain)
                    or result_head(binder.domain).startswith("Set")
                ):
                    continue
                # Agda renders shadowed labels as {label = local : T}.
                # Named applications use the external label, not the alias.
                if "=" in binder.names:
                    if len(binder.names) == 3 and binder.names[1] == "=":
                        if binder.names[2] in referenced:
                            labels.append(binder.names[0])
                else:
                    labels.extend(
                        label for label in binder.names if label in referenced
                    )
        for witness_name, witness_type in declarations:
            witness_domains = explicit_domains(witness_type)
            if (
                not witness_domains
                or top_level_arrow_count(witness_domains[0])
                or len(split_top_level_application(witness_domains[0])) < 2
                or not parse_relation(
                    split_top_level_arrows(witness_type)[-1],
                    expected_operator=relation.operator,
                    prefix_heads=families,
                )
            ):
                continue
            for evidence in values:
                if len(split_top_level_application(evidence.type_text)) < 2:
                    continue
                witness = render_application(
                    witness_name,
                    (evidence.expression, *("_" for _ in witness_domains[1:])),
                )
                for endpoints in product(values, repeat=len(labels)):
                    checkpoint()
                    applied = " ".join(
                        (
                            render_application(name, ()),
                            *(
                                f"{{{label} = {v.expression}}}"
                                for label, v in zip(labels, endpoints, strict=True)
                            ),
                        )
                    )
                    yield render_application(applied, (witness,))


def has_structured_builder(
    goal_type: str,
    context_types: tuple[str, ...],
    declarations: tuple[tuple[str, str], ...],
) -> bool:
    """Predict a ready builder after introducing the goal's telescope."""
    available = (*context_types, *explicit_domains(goal_type))
    return (
        next(
            structured_combinator_applications(
                split_top_level_arrows(goal_type)[-1],
                tuple(EvidenceTerm("_", ty) for ty in available),
                (
                    *declarations,
                    *(("_", ty) for ty in available if top_level_arrow_count(ty)),
                ),
            ),
            None,
        )
        is not None
    )


def explicit_domains(type_text: str) -> tuple[str, ...]:
    try:
        return tuple(
            domain
            for part in split_top_level_arrows(type_text)[:-1]
            for group in split_adjacent_binders(part) or (part,)
            if not group.lstrip().startswith(("{", "⦃"))
            for domain in binder_domains(group)
        )
    except ValueError:
        return ()


def implicit_value_type(type_text: str) -> str | None:
    """View a value after only ordinary implicit arguments, for proposals.

    Keep its original type on the evidence term: this view neither substitutes
    indices nor claims an instantiation exists. Agda must infer the complete
    consuming application, or check the value against the requested goal.
    Explicit and instance arguments require other search lanes.
    """
    try:
        parts = split_top_level_arrows(type_text)
        for part in parts[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder is None or binder.visibility != "implicit":
                    return None
        return parts[-1]
    except ValueError:
        return None


def family_names(declarations: tuple[tuple[str, str], ...]) -> dict[str, int]:
    """Recognize type-valued families from signatures, never their spelling."""
    result: dict[str, int] = {}
    for name, ty in declarations:
        checkpoint()
        try:
            arity = len(explicit_domains(ty))
            if arity >= 2 and result_head(ty).startswith("Set"):
                result[strip_outer_parentheses(name)] = arity
        except ValueError:
            continue
    return result


def _flexible_domain(type_text: str, domain: str) -> bool:
    """Do not blindly instantiate an unresolved polymorphic carrier."""
    try:
        for part in split_top_level_arrows(type_text)[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder is not None and domain in binder.names:
                    return True
    except ValueError:
        return True
    return False


def _plain_function_argument(type_text: str) -> bool:
    """Keep ordinary-map specialization separate from higher-order inference.

    Passing polymorphic or dependent functions to an ordinary map parameter
    invents unconstrained families. Leave that search to the general fallback.
    """
    try:
        parts = split_top_level_arrows(type_text)
        result_names = set(re.findall(r"[^\s(){}⦃⦄:→]+", parts[-1]))
        for part in parts[:-1]:
            for group in split_adjacent_binders(part) or (part,):
                binder = parse_named_binder(group)
                if binder is not None and (
                    binder.visibility != "explicit"
                    or result_names.intersection(binder.names)
                ):
                    return False
    except ValueError:
        return False
    return True


def evidence_applications(
    terms: tuple[EvidenceTerm, ...],
    declarations: tuple[tuple[str, str], ...],
    *,
    endpoint_terms: frozenset[str],
    relation_heads: frozenset[str],
) -> Iterator[EvidenceApplication]:
    """Project ready structured inputs, then apply their observed functions.

    Exact text/head tests order a conservative proposal fragment only. They
    cannot establish definitional equality or inhabitance. In particular,
    dependent field types are never reconstructed by string substitution.
    """
    values = tuple(
        term
        for term in terms
        if implicit_value_type(term.type_text) is not None
        and not result_head(term.type_text).startswith("Set")
        and result_head(term.type_text) not in relation_heads
    )
    functions = tuple(term for term in terms if explicit_domains(term.type_text))
    for function in functions:
        domain = explicit_domains(function.type_text)[0]
        if _flexible_domain(function.type_text, domain):
            continue
        normalized_domain = normalize_type_text(strip_outer_parentheses(domain))
        domain_head = _evidence_application_head(domain)
        for value in sorted(
            values,
            key=lambda t: (t.expression not in endpoint_terms, t.depth, t.expression),
        ):
            checkpoint()
            exact = (
                normalize_type_text(
                    strip_outer_parentheses(implicit_value_type(value.type_text) or "")
                )
                == normalized_domain
            )
            # An observed function may still quantify hidden indices that
            # its next explicit argument determines. Textual equality cannot
            # instantiate those binders. A common structured head proposes
            # the application; Agda must check the actual dependent indices.
            if not exact and not (
                domain_head is not None
                and domain_head == _evidence_application_head(value.type_text)
            ):
                continue
            yield EvidenceApplication(function, (value,))
    for name, ty in declarations:
        checkpoint()
        domains = explicit_domains(ty)
        if not domains:
            continue
        if top_level_arrow_count(domains[0]):
            for function in functions:
                if _plain_function_argument(function.type_text) and len(
                    explicit_domains(function.type_text)
                ) == len(explicit_domains(domains[0])):
                    yield EvidenceApplication(EvidenceTerm(name, ty), (function,))
                    # The function may not determine parameters appearing
                    # only in the following structured input. Infer this
                    # supported prefix together instead of retaining an
                    # underconstrained partial application's guessed type.
                    if (
                        len(domains) > 1
                        and not top_level_arrow_count(domains[1])
                        and len(split_top_level_application(domains[1])) > 1
                    ):
                        for value in values:
                            checkpoint()
                            if _evidence_application_head(
                                value.type_text
                            ) == _evidence_application_head(domains[1]):
                                yield EvidenceApplication(
                                    EvidenceTerm(name, ty), (function, value)
                                )
            continue
        domain_head = _evidence_application_head(domains[0]) or result_head(domains[0])
        if domain_head in relation_heads or _flexible_domain(ty, domains[0]):
            continue
        for value in values:
            if (
                _evidence_application_head(value.type_text)
                or result_head(value.type_text)
            ) == domain_head:
                yield EvidenceApplication(EvidenceTerm(name, ty), (value,))


def _evidence_application_head(type_text: str) -> str | None:
    """Compare supported prefix/infix applications without treating operands as heads.

    This is a syntactic proposal hint, not a normalization or equality claim.
    Unknown/malformed observations have no recognized application head.
    """
    try:
        value_type = implicit_value_type(type_text)
        if value_type is None:
            return None
        relation = parse_relation(value_type)
        if relation is not None:
            return binary_mixfix_head(relation.operator)
        parts = split_top_level_application(value_type)
        return strip_outer_parentheses(parts[0]) if len(parts) > 1 else None
    except ValueError:
        return None


def ready_evidence_declarations(
    goal_type: str,
    terms: tuple[EvidenceTerm, ...],
    declarations: tuple[tuple[str, str], ...],
) -> Iterator[tuple[str, str]]:
    """Offer supplied maps and consumers supported by the current context.

    Specializing a map with an existing ordinary function can expose a useful
    intermediate type without inventing a polymorphic function argument. A
    supplied consumer can then connect that evidence to the goal. These are
    shape-based proposals only: the caller must infer every application in the
    exact kernel context, and retain no type containing unresolved metavariables.
    No declarations are discovered here and no constructor law is assumed.
    """
    try:
        goal_head = result_head(goal_type)
    except ValueError:
        return
    function_arities: set[int] = set()
    value_heads: set[str] = set()
    for term in terms:
        checkpoint()
        try:
            if result_head(term.type_text).startswith("Set"):
                continue
        except ValueError:
            continue
        domains = explicit_domains(term.type_text)
        if domains and _plain_function_argument(term.type_text):
            function_arities.add(len(domains))
        head = _evidence_application_head(term.type_text)
        if head is not None:
            value_heads.add(head)
    relevant_heads = {goal_head, *value_heads}
    for name, ty in declarations:
        checkpoint()
        domains = explicit_domains(ty)
        if not domains:
            continue
        if top_level_arrow_count(domains[0]):
            if len(explicit_domains(domains[0])) in function_arities and any(
                _evidence_application_head(domain) in value_heads
                for domain in domains[1:]
            ):
                yield name, ty
        elif (
            result_head(ty) in relevant_heads
            and _evidence_application_head(domains[0]) in value_heads
        ):
            yield name, ty
