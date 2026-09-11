"""Goal-directed composition of supplied terms, independent of type families.

Surface matches are proposal hints, never inferred types. Keep the original
quantified signatures on supplied values, leave derived types unknown, and
check the whole application in Agda.
This joins available producers to consumers before lexical shortlisting can
discard the connecting declaration. It does not invent symmetry or other laws.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import replace
from itertools import product

from ..contracts import GoalInfo
from ..premise_search import (
    ScopePremiseAction,
    premise_expected_arguments,
    premise_result_application,
    premise_result_bindings_consistent,
)
from ..resource_budget import checkpoint
from ..type_syntax import normalize_type_text, strip_outer_delimiters
from .evidence import EvidenceApplication, EvidenceTerm, implicit_value_type


def supported_applications(
    goal: GoalInfo,
    actions: tuple[ScopePremiseAction, ...],
    *,
    excluded_names: frozenset[str] = frozenset(),
    poll: Callable[[], None] = checkpoint,
) -> Iterator[EvidenceApplication]:
    """Join result-determined input types to available argument expressions.

    There is no requirement on the number of operands or on their type families.
    Leaves may be whole function values, hidden-parameter values, or applications
    whose explicit arguments are fixed by the requested input type. Unresolved
    dependencies and binder-sensitive substitutions remain ordinary search work.
    The caller owns visibility, finite-batch scheduling and kernel checking.
    """
    actions = tuple(
        a
        for a in actions
        if a.name not in excluded_names
        and a.name.rsplit(".", 1)[-1] not in excluded_names
    )
    # Several consumers can request the same input. Reuse only this pure,
    # invocation-local matching work; never cache a checker acceptance here.
    leaves: dict[str, tuple[EvidenceTerm, ...]] = {}

    def inputs(target: str) -> tuple[EvidenceTerm, ...]:
        try:
            key = normalize_type_text(strip_outer_delimiters(target))
        except ValueError:
            return ()
        if key in leaves:
            return leaves[key]
        needed = replace(goal, target=target)
        found: dict[str, EvidenceTerm] = {}
        for source in actions:
            poll()
            try:
                exact = (
                    normalize_type_text(strip_outer_delimiters(source.type_text)) == key
                )
                expression = (
                    source.expression
                    if exact
                    or (
                        implicit_value_type(source.type_text) is not None
                        and premise_result_bindings_consistent(needed, source)
                    )
                    else premise_result_application(
                        needed, source, excluded_names=excluded_names
                    )
                )
            except ValueError:
                # Unsupported surface syntax loses this hint, not ordinary
                # kernel-driven search. Cancellation/resource errors propagate.
                continue
            if expression is not None:
                found.setdefault(
                    expression,
                    EvidenceTerm(
                        expression,
                        source.type_text if expression == source.expression else "",
                        depth=int(expression != source.expression),
                    ),
                )
        leaves[key] = tuple(found.values())
        return leaves[key]

    for consumer in actions:
        poll()
        try:
            domains = premise_expected_arguments(goal, consumer)
        except ValueError:
            continue
        if not domains:
            continue
        operands = tuple(inputs(domain) for domain in domains)
        if not all(operands):
            continue
        for arguments in product(*operands):
            poll()
            yield EvidenceApplication(
                EvidenceTerm(consumer.expression, consumer.type_text), arguments
            )
