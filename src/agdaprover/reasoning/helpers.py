"""Finite local helper proposals using Agda's inferred helper telescope.

This is function synthesis, not an assumed relation law. Constructor patterns
come from the live signature; coverage, indices and every application are
checked by Agda. The caller owns scheduling, accounting and final validation.
"""

from collections.abc import Iterator, Mapping

from ..notation import render_application
from ..resource_budget import checkpoint
from ..type_syntax import explicit_domains


def helper_bodies(
    signature_type: str, constructors: Mapping[int, tuple[str, str]]
) -> Iterator[str]:
    """Propose one-constructor eliminations returning an available argument.

    The telescope can contain arbitrary implicit/instance arguments, indices and
    function-valued fields. Hidden arguments are left for Agda to infer. Missing
    or multi-constructor cases are not claimed exhaustive by this finite fragment.
    """
    domains = explicit_domains(signature_type)
    names = tuple(f"helperArg{i}" for i in range(len(domains)))
    for position, (constructor, constructor_type) in constructors.items():
        checkpoint()
        fields = tuple(
            f"helperField{i}" for i in range(len(explicit_domains(constructor_type)))
        )
        pattern = render_application(constructor, fields)
        patterns = list(names)
        patterns[position] = f"({pattern})" if fields else pattern
        outputs = (*fields, *(n for i, n in enumerate(names) if i != position))
        for output in reversed(outputs):
            yield "λ { " + " ".join(patterns) + " → " + output + " }"
