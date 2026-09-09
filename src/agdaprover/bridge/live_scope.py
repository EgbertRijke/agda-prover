"""Decode the opt-in Agda 2.8 live-scope feature protocol at the gateway."""

from __future__ import annotations

import json

from ..resource_budget import checkpoint
from ..retrieval import (
    AllowedDependencies,
    AllowedPremise,
    AllowedPremiseSet,
    RetrievalQuery,
    ScopedPremises,
    TypeFeatures,
    name_fragments,
)
from .contracts import StateToken, stable_hash

SCHEMA = "agdaprover.live-scope.v2"
FEATURE_POLICY = "agda-term-body-head-symbol-arity-v1"
TYPE_VIEW_POLICY = "agda-normalise-contextual-type-v1"
MARKER = "agdaprover:scoped-retrieval:v2:"
DEPENDENCY_SCHEMA = "agdaprover.live-scope.v3"
DEPENDENCY_POLICY = "permitted-clause-rhs-references-v1"
DEPENDENCY_MARKER = "agdaprover:scoped-retrieval:v3:"


def exclusions_payload(
    excluded: frozenset[str], *, include_dependencies: bool = False
) -> str:
    if type(include_dependencies) is not bool:
        raise ValueError("invalid dependency capability flag")
    if (
        type(excluded) is not frozenset
        or len(excluded) > 5000
        or any(
            not isinstance(n, str) or not n or len(n) > 65536 or "\0" in n
            for n in excluded
        )
    ):
        raise ValueError("invalid live-scope exclusion set")
    payload = json.dumps(sorted(excluded), ensure_ascii=False)
    if len(payload) > 65536:
        raise ValueError("live-scope exclusion limit")
    return (DEPENDENCY_MARKER if include_dependencies else MARKER) + payload


def _features(value: object) -> TypeFeatures:
    if (
        not isinstance(value, dict)
        or set(value) != {"result_head", "symbols", "arity"}
        or not isinstance(value["symbols"], list)
    ):
        raise ValueError("invalid live-scope type features")
    return TypeFeatures(value["result_head"], tuple(value["symbols"]), value["arity"])


def decode_scope(
    value: object,
    *,
    state: StateToken,
    goal_id: int,
    excluded_names: frozenset[str],
    adapter_sha256: str,
    include_dependencies: bool = False,
) -> ScopedPremises:
    AllowedPremiseSet(adapter_sha256, ())
    if type(goal_id) is not int or goal_id < 0:
        raise ValueError("invalid live-scope goal identity")
    exclusions_payload(excluded_names, include_dependencies=include_dependencies)
    fields = {
        "kind",
        "schema_version",
        "feature_policy",
        "type_view_policy",
        "interaction_id",
        "excluded_names",
        "target",
        "declarations",
        "structure_nodes",
    }
    if include_dependencies:
        fields |= {"dependency_policy", "dependency_nodes"}
    if not isinstance(value, dict) or set(value) != fields:
        raise ValueError("invalid closed live-scope record")
    if (
        value["kind"] != "AgdaProverScope"
        or value["schema_version"]
        != (DEPENDENCY_SCHEMA if include_dependencies else SCHEMA)
        or value["feature_policy"] != FEATURE_POLICY
        or value["type_view_policy"] != TYPE_VIEW_POLICY
        or type(value["interaction_id"]) is not int
        or value["interaction_id"] != goal_id
        or value["excluded_names"] != sorted(excluded_names)
    ):
        raise ValueError("live-scope request/response mismatch")
    if include_dependencies and (
        value["dependency_policy"] != DEPENDENCY_POLICY
        or type(value["structure_nodes"]) is not int
        or type(value["dependency_nodes"]) is not int
        or not 0 <= value["dependency_nodes"] <= value["structure_nodes"]
    ):
        raise ValueError("invalid live-scope dependency policy/work count")
    declarations = value["declarations"]
    if not isinstance(declarations, list):
        raise ValueError("invalid live-scope declaration array")
    premises, views, references = [], [], []
    for row in declarations:
        checkpoint()
        row_fields = {
            "id",
            "aliases",
            "type",
            "features",
        }
        if include_dependencies:
            row_fields.add("rhs_dependencies")
        if not isinstance(row, dict) or set(row) != row_fields:
            raise ValueError("invalid live-scope declaration")
        aliases, ty = row["aliases"], row["type"]
        if not isinstance(aliases, list) or not isinstance(ty, str) or not ty:
            raise ValueError("invalid live-scope aliases/type")
        if include_dependencies:
            refs = row["rhs_dependencies"]
            if refs is not None and not isinstance(refs, list):
                raise ValueError("invalid live-scope dependency array")
            previous = None
            for ref in refs or ():
                checkpoint()
                if (
                    not isinstance(ref, str)
                    or not ref
                    or "\0" in ref
                    or (previous is not None and previous >= ref)
                ):
                    raise ValueError("invalid live-scope dependency identity")
                previous = ref
            references.append((row["id"], tuple(refs) if refs is not None else None))
        premise = AllowedPremise(
            row["id"],
            tuple(aliases),
            _features(row["features"]),
            "contextual",
            stable_hash({"state": state.to_dict(), "declaration": row}),
        )
        if any(
            a in excluded_names or a.rsplit(".", 1)[-1] in excluded_names
            for a in premise.aliases
        ):
            raise ValueError("excluded declaration in live scope")
        premises.append(premise)
        views.append((premise.declaration_id, ty))
    checkpoint()
    scope_id = stable_hash(
        {
            "state": state.to_dict(),
            "adapter_sha256": adapter_sha256,
            "observation": value,
        }
    )
    allowed = AllowedPremiseSet(
        scope_id, tuple(sorted(premises, key=lambda p: p.declaration_id))
    )
    target = _features(value["target"])
    target_symbols = set(target.symbols)
    query_aliases = tuple(
        sorted(
            {
                a
                for p in allowed.premises
                if p.declaration_id in target_symbols
                for a in p.aliases
            }
        )
    )
    return ScopedPremises(
        allowed,
        RetrievalQuery(scope_id, target, name_fragments(query_aliases)),
        tuple(sorted(views)),
        value["structure_nodes"],
        AllowedDependencies(scope_id, tuple(sorted(references)))
        if include_dependencies
        else None,
    )
