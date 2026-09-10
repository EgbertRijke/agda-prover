"""Decode the opt-in Agda 2.8 live-scope feature protocol at the gateway."""

from __future__ import annotations

import json

from ..resource_budget import checkpoint
from ..retrieval import (
    QUERY_NORMALIZATION_POLICY,
    TYPE_SPINE_HEAD_POLICY,
    AllowedDependencies,
    AllowedPremise,
    AllowedPremiseSet,
    NormalizedQueryView,
    RetrievalQuery,
    ScopedPremises,
    TypeFamilyQueryView,
    TypeFeatures,
    TypeSpineWork,
    name_fragments,
)
from .contracts import StateToken, stable_hash

SCHEMA = "agdaprover.live-scope.v6"
FEATURE_POLICY = "agda-term-body-head-symbol-arity-v1"
TYPE_VIEW_POLICY = "agda-normalise-contextual-type-v1"
MARKER = "agdaprover:scoped-retrieval:v6:"
DEPENDENCY_SCHEMA = "agdaprover.live-scope.v7"
DEPENDENCY_POLICY = "permitted-clause-rhs-references-v1"
DEPENDENCY_MARKER = "agdaprover:scoped-retrieval:v7:"
RESOURCE_SCHEMA = "agdaprover.live-scope-resource.v1"
QUERY_VIEWS_SCHEMA = "agdaprover.live-scope.v8"
DEPENDENCY_QUERY_VIEWS_SCHEMA = "agdaprover.live-scope.v9"
QUERY_VIEWS_MARKER = "agdaprover:scoped-retrieval:v8:"
DEPENDENCY_QUERY_VIEWS_MARKER = "agdaprover:scoped-retrieval:v9:"
TYPE_FAMILY_SCHEMA = "agdaprover.live-scope.v10"
DEPENDENCY_TYPE_FAMILY_SCHEMA = "agdaprover.live-scope.v11"
TYPE_FAMILY_MARKER = "agdaprover:scoped-retrieval:v10:"
DEPENDENCY_TYPE_FAMILY_MARKER = "agdaprover:scoped-retrieval:v11:"
TYPE_HEADS_SCHEMA = "agdaprover.live-scope.v12"
DEPENDENCY_TYPE_HEADS_SCHEMA = "agdaprover.live-scope.v13"
TYPE_HEADS_MARKER = "agdaprover:scoped-retrieval:v12:"
DEPENDENCY_TYPE_HEADS_MARKER = "agdaprover:scoped-retrieval:v13:"
TYPE_HEADS_POLICY = TYPE_SPINE_HEAD_POLICY


def scope_schema(
    include_dependencies: bool,
    normalize_query: bool,
    type_family_query: bool = False,
    type_spine_heads: bool = False,
) -> str:
    if type_spine_heads:
        return (
            DEPENDENCY_TYPE_HEADS_SCHEMA if include_dependencies else TYPE_HEADS_SCHEMA
        )
    if type_family_query:
        return (
            DEPENDENCY_TYPE_FAMILY_SCHEMA
            if include_dependencies
            else TYPE_FAMILY_SCHEMA
        )
    if normalize_query:
        return (
            DEPENDENCY_QUERY_VIEWS_SCHEMA
            if include_dependencies
            else QUERY_VIEWS_SCHEMA
        )
    return DEPENDENCY_SCHEMA if include_dependencies else SCHEMA


def _validate_request(
    excluded: frozenset[str],
    output_bytes: int,
    include_dependencies: bool,
    normalize_query: bool = False,
    type_family_query: bool = False,
    type_spine_heads: bool = False,
) -> None:
    if type(include_dependencies) is not bool:
        raise ValueError("invalid dependency capability flag")
    if type(normalize_query) is not bool:
        raise ValueError("invalid query normalization capability flag")
    if type(type_family_query) is not bool:
        raise ValueError("invalid type-family query capability flag")
    if type(type_spine_heads) is not bool:
        raise ValueError("invalid type-spine head capability flag")
    if sum((normalize_query, type_family_query, type_spine_heads)) > 1:
        raise ValueError("query reduction policies are mutually exclusive")
    if type(output_bytes) is not int or output_bytes <= 0:
        raise ValueError("invalid live-scope output reservation")
    if type(excluded) is not frozenset:
        raise ValueError("invalid live-scope exclusion set")
    for name in excluded:
        checkpoint()
        if not isinstance(name, str) or not name or "\0" in name:
            raise ValueError("invalid live-scope exclusion set")


def exclusions_payload(
    excluded: frozenset[str],
    *,
    output_bytes: int,
    include_dependencies: bool = False,
    normalize_query: bool = False,
    type_family_query: bool = False,
    type_spine_heads: bool = False,
) -> str:
    _validate_request(
        excluded,
        output_bytes,
        include_dependencies,
        normalize_query,
        type_family_query,
        type_spine_heads,
    )
    payload = json.dumps(
        {"excluded_names": sorted(excluded), "output_bytes": output_bytes},
        ensure_ascii=False,
    )
    checkpoint()
    marker = (
        (DEPENDENCY_TYPE_HEADS_MARKER if include_dependencies else TYPE_HEADS_MARKER)
        if type_spine_heads
        else (
            DEPENDENCY_TYPE_FAMILY_MARKER
            if include_dependencies
            else TYPE_FAMILY_MARKER
        )
        if type_family_query
        else (
            DEPENDENCY_QUERY_VIEWS_MARKER
            if include_dependencies
            else QUERY_VIEWS_MARKER
        )
        if normalize_query
        else (DEPENDENCY_MARKER if include_dependencies else MARKER)
    )
    return marker + payload


def decode_resource_limit(
    value: object,
    *,
    goal_id: int,
    output_bytes: int,
    include_dependencies: bool,
    normalize_query: bool = False,
    type_family_query: bool = False,
    type_spine_heads: bool = False,
) -> int:
    """Validate a complete resource refusal, never a partial scope or rejection."""
    _validate_request(
        frozenset(),
        output_bytes,
        include_dependencies,
        normalize_query,
        type_family_query,
        type_spine_heads,
    )
    if (
        type(goal_id) is not int
        or goal_id < 0
        or not isinstance(value, dict)
        or set(value)
        != {
            "kind",
            "schema_version",
            "request_schema",
            "interaction_id",
            "resource",
            "limit",
            "observed_lower_bound",
        }
        or value["kind"] != "AgdaProverScopeResource"
        or value["schema_version"] != RESOURCE_SCHEMA
        or value["request_schema"]
        != scope_schema(
            include_dependencies, normalize_query, type_family_query, type_spine_heads
        )
        or type(value["interaction_id"]) is not int
        or value["interaction_id"] != goal_id
        or value["resource"] != "output-bytes"
        or type(value["limit"]) is not int
        or value["limit"] != output_bytes
        or type(value["observed_lower_bound"]) is not int
        or value["observed_lower_bound"] <= output_bytes
    ):
        raise ValueError("invalid live-scope resource refusal")
    return value["observed_lower_bound"]


def _features(value: object) -> TypeFeatures:
    if (
        not isinstance(value, dict)
        or set(value) != {"result_head", "symbols", "arity"}
        or not isinstance(value["symbols"], list)
    ):
        raise ValueError("invalid live-scope type features")
    return TypeFeatures(value["result_head"], tuple(value["symbols"]), value["arity"])


def _type_spine(value: object, features: TypeFeatures) -> int:
    if (
        not isinstance(value, dict)
        or set(value)
        != {
            "status",
            "head_reductions",
            "conversion_checked",
            "raw_result_head",
            "raw_arity",
        }
        or type(value["status"]) is not str
        or value["status"] not in {"checked", "kernel-rejected"}
        or value["conversion_checked"] is not (value["status"] == "checked")
        or type(value["head_reductions"]) is not int
        or value["head_reductions"] < 0
    ):
        raise ValueError("invalid checked type-spine evidence")
    raw = TypeFeatures(value["raw_result_head"], features.symbols, value["raw_arity"])
    if value["status"] == "kernel-rejected" and raw != features:
        raise ValueError("rejected type-spine evidence changed raw features")
    if value["status"] == "checked" and value["head_reductions"] != features.arity + 1:
        raise ValueError("incomplete result-spine traversal")
    return value["head_reductions"]


def _omissions(value: object) -> set[str]:
    if not isinstance(value, dict) or set(value) != {"ambiguous", "unnameable"}:
        raise ValueError("invalid closed live-scope omissions")
    omitted: set[str] = set()
    for aliases in value.values():
        if not isinstance(aliases, list):
            raise ValueError("invalid live-scope omission array")
        previous = None
        for alias in aliases:
            checkpoint()
            if (
                not isinstance(alias, str)
                or not alias
                or "\0" in alias
                or (previous is not None and previous >= alias)
                or alias in omitted
            ):
                raise ValueError("invalid or overlapping live-scope omission")
            omitted.add(alias)
            previous = alias
    return omitted


def decode_scope(
    value: object,
    *,
    state: StateToken,
    goal_id: int,
    excluded_names: frozenset[str],
    adapter_sha256: str,
    output_bytes: int,
    include_dependencies: bool = False,
    normalize_query: bool = False,
    type_family_query: bool = False,
    type_spine_heads: bool = False,
) -> ScopedPremises:
    AllowedPremiseSet(adapter_sha256, ())
    if type(goal_id) is not int or goal_id < 0:
        raise ValueError("invalid live-scope goal identity")
    _validate_request(
        excluded_names,
        output_bytes,
        include_dependencies,
        normalize_query,
        type_family_query,
        type_spine_heads,
    )
    fields = {
        "kind",
        "schema_version",
        "feature_policy",
        "type_view_policy",
        "interaction_id",
        "excluded_names",
        "omitted_aliases",
        "target",
        "declarations",
        "structure_nodes",
        "output_bytes",
    }
    if include_dependencies:
        fields |= {"dependency_policy", "dependency_nodes"}
    if normalize_query:
        fields.add("normalized_query")
    if type_family_query:
        fields.add("type_family_query")
    if type_spine_heads:
        fields.add("type_spine")
    if not isinstance(value, dict) or set(value) != fields:
        raise ValueError("invalid closed live-scope record")
    if (
        value["kind"] != "AgdaProverScope"
        or value["schema_version"]
        != scope_schema(
            include_dependencies, normalize_query, type_family_query, type_spine_heads
        )
        or value["feature_policy"]
        != (TYPE_HEADS_POLICY if type_spine_heads else FEATURE_POLICY)
        or value["type_view_policy"] != TYPE_VIEW_POLICY
        or type(value["interaction_id"]) is not int
        or value["interaction_id"] != goal_id
        or value["excluded_names"] != sorted(excluded_names)
        or type(value["output_bytes"]) is not int
        or value["output_bytes"] != output_bytes
    ):
        raise ValueError("live-scope request/response mismatch")
    if include_dependencies and (
        value["dependency_policy"] != DEPENDENCY_POLICY
        or type(value["structure_nodes"]) is not int
        or type(value["dependency_nodes"]) is not int
        or not 0 <= value["dependency_nodes"] <= value["structure_nodes"]
    ):
        raise ValueError("invalid live-scope dependency policy/work count")
    normalized_target = None
    if normalize_query:
        normalized = value["normalized_query"]
        if (
            not isinstance(normalized, dict)
            or set(normalized)
            != {"policy", "features", "structure_nodes", "conversion_checked"}
            or normalized["policy"] != QUERY_NORMALIZATION_POLICY
            or normalized["conversion_checked"] is not True
            or type(normalized["structure_nodes"]) is not int
            or type(value["structure_nodes"]) is not int
            or not 0 < normalized["structure_nodes"] <= value["structure_nodes"]
        ):
            raise ValueError("invalid checked query normalization evidence")
        normalized_target = _features(normalized["features"])
    type_family = None
    if type_family_query:
        reduced = value["type_family_query"]
        if (
            not isinstance(reduced, dict)
            or set(reduced)
            != {
                "policy",
                "status",
                "features",
                "structure_nodes",
                "conversion_checked",
                "term_visits",
                "type_position_reductions",
            }
            or type(reduced["status"]) is not str
            or reduced["conversion_checked"]
            is not (reduced["status"] != "kernel-rejected")
            or type(reduced["structure_nodes"]) is not int
            or type(value["structure_nodes"]) is not int
            or not 0 <= reduced["structure_nodes"] <= value["structure_nodes"]
            or (reduced["structure_nodes"] == 0)
            != (reduced["status"] == "kernel-rejected")
        ):
            raise ValueError("invalid type-family query evidence")
        type_family = TypeFamilyQueryView(
            _features(reduced["features"]) if reduced["features"] is not None else None,
            status=reduced["status"],
            policy=reduced["policy"],
            term_visits=reduced["term_visits"],
            type_position_reductions=reduced["type_position_reductions"],
        )
    declarations = value["declarations"]
    if not isinstance(declarations, list):
        raise ValueError("invalid live-scope declaration array")
    omitted = _omissions(value["omitted_aliases"])
    spine_work = (
        _type_spine(value["type_spine"], _features(value["target"]))
        if type_spine_heads
        else 0
    )
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
        if type_spine_heads:
            row_fields.add("type_spine")
        if not isinstance(row, dict) or set(row) != row_fields:
            raise ValueError("invalid live-scope declaration")
        aliases, ty = row["aliases"], row["type"]
        if not isinstance(aliases, list) or not isinstance(ty, str) or not ty:
            raise ValueError("invalid live-scope aliases/type")
        for alias in aliases:
            checkpoint()
            if not isinstance(alias, str) or alias in omitted:
                raise ValueError("omitted or malformed live-scope premise alias")
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
        if type_spine_heads:
            spine_work += _type_spine(row["type_spine"], premise.features)
        if any(
            a in excluded_names or a.rsplit(".", 1)[-1] in excluded_names
            for a in premise.aliases
        ):
            raise ValueError("excluded declaration in live scope")
        premises.append(premise)
        views.append((premise.declaration_id, ty))
    checkpoint()
    if type_spine_heads and (
        type(value["structure_nodes"]) is not int
        or spine_work > value["structure_nodes"]
    ):
        raise ValueError("invalid type-spine work accounting")
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

    def tokens(features: TypeFeatures) -> tuple[str, ...]:
        target_symbols = set(features.symbols)
        return name_fragments(
            tuple(
                sorted(
                    {
                        a
                        for p in allowed.premises
                        if p.declaration_id in target_symbols
                        for a in p.aliases
                    }
                )
            )
        )

    return ScopedPremises(
        allowed,
        RetrievalQuery(
            scope_id,
            target,
            tokens(target),
            normalized=NormalizedQueryView(normalized_target, tokens(normalized_target))
            if normalized_target is not None
            else None,
            type_family=TypeFamilyQueryView(
                type_family.features,
                tokens(type_family.features)
                if type_family.features is not None
                else (),
                type_family.status,
                type_family.policy,
                type_family.term_visits,
                type_family.type_position_reductions,
            )
            if type_family is not None
            else None,
        ),
        tuple(sorted(views)),
        value["structure_nodes"],
        AllowedDependencies(scope_id, tuple(sorted(references)))
        if include_dependencies
        else None,
        type_spine_work=TypeSpineWork(
            len(premises) + 1,
            spine_work,
            sum(
                v["status"] == "kernel-rejected"
                for v in [value["type_spine"], *(r["type_spine"] for r in declarations)]
            ),
        )
        if type_spine_heads
        else None,
    )
