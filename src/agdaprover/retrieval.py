"""Pure symbolic retrieval over an already-authorized, immutable goal scope.

The caller owns scope authority. This module cannot inspect an unfiltered
catalogue, expand visibility, elaborate an alias, or certify a proof.
"""

from __future__ import annotations

import hashlib
import heapq
import json
import math
import re
from collections import Counter, defaultdict
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import InitVar, dataclass, field, replace
from types import MappingProxyType
from typing import Any, TypeVar

from .resource_budget import checkpoint

INDEX_SCHEMA = "agdaprover.allowed-premise-index.v1"
RESULT_SCHEMA = "agdaprover.symbolic-retrieval.v1"
POLICY = "head-symbol-arity-lexical-v1"
DEPENDENCY_POLICY = "head-dependency-symbol-arity-lexical-v1"
QUERY_SYMBOL_POLICY = "head-symbol-arity-lexical-query-symbol-interleave-v1"
DEPENDENCY_QUERY_SYMBOL_POLICY = (
    "head-dependency-symbol-arity-lexical-query-symbol-interleave-v1"
)
SYMBOL_RARITY_POLICY = "head-symbol-arity-lexical-query-symbol-rarity-interleave-v1"
DEPENDENCY_SYMBOL_RARITY_POLICY = (
    "head-dependency-symbol-arity-lexical-query-symbol-rarity-interleave-v1"
)
QUERY_VIEWS_POLICY = "raw-normalized-query-interleave-v1"
QUERY_NORMALIZATION_POLICY = "agda-normalise-query-type-v1"
TYPE_FAMILY_QUERY_POLICY = "agda-type-family-whnf-query-v1"
TYPE_FAMILY_VIEWS_POLICY = "raw-stable-type-family-query-interleave-v1"
DEPENDENCY_SCHEMA = "agdaprover.allowed-dependencies.v1"
PROGRESSIVE_POLICY = "scoped-progressive-premises-v3"
PROGRESSIVE_WIDTHS = (8, 32, 128, 512)
_T = TypeVar("_T")


def _checked(values: Iterable[_T]) -> Iterator[_T]:
    """Poll the controller's envelope without turning shape into validity.

    The controller owns CPU/RSS accounting; no process or scope authority lives
    here. Batching amortizes polling in wide postings while empty work and
    short operations still observe an already exhausted envelope.
    """
    checkpoint()
    for count, value in enumerate(values, 1):
        if count % 256 == 0:
            checkpoint()
        yield value
    checkpoint()


def _digest(value: object) -> str:
    # These closed feature records have fixed schema nesting, not recursive
    # Agda terms. Use the stdlib's faster incremental encoder here; no whole
    # index-sized wire copy or mathematical-depth restriction is necessary.
    digest = hashlib.sha256()
    encoder = json.JSONEncoder(
        ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False
    )
    for chunk in _checked(encoder.iterencode(value)):
        digest.update(chunk.encode())
    return digest.hexdigest()


def _hash(value: str) -> None:
    if not isinstance(value, str) or re.fullmatch("[0-9a-f]{64}", value) is None:
        raise ValueError("retrieval identity must be a SHA256 digest")


def _text(value: str) -> None:
    if not isinstance(value, str) or not value or "\0" in value:
        raise ValueError("retrieval text must be nonempty without NUL")


def _strings(values: tuple[str, ...]) -> None:
    if type(values) is not tuple:
        raise ValueError("retrieval features must be an immutable tuple")
    previous = None
    for value in _checked(values):
        _text(value)
        if previous is not None and previous >= value:
            raise ValueError("retrieval features must be unique and sorted")
        previous = value


def _record(value: object, fields: set[str]) -> dict[str, Any]:
    checkpoint()
    if not isinstance(value, dict) or set(value) != fields:
        raise ValueError("invalid closed retrieval record")
    return value


def _array(value: object) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError("invalid retrieval array")
    return value


def name_fragments(aliases: tuple[str, ...]) -> tuple[str, ...]:
    """Only call on names already exposed by the allowed scope or query."""
    _strings(aliases)
    return tuple(
        sorted(
            {
                part.group().casefold()
                for a in _checked(aliases)
                for part in _checked(re.finditer(r"[^\W_]+", a))
            }
        )
    )


@dataclass(frozen=True)
class TypeFeatures:
    result_head: str | None
    symbols: tuple[str, ...]
    arity: int

    def __post_init__(self) -> None:
        if self.result_head is not None:
            _text(self.result_head)
        _strings(self.symbols)
        if type(self.arity) is not int or self.arity < 0:
            raise ValueError("invalid retrieval type arity")

    def to_dict(self) -> dict[str, object]:
        return {
            "result_head": self.result_head,
            "symbols": list(self.symbols),
            "arity": self.arity,
        }


@dataclass(frozen=True)
class AllowedPremise:
    declaration_id: str
    aliases: tuple[str, ...]
    features: TypeFeatures
    type_basis: str
    type_sha256: str

    def __post_init__(self) -> None:
        _text(self.declaration_id)
        _strings(self.aliases)
        if not self.aliases or not isinstance(self.features, TypeFeatures):
            raise ValueError("premise requires checked aliases and type features")
        if not isinstance(self.type_basis, str) or self.type_basis not in {
            "lifted",
            "normalized-lifted",
            "contextual",
        }:
            raise ValueError("invalid retrieval type evidence basis")
        _hash(self.type_sha256)

    def to_dict(self) -> dict[str, object]:
        return {
            "declaration_id": self.declaration_id,
            "aliases": list(self.aliases),
            "features": self.features.to_dict(),
            "type_basis": self.type_basis,
            "type_sha256": self.type_sha256,
        }


@dataclass(frozen=True)
class AllowedPremiseSet:
    """All ranking inputs, after scope/position/policy filtering by the producer.

    No factory accepting an unfiltered catalogue exists in the ranking layer.
    A digest pins evidence; it does not authenticate an untrusted producer.
    """

    scope_id: str
    premises: tuple[AllowedPremise, ...]

    def __post_init__(self) -> None:
        _hash(self.scope_id)
        if type(self.premises) is not tuple:
            raise ValueError("invalid immutable allowed-premise set")
        if not all(isinstance(p, AllowedPremise) for p in _checked(self.premises)):
            raise ValueError("invalid allowed premise")
        _strings(tuple(p.declaration_id for p in _checked(self.premises)))

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": INDEX_SCHEMA,
            "scope_id": self.scope_id,
            "premises": [p.to_dict() for p in _checked(self.premises)],
        }

    @property
    def index_id(self) -> str:
        return _digest(self.to_dict())

    @classmethod
    def from_dict(
        cls, value: object, *, expected_scope_id: str, expected_index_id: str
    ) -> AllowedPremiseSet:
        """Read only against externally pinned identities, never grant scope."""
        _hash(expected_scope_id)
        _hash(expected_index_id)
        root = _record(value, {"schema_version", "scope_id", "premises"})
        if (
            root["schema_version"] != INDEX_SCHEMA
            or root["scope_id"] != expected_scope_id
        ):
            raise ValueError("retrieval index schema/scope mismatch")
        premises = []
        for item in _checked(_array(root["premises"])):
            row = _record(
                item,
                {"declaration_id", "aliases", "features", "type_basis", "type_sha256"},
            )
            features = _record(row["features"], {"result_head", "symbols", "arity"})
            premises.append(
                AllowedPremise(
                    row["declaration_id"],
                    tuple(_array(row["aliases"])),
                    TypeFeatures(
                        features["result_head"],
                        tuple(_array(features["symbols"])),
                        features["arity"],
                    ),
                    row["type_basis"],
                    row["type_sha256"],
                )
            )
        result = cls(expected_scope_id, tuple(premises))
        if result.index_id != expected_index_id:
            raise ValueError("retrieval index checksum mismatch")
        return result


@dataclass(frozen=True)
class NormalizedQueryView:
    """Gateway-supplied equivalent type in the original interaction telescope.

    This value carries ranking evidence, not conversion or scope authority.
    The producer must check conversion without assigning metas and charge the
    normalization to its request envelope before constructing this view.
    """

    features: TypeFeatures
    tokens: tuple[str, ...] = ()
    policy: str = QUERY_NORMALIZATION_POLICY

    def __post_init__(self) -> None:
        if not isinstance(self.features, TypeFeatures):
            raise ValueError("invalid normalized query type features")
        _strings(self.tokens)
        if self.policy != QUERY_NORMALIZATION_POLICY:
            raise ValueError("unsupported query normalization policy")

    def to_dict(self) -> dict[str, object]:
        return {
            "policy": self.policy,
            "features": self.features.to_dict(),
            "tokens": list(self.tokens),
        }


@dataclass(frozen=True)
class TypeFamilyQueryView:
    """Optional typed reduction evidence, explicitly not a full normal form.

    An unavailable alternate retains raw retrieval. Operational exhaustion and
    cancellation of the whole request are errors, not unavailable evidence.
    Native traversal work is retained even when the alternate is declined.
    """

    features: TypeFeatures | None
    tokens: tuple[str, ...] = ()
    status: str = "checked"
    policy: str = TYPE_FAMILY_QUERY_POLICY
    term_visits: int = 0
    type_position_reductions: int = 0

    def __post_init__(self) -> None:
        _strings(self.tokens)
        if self.policy != TYPE_FAMILY_QUERY_POLICY:
            raise ValueError("unsupported type-family query policy")
        if not isinstance(self.status, str) or self.status not in {
            "checked",
            "kernel-rejected",
            "output-limited",
        }:
            raise ValueError("invalid type-family query status")
        if self.status == "checked":
            if not isinstance(self.features, TypeFeatures):
                raise ValueError("checked type-family query requires features")
        elif self.features is not None or self.tokens:
            raise ValueError("unavailable type-family query cannot supply features")
        if (
            type(self.term_visits) is not int
            or type(self.type_position_reductions) is not int
            or not 0 <= self.type_position_reductions <= self.term_visits
        ):
            raise ValueError("invalid type-family traversal work")

    def classification(self, raw: TypeFeatures, tokens: tuple[str, ...]) -> str:
        """Similarity scheduling only: no premise is rejected by this gate."""
        alternate = self.features
        if alternate is None:
            return self.status
        if raw.result_head is None or alternate.result_head is None:
            return "unknown-head"
        if raw.result_head != alternate.result_head:
            return "changed-head"
        if raw.arity != alternate.arity:
            return "changed-arity"
        if raw == alternate and tokens == self.tokens:
            return "identical"
        return "stable-head-and-arity"

    def to_dict(self) -> dict[str, object]:
        return {
            "policy": self.policy,
            "status": self.status,
            "features": self.features.to_dict() if self.features is not None else None,
            "tokens": list(self.tokens),
            "term_visits": self.term_visits,
            "type_position_reductions": self.type_position_reductions,
        }


@dataclass(frozen=True)
class RetrievalQuery:
    scope_id: str
    features: TypeFeatures
    tokens: tuple[str, ...] = ()
    query_symbol_lane: bool = False
    symbol_rarity_lane: bool = False
    normalized: NormalizedQueryView | None = None
    type_family: TypeFamilyQueryView | None = None

    def __post_init__(self) -> None:
        _hash(self.scope_id)
        if not isinstance(self.features, TypeFeatures):
            raise ValueError("invalid query type features")
        _strings(self.tokens)
        if type(self.query_symbol_lane) is not bool:
            raise ValueError("query-symbol lane must be a Boolean")
        if type(self.symbol_rarity_lane) is not bool:
            raise ValueError("symbol-rarity lane must be a Boolean")
        if self.symbol_rarity_lane and not self.query_symbol_lane:
            raise ValueError("symbol-rarity lane requires the query-symbol lane")
        if self.normalized is not None and not isinstance(
            self.normalized, NormalizedQueryView
        ):
            raise ValueError("invalid normalized query view")
        if self.type_family is not None and not isinstance(
            self.type_family, TypeFamilyQueryView
        ):
            raise ValueError("invalid type-family query view")
        if self.normalized is not None and self.type_family is not None:
            raise ValueError("query reduction policies are mutually exclusive")

    @property
    def query_id(self) -> str:
        return _digest(
            {
                "scope_id": self.scope_id,
                "features": self.features.to_dict(),
                "tokens": self.tokens,
                "policy": SYMBOL_RARITY_POLICY
                if self.symbol_rarity_lane
                else QUERY_SYMBOL_POLICY
                if self.query_symbol_lane
                else POLICY,
                **(
                    {
                        "query_views_policy": QUERY_VIEWS_POLICY,
                        "normalized": self.normalized.to_dict(),
                    }
                    if self.normalized is not None
                    else {}
                ),
                **(
                    {
                        "query_views_policy": TYPE_FAMILY_VIEWS_POLICY,
                        "type_family": self.type_family.to_dict(),
                    }
                    if self.type_family is not None
                    else {}
                ),
            }
        )


@dataclass(frozen=True)
class AllowedDependencies:
    """Permitted clause-reference evidence, never a private proof inventory."""

    scope_id: str
    rhs_references: tuple[tuple[str, tuple[str, ...] | None], ...]

    def __post_init__(self) -> None:
        _hash(self.scope_id)
        if type(self.rhs_references) is not tuple:
            raise ValueError("invalid immutable dependency references")
        ids = []
        for row in _checked(self.rhs_references):
            if type(row) is not tuple or len(row) != 2:
                raise ValueError("invalid dependency reference row")
            identifier, references = row
            _text(identifier)
            ids.append(identifier)
            if references is not None:
                _strings(references)
                if identifier in references:
                    raise ValueError("dependency self reference")
        _strings(tuple(ids))

    def validate(self, allowed: AllowedPremiseSet) -> None:
        checkpoint()
        if self.scope_id != allowed.scope_id or tuple(
            r[0] for r in self.rhs_references
        ) != tuple(p.declaration_id for p in allowed.premises):
            raise ValueError("dependency coverage/scope mismatch")
        members = {p.declaration_id for p in allowed.premises}
        if any(
            r not in members
            for _, refs in _checked(self.rhs_references)
            for r in _checked(refs or ())
        ):
            raise ValueError("forbidden dependency endpoint")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": DEPENDENCY_SCHEMA,
            "scope_id": self.scope_id,
            "rhs_references": [
                {
                    "declaration_id": name,
                    "references": list(refs) if refs is not None else None,
                }
                for name, refs in _checked(self.rhs_references)
            ],
        }

    @property
    def graph_id(self) -> str:
        return _digest(self.to_dict())

    @classmethod
    def from_dict(
        cls, value: object, *, allowed: AllowedPremiseSet, expected_graph_id: str
    ) -> AllowedDependencies:
        _hash(expected_graph_id)
        root = _record(value, {"schema_version", "scope_id", "rhs_references"})
        if root["schema_version"] != DEPENDENCY_SCHEMA:
            raise ValueError("unsupported dependency evidence schema")
        rows = []
        for row in _checked(_array(root["rhs_references"])):
            record = _record(row, {"declaration_id", "references"})
            name, refs = record["declaration_id"], record["references"]
            _text(name)
            references = tuple(_array(refs)) if refs is not None else None
            if references is not None:
                _strings(references)
            rows.append((name, references))
        result = cls(root["scope_id"], tuple(rows))
        result.validate(allowed)
        if result.graph_id != expected_graph_id:
            raise ValueError("dependency evidence checksum mismatch")
        return result


def _index_identity(
    allowed: AllowedPremiseSet, dependencies: AllowedDependencies | None
) -> str:
    if dependencies is None:
        return allowed.index_id
    return _digest(
        {
            "schema_version": "agdaprover.dependency-premise-index.v1",
            "allowed_index_id": allowed.index_id,
            "dependency_graph_id": dependencies.graph_id,
            "policy": DEPENDENCY_POLICY,
        }
    )


def _query_identity(query: RetrievalQuery, dependencies: bool) -> str:
    return (
        _digest(
            {
                "query_id": query.query_id,
                "policy": DEPENDENCY_SYMBOL_RARITY_POLICY
                if query.symbol_rarity_lane
                else DEPENDENCY_QUERY_SYMBOL_POLICY
                if query.query_symbol_lane
                else DEPENDENCY_POLICY,
            }
        )
        if dependencies
        else query.query_id
    )


@dataclass(frozen=True)
class RankedPremise:
    premise: AllowedPremise
    head_match: int
    symbol_overlap: int
    lexical_overlap: int
    arity_distance: int
    dependency_score: int = 0
    query_symbol_match: int = 0
    symbol_rarity: float = 0.0
    query_view: str | None = None
    query_view_rank: int | None = None

    @property
    def sort_key(self) -> tuple[object, ...]:
        return (
            -self.head_match,
            -self.dependency_score,
            -self.symbol_overlap,
            self.arity_distance,
            -self.lexical_overlap,
            self.premise.aliases,
            self.premise.declaration_id,
        )

    def to_dict(
        self,
        rank: int,
        *,
        include_dependencies: bool = False,
        include_query_symbols: bool = False,
        include_symbol_rarity: bool = False,
        include_query_views: bool = False,
    ) -> dict[str, object]:
        return {
            "rank": rank,
            "premise": self.premise.to_dict(),
            **(
                {"query_view": self.query_view, "query_view_rank": self.query_view_rank}
                if include_query_views
                else {}
            ),
            "components": {
                "head_match": self.head_match,
                "symbol_overlap": self.symbol_overlap,
                "lexical_overlap": self.lexical_overlap,
                "arity_distance": self.arity_distance,
                **(
                    {"dependency_score": self.dependency_score}
                    if include_dependencies
                    else {}
                ),
                **(
                    {"query_symbol_match": self.query_symbol_match}
                    if include_query_symbols
                    else {}
                ),
                **(
                    {"symbol_rarity": self.symbol_rarity}
                    if include_symbol_rarity
                    else {}
                ),
            },
        }


@dataclass(frozen=True)
class RetrievalResult:
    index_id: str
    query_id: str
    scope_id: str
    candidate_count: int
    postings_visited: int
    items: tuple[RankedPremise, ...]
    dependency_graph_id: str | None = None
    dependency_postings_visited: int = 0
    query_symbol_lane: bool = False
    symbol_rarity_lane: bool = False
    normalized_query_policy: str | None = None
    query_views_scored: int = 1
    type_family_query_policy: str | None = None
    type_family_classification: str | None = None

    @property
    def has_query_views(self) -> bool:
        return (
            self.normalized_query_policy is not None
            or self.type_family_query_policy is not None
        )

    @property
    def scored_count(self) -> int:
        return self.candidate_count * self.query_views_scored

    @property
    def policy(self) -> str:
        if self.type_family_query_policy is not None:
            base = replace(self, type_family_query_policy=None).policy
            return f"{TYPE_FAMILY_VIEWS_POLICY}/{base}"
        if self.normalized_query_policy is not None:
            base = replace(self, normalized_query_policy=None).policy
            return f"{QUERY_VIEWS_POLICY}/{base}"
        if self.symbol_rarity_lane:
            return (
                DEPENDENCY_SYMBOL_RARITY_POLICY
                if self.dependency_graph_id is not None
                else SYMBOL_RARITY_POLICY
            )
        if self.query_symbol_lane:
            return (
                DEPENDENCY_QUERY_SYMBOL_POLICY
                if self.dependency_graph_id is not None
                else QUERY_SYMBOL_POLICY
            )
        return DEPENDENCY_POLICY if self.dependency_graph_id is not None else POLICY

    def progressive_limits(self) -> tuple[int, ...]:
        """Cumulative widths, stopping once the pinned result is exhausted.

        Empty scope still exposes one empty batch. Reaching the last batch
        says nothing about provability or premises outside the retrieval cap.
        """
        widths = tuple(
            width
            for i, width in enumerate(PROGRESSIVE_WIDTHS)
            if i == 0 or len(self.items) > PROGRESSIVE_WIDTHS[i - 1]
        )
        # The usual 512-result request retains its exact policy. Explicitly
        # larger requests are reachable, not silently hidden after batch four.
        while widths[-1] < len(self.items):
            widths += (min(widths[-1] * 4, len(self.items)),)
        return widths

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": "agdaprover.symbolic-retrieval.v6"
            if self.type_family_query_policy is not None
            else "agdaprover.symbolic-retrieval.v5"
            if self.normalized_query_policy is not None
            else "agdaprover.symbolic-retrieval.v4"
            if self.symbol_rarity_lane
            else "agdaprover.symbolic-retrieval.v3"
            if self.query_symbol_lane
            else "agdaprover.symbolic-retrieval.v2"
            if self.dependency_graph_id is not None
            else RESULT_SCHEMA,
            "policy": self.policy,
            "index_id": self.index_id,
            "query_id": self.query_id,
            "scope_id": self.scope_id,
            "candidate_count": self.candidate_count,
            "scored_count": self.scored_count,
            "postings_visited": self.postings_visited,
            "usage_authority": "ranking-only-requires-agda-elaboration",
            "items": [
                item.to_dict(
                    i,
                    include_dependencies=self.dependency_graph_id is not None,
                    include_query_symbols=self.query_symbol_lane,
                    include_symbol_rarity=self.symbol_rarity_lane,
                    include_query_views=self.has_query_views,
                )
                for i, item in enumerate(self.items, 1)
            ],
            **(
                {
                    "normalized_query_policy": self.normalized_query_policy,
                    "query_views_scored": self.query_views_scored,
                }
                if self.normalized_query_policy is not None
                else {}
            ),
            **(
                {
                    "type_family_query_policy": self.type_family_query_policy,
                    "type_family_classification": self.type_family_classification,
                    "query_views_scored": self.query_views_scored,
                }
                if self.type_family_query_policy is not None
                else {}
            ),
            **(
                {
                    "dependency_graph_id": self.dependency_graph_id,
                    "dependency_postings_visited": self.dependency_postings_visited,
                }
                if self.dependency_graph_id is not None
                else {}
            ),
        }


def _updated_postings(
    previous: Mapping[str, tuple[str, ...]],
    old_rows: Mapping[str, tuple[str, ...]],
    rows: Mapping[str, tuple[str, ...]],
    work: Counter[str],
) -> Mapping[str, tuple[str, ...]]:
    """Copy-on-write inverted rows, including deletions before publication."""
    entries = sum(map(len, rows.values()))
    if not old_rows and not previous:
        # Cold construction has no removals or copy-on-write buckets. Avoid
        # allocating a set for every row and token in this common path.
        collected: dict[str, list[str]] = defaultdict(list)
        for identifier, tokens in _checked(rows.items()):
            for token in _checked(tokens):
                collected[token].append(identifier)
        work["posting_entries_inserted"] += entries
        work["posting_buckets_rebuilt"] += len(collected)
        return MappingProxyType(
            {token: tuple(sorted(ids)) for token, ids in _checked(collected.items())}
        )
    changed: dict[str, set[str]] = {}
    for identifier in _checked(old_rows.keys() | rows.keys()):
        before, after = old_rows.get(identifier, ()), rows.get(identifier, ())
        if before == after:
            continue
        removed, added = set(before) - set(after), set(after) - set(before)
        for token in _checked(removed | added):
            if token not in changed:
                changed[token] = set(previous.get(token, ()))
            if token in removed:
                changed[token].discard(identifier)
            else:
                changed[token].add(identifier)
        work["posting_entries_removed"] += len(removed)
        work["posting_entries_inserted"] += len(added)
    work["posting_buckets_rebuilt"] += len(changed)
    work["posting_buckets_reused"] += len(previous.keys() - changed.keys())
    if not changed:
        return previous
    postings = dict(previous)
    for token, members in _checked(changed.items()):
        if members:
            postings[token] = tuple(sorted(members))
        else:
            postings.pop(token, None)
    return MappingProxyType(postings)


@dataclass(frozen=True)
class SymbolicPremiseIndex:
    allowed: AllowedPremiseSet
    dependencies: AllowedDependencies | None = None
    _previous: InitVar[SymbolicPremiseIndex | None] = None
    _symbols: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    _lexical: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    _symbol_rows: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    _lexical_rows: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    _directed: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    _reverse: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    index_id: str = field(init=False)
    _neighbors: Mapping[str, tuple[str, ...]] = field(init=False, repr=False)
    build_work: Mapping[str, int | str | None] = field(init=False, compare=False)

    def __post_init__(self, _previous: SymbolicPremiseIndex | None) -> None:
        checkpoint()
        if not isinstance(self.allowed, AllowedPremiseSet):
            raise ValueError("index requires an allowed-premise set")
        if self.dependencies is not None:
            if not isinstance(self.dependencies, AllowedDependencies):
                raise ValueError("invalid allowed dependency evidence")
            self.dependencies.validate(self.allowed)
        if _previous is not None and not isinstance(_previous, SymbolicPremiseIndex):
            raise ValueError("invalid predecessor index")
        empty: Mapping[str, tuple[str, ...]] = MappingProxyType({})
        old = (
            {p.declaration_id: p for p in _previous.allowed.premises}
            if _previous
            else {}
        )
        current = {p.declaration_id: p for p in self.allowed.premises}
        work: Counter[str] = Counter(
            dict.fromkeys(
                (
                    "symbol_rows_reused",
                    "lexical_rows_reused",
                    "dependency_rows_reused",
                    "posting_entries_removed",
                    "posting_entries_inserted",
                    "posting_buckets_rebuilt",
                    "posting_buckets_reused",
                    "adjacency_buckets_rebuilt",
                    "adjacency_buckets_reused",
                ),
                0,
            )
        )
        work["declarations_examined"] = len(old.keys() | current.keys())
        work["declarations_removed"] = len(old.keys() - current.keys())
        symbol_rows, lexical_rows = {}, {}
        for identifier, premise in _checked(current.items()):
            before = old.get(identifier)
            if (
                _previous is not None
                and before is not None
                and before.features.symbols == premise.features.symbols
            ):
                symbol_rows[identifier] = _previous._symbol_rows[identifier]
                work["symbol_rows_reused"] += 1
            else:
                symbol_rows[identifier] = premise.features.symbols
            if (
                _previous is not None
                and before is not None
                and before.aliases == premise.aliases
            ):
                lexical_rows[identifier] = _previous._lexical_rows[identifier]
                work["lexical_rows_reused"] += 1
            else:
                lexical_rows[identifier] = name_fragments(premise.aliases)
        for attribute, rows in (("_symbols", symbol_rows), ("_lexical", lexical_rows)):
            row_attribute = (
                "_symbol_rows" if attribute == "_symbols" else "_lexical_rows"
            )
            object.__setattr__(
                self,
                attribute,
                _updated_postings(
                    getattr(_previous, attribute, empty),
                    getattr(_previous, row_attribute, empty),
                    rows,
                    work,
                ),
            )
            object.__setattr__(self, row_attribute, MappingProxyType(rows))
        directed = {}
        if self.dependencies is not None:
            old_refs = (
                dict(_previous.dependencies.rhs_references)
                if _previous and _previous.dependencies
                else {}
            )
            membership_delta = old.keys() ^ current.keys()
            for p, (_, refs) in _checked(
                zip(
                    self.allowed.premises, self.dependencies.rhs_references, strict=True
                )
            ):
                identifier = p.declaration_id
                before = old.get(identifier)
                if (
                    _previous is not None
                    and _previous.dependencies is not None
                    and before is not None
                    and before.features.symbols == p.features.symbols
                    and old_refs[identifier] == refs
                    and membership_delta.isdisjoint(p.features.symbols)
                ):
                    directed[identifier] = _previous._directed[identifier]
                    work["dependency_rows_reused"] += 1
                else:
                    directed[identifier] = tuple(
                        sorted(
                            (
                                (set(p.features.symbols) | set(refs or ()))
                                & current.keys()
                            )
                            - {identifier}
                        )
                    )
        reverse = _updated_postings(
            _previous._reverse if _previous else empty,
            _previous._directed if _previous else empty,
            directed,
            work,
        )
        neighbors = {}
        if self.dependencies is not None:
            for identifier, outgoing in _checked(directed.items()):
                incoming = reverse.get(identifier, ())
                if (
                    _previous
                    and outgoing == _previous._directed.get(identifier)
                    and incoming == _previous._reverse.get(identifier, ())
                ):
                    neighbors[identifier] = _previous._neighbors[identifier]
                    work["adjacency_buckets_reused"] += 1
                else:
                    neighbors[identifier] = tuple(sorted(set(outgoing) | set(incoming)))
                    work["adjacency_buckets_rebuilt"] += 1
        object.__setattr__(self, "_directed", MappingProxyType(directed))
        object.__setattr__(self, "_reverse", reverse)
        object.__setattr__(
            self,
            "_neighbors",
            MappingProxyType(neighbors),
        )
        object.__setattr__(
            self, "index_id", _index_identity(self.allowed, self.dependencies)
        )
        object.__setattr__(
            self,
            "build_work",
            MappingProxyType(
                {
                    "schema_version": "agdaprover.index-build-work.v1",
                    "mode": "incremental" if _previous is not None else "cold",
                    "previous_index_id": _previous.index_id
                    if _previous is not None
                    else None,
                    **work,
                }
            ),
        )

    def updated(
        self,
        allowed: AllowedPremiseSet,
        dependencies: AllowedDependencies | None = None,
    ) -> SymbolicPremiseIndex:
        """Reconcile fresh authorized features, never reuse scope or proof authority."""
        return SymbolicPremiseIndex(allowed, dependencies, self)

    def retrieve(self, query: RetrievalQuery, *, limit: int = 64) -> RetrievalResult:
        checkpoint()
        if (
            not isinstance(query, RetrievalQuery)
            or query.scope_id != self.allowed.scope_id
        ):
            raise ValueError("retrieval query scope does not match pinned index")
        if type(limit) is not int or limit < 1:
            raise ValueError("retrieval limit must be a positive integer")
        if query.normalized is not None or query.type_family is not None:
            return self._retrieve_query_views(query, limit=limit)
        symbols: Counter[str] = Counter()
        lexical: Counter[str] = Counter()
        rarity_weights: dict[str, float] = {}
        population = len(self.allowed.premises)
        average = (
            max(
                1.0,
                sum(len(p.features.symbols) for p in _checked(self.allowed.premises))
                / max(population, 1),
            )
            if query.symbol_rarity_lane
            else 1.0
        )
        visited = 0
        for tokens, postings, counts in (
            (query.features.symbols, self._symbols, symbols),
            (query.tokens, self._lexical, lexical),
        ):
            for token in _checked(tokens):
                rows = postings.get(token, ())
                if query.symbol_rarity_lane and counts is symbols:
                    rarity_weights[token] = math.log1p(
                        (population - len(rows) + 0.5) / (len(rows) + 0.5)
                    )
                counts.update(_checked(rows))
                visited += len(rows)
        dependency_scores: Counter[str] = Counter()
        dependency_visits = 0
        if self.dependencies is not None:
            members = {p.declaration_id for p in self.allowed.premises}
            seeds = [n for n in query.features.symbols if n in members]
            # One bounded bit per allowed query symbol. Propagate all seeds
            # together, not O(seeds * edges) separate breadth-first searches.
            frontier = {name: 1 << i for i, name in enumerate(seeds)}
            seen = dict(frontier)
            dependency_scores.update(dict.fromkeys(seeds, 3))
            for weight in (2, 1):
                reached: dict[str, int] = {}
                for name, mask in _checked(frontier.items()):
                    adjacent = self._neighbors.get(name, ())
                    dependency_visits += len(adjacent)
                    for neighbor in _checked(adjacent):
                        reached[neighbor] = reached.get(neighbor, 0) | mask
                frontier = {}
                for name, mask in _checked(reached.items()):
                    fresh = mask & ~seen.get(name, 0)
                    if fresh:
                        dependency_scores[name] += weight * fresh.bit_count()
                        seen[name] = seen.get(name, 0) | fresh
                        frontier[name] = fresh
        referenced = set(query.features.symbols) if query.query_symbol_lane else set()
        direct: list[RankedPremise] = []

        def candidates(*, collect_direct: bool = False) -> Iterator[RankedPremise]:
            for p in _checked(self.allowed.premises):
                item = RankedPremise(
                    p,
                    int(
                        query.features.result_head is not None
                        and p.features.result_head == query.features.result_head
                    ),
                    symbols[p.declaration_id],
                    lexical[p.declaration_id],
                    abs(p.features.arity - query.features.arity),
                    dependency_scores[p.declaration_id],
                    int(p.declaration_id in referenced),
                    sum(
                        rarity_weights[s]
                        for s in _checked(p.features.symbols)
                        if s in rarity_weights
                    )
                    * 2.2
                    / (1 + 1.2 * (0.25 + 0.75 * len(p.features.symbols) / average))
                    if query.symbol_rarity_lane
                    else 0.0,
                )
                if collect_direct and item.query_symbol_match:
                    direct.append(item)
                yield item

        # Unknown/mismatched heads remain eligible: symbolic similarity is not
        # a unification test, and aliases may require further normalization.
        items = tuple(
            heapq.nsmallest(
                limit, candidates(collect_direct=True), key=lambda p: p.sort_key
            )
        )
        if (query.query_symbol_lane and direct) or query.symbol_rarity_lane:
            # Each lane's first k entries suffice for a k-element merged prefix.
            # In particular, do not truncate the allowed set before finding
            # referenced declarations whose baseline rank lies beyond k.
            lanes = [
                iter(items),
                iter(
                    heapq.nsmallest(limit, _checked(direct), key=lambda p: p.sort_key)
                ),
            ]
            if query.symbol_rarity_lane:
                # A second bounded top-k pass avoids storing/sorting N ranked
                # objects. Posting statistics are collected once, above.
                lanes.append(
                    iter(
                        heapq.nsmallest(
                            limit,
                            candidates(),
                            key=lambda p: (-p.symbol_rarity, p.sort_key),
                        )
                    )
                )
            selected: list[RankedPremise] = []
            emitted: set[str] = set()
            while len(selected) < min(limit, len(self.allowed.premises)):
                checkpoint()
                for lane in lanes:
                    for item in _checked(lane):
                        if item.premise.declaration_id not in emitted:
                            emitted.add(item.premise.declaration_id)
                            selected.append(item)
                            break
                    if len(selected) == limit:
                        break
            items = tuple(selected)
        return RetrievalResult(
            self.index_id,
            _query_identity(query, self.dependencies is not None),
            query.scope_id,
            len(self.allowed.premises),
            visited + dependency_visits,
            items,
            self.dependencies.graph_id if self.dependencies is not None else None,
            dependency_visits,
            query.query_symbol_lane,
            query.symbol_rarity_lane,
        )

    def _retrieve_query_views(
        self, query: RetrievalQuery, *, limit: int
    ) -> RetrievalResult:
        """Two bounded rankings over one index; never a union of scopes.

        Raw goes first. Each view's top k suffices for the merged top k;
        duplicate removal is deterministic and the order is prefix-stable.
        Components and view rank belong to the view that emitted the item.
        """
        view = query.normalized or query.type_family
        assert view is not None
        raw_query = replace(query, normalized=None, type_family=None)
        raw = self.retrieve(raw_query, limit=limit)
        classification = (
            query.type_family.classification(query.features, query.tokens)
            if query.type_family is not None
            else None
        )
        raw = replace(
            raw,
            query_id=_query_identity(query, self.dependencies is not None),
            normalized_query_policy=view.policy
            if query.normalized is not None
            else None,
            type_family_query_policy=view.policy
            if query.type_family is not None
            else None,
            type_family_classification=classification,
        )
        if (
            classification is not None and classification != "stable-head-and-arity"
        ) or (view.features == query.features and view.tokens == query.tokens):
            # Normalization often exposes no new ranking evidence. Do not
            # repeat a full candidate pass merely to give it another label.
            return replace(
                raw,
                items=tuple(
                    replace(item, query_view="raw", query_view_rank=rank)
                    for rank, item in _checked(enumerate(raw.items, 1))
                ),
            )
        assert view.features is not None
        normalized = self.retrieve(
            replace(raw_query, features=view.features, tokens=view.tokens),
            limit=limit,
        )
        lanes = (
            ("raw", iter(enumerate(raw.items, 1))),
            (
                "normalized" if query.normalized is not None else "type-family",
                iter(enumerate(normalized.items, 1)),
            ),
        )
        selected: list[RankedPremise] = []
        emitted: set[str] = set()
        while len(selected) < min(limit, raw.candidate_count):
            checkpoint()
            for name, lane in lanes:
                for rank, item in _checked(lane):
                    if item.premise.declaration_id not in emitted:
                        emitted.add(item.premise.declaration_id)
                        selected.append(
                            replace(item, query_view=name, query_view_rank=rank)
                        )
                        break
                if len(selected) == limit:
                    break
        return replace(
            raw,
            query_id=_query_identity(query, self.dependencies is not None),
            postings_visited=raw.postings_visited + normalized.postings_visited,
            dependency_postings_visited=(
                raw.dependency_postings_visited + normalized.dependency_postings_visited
            ),
            items=tuple(selected),
            query_views_scored=2,
        )


@dataclass(frozen=True)
class ScopedPremises:
    """Checked goal-local ranking inputs with non-authoritative rendering views.

    The gateway owns the exact interaction-state binding. This core value has
    no kernel or process imports and cannot confer action/proof authority.
    """

    allowed: AllowedPremiseSet
    query: RetrievalQuery
    type_views: tuple[tuple[str, str], ...]
    structure_nodes: int
    dependencies: AllowedDependencies | None = None

    def __post_init__(self) -> None:
        checkpoint()
        if not isinstance(self.allowed, AllowedPremiseSet) or not isinstance(
            self.query, RetrievalQuery
        ):
            raise ValueError("invalid scoped retrieval inputs")
        if self.allowed.scope_id != self.query.scope_id:
            raise ValueError("scoped retrieval query/index mismatch")
        if self.dependencies is not None:
            if not isinstance(self.dependencies, AllowedDependencies):
                raise ValueError("invalid scoped dependency evidence")
            self.dependencies.validate(self.allowed)
        if type(self.type_views) is not tuple or any(
            type(row) is not tuple
            or len(row) != 2
            or not all(isinstance(value, str) and value for value in row)
            for row in _checked(self.type_views)
        ):
            raise ValueError("invalid immutable scoped type views")
        if tuple(p.declaration_id for p in self.allowed.premises) != tuple(
            row[0] for row in self.type_views
        ):
            raise ValueError("scoped type views do not cover the allowed set")
        if type(self.structure_nodes) is not int or self.structure_nodes < 0:
            raise ValueError("invalid scoped retrieval work count")

    def declarations(self) -> tuple[tuple[str, str], ...]:
        types = dict(self.type_views)
        return tuple(
            (alias, types[p.declaration_id])
            for p in self.allowed.premises
            for alias in p.aliases
        )

    def index(self) -> SymbolicPremiseIndex:
        return SymbolicPremiseIndex(self.allowed, self.dependencies)

    @property
    def index_id(self) -> str:
        return _index_identity(self.allowed, self.dependencies)

    @property
    def query_id(self) -> str:
        return _query_identity(self.query, self.dependencies is not None)
