"""Ranking diversity cannot change scope authority or legacy result identities."""

from __future__ import annotations

import hashlib
import heapq
import json
import random
import unittest
from dataclasses import replace
from unittest.mock import patch

from agdaprover.retrieval import (
    DEPENDENCY_POLICY,
    DEPENDENCY_QUERY_SYMBOL_POLICY,
    POLICY,
    QUERY_SYMBOL_POLICY,
    AllowedDependencies,
    AllowedPremise,
    AllowedPremiseSet,
    RetrievalQuery,
    SymbolicPremiseIndex,
    TypeFeatures,
)

SCOPE = "0" * 64


def premise(name: str, head: str | None = None) -> AllowedPremise:
    return AllowedPremise(name, (name,), TypeFeatures(head, (), 0), "lifted", "1" * 64)


def index(*premises: AllowedPremise) -> SymbolicPremiseIndex:
    return SymbolicPremiseIndex(
        AllowedPremiseSet(
            SCOPE, tuple(sorted(premises, key=lambda p: p.declaration_id))
        )
    )


def ids(result) -> list[str]:
    return [item.premise.declaration_id for item in result.items]


def interleave(baseline: list[str], references: set[str]) -> list[str]:
    """Deliberately simple full-sort oracle, independent of the top-k merge."""
    lanes = (list(baseline), [name for name in baseline if name in references])
    result: list[str] = []
    while any(lanes):
        for lane in lanes:
            while lane:
                name = lane.pop(0)
                if name not in result:
                    result.append(name)
                    break
    return result


class QuerySymbolRetrievalTests(unittest.TestCase):
    def test_disabled_policy_preserves_legacy_identity_and_serialization(self) -> None:
        query = RetrievalQuery(SCOPE, TypeFeatures("R", ("z",), 0))
        legacy_identity = hashlib.sha256(
            json.dumps(
                {
                    "scope_id": SCOPE,
                    "features": query.features.to_dict(),
                    "tokens": [],
                    "policy": POLICY,
                },
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode()
        ).hexdigest()
        self.assertEqual(query.query_id, legacy_identity)
        scoped = index(premise("a", "R"), premise("z", "Q"))
        result = scoped.retrieve(query)
        self.assertEqual(
            result, scoped.retrieve(replace(query, query_symbol_lane=False))
        )
        self.assertEqual(result.policy, POLICY)
        self.assertEqual(
            result.to_dict()["schema_version"], "agdaprover.symbolic-retrieval.v1"
        )
        self.assertNotIn(
            "query_symbol_match", result.to_dict()["items"][0]["components"]
        )
        graph = AllowedDependencies(SCOPE, (("a", ()), ("z", ())))
        result = SymbolicPremiseIndex(scoped.allowed, graph).retrieve(query)
        self.assertEqual(result.policy, DEPENDENCY_POLICY)
        self.assertEqual(
            result.to_dict()["schema_version"], "agdaprover.symbolic-retrieval.v2"
        )

    def test_query_references_beyond_the_cutoff_get_a_distinct_lane(self) -> None:
        scoped = index(
            *(premise(f"a{i:03}", "R") for i in range(100)), premise("z", "Q")
        )
        query = RetrievalQuery(SCOPE, TypeFeatures("R", ("z",), 0))
        self.assertNotIn("z", ids(scoped.retrieve(query, limit=64)))
        result = scoped.retrieve(replace(query, query_symbol_lane=True), limit=8)
        self.assertEqual(ids(result)[:4], ["a000", "z", "a001", "a002"])
        self.assertEqual(result.candidate_count, 101)
        self.assertEqual(result.policy, QUERY_SYMBOL_POLICY)
        self.assertEqual(
            result.to_dict()["schema_version"], "agdaprover.symbolic-retrieval.v3"
        )
        self.assertEqual(result.items[1].query_symbol_match, 1)
        self.assertEqual(result.items[0].query_symbol_match, 0)
        self.assertEqual(result.index_id, scoped.index_id)
        self.assertNotEqual(result.query_id, query.query_id)

    def test_aliases_and_hidden_query_symbols_cannot_create_members(self) -> None:
        scoped = index(
            premise("a", "R"),
            replace(premise("native-id", "Q"), aliases=("alias", "second-alias")),
        )
        query = RetrievalQuery(
            SCOPE, TypeFeatures("R", ("alias", "hidden"), 0), query_symbol_lane=True
        )
        result = scoped.retrieve(query)
        self.assertEqual(ids(result), ["a", "native-id"])
        self.assertTrue(all(item.query_symbol_match == 0 for item in result.items))
        self.assertEqual(result.candidate_count, 2)
        self.assertEqual(index().retrieve(query).items, ())
        with self.assertRaisesRegex(ValueError, "scope"):
            scoped.retrieve(replace(query, scope_id="2" * 64))

    def test_flag_is_strict_boolean(self) -> None:
        for value in (None, 0, 1, "true", [], {}):
            with (
                self.subTest(value=value),
                self.assertRaisesRegex(ValueError, "Boolean"),
            ):
                RetrievalQuery(
                    SCOPE, TypeFeatures(None, (), 0), query_symbol_lane=value
                )

    def test_full_merge_oracle_and_prefix_stability(self) -> None:
        rng = random.Random(934)
        for case in range(60):
            names = [f"n{i:03}" for i in range(rng.randrange(1, 80))]
            scoped = index(
                *(premise(name, rng.choice((None, "R", "S"))) for name in names)
            )
            references = set(rng.sample(names, rng.randrange(len(names) + 1)))
            base = RetrievalQuery(
                SCOPE, TypeFeatures("R", tuple(sorted(references)), 0)
            )
            query = replace(base, query_symbol_lane=True)
            expected = interleave(
                ids(scoped.retrieve(base, limit=len(names))), references
            )
            for limit in (1, 2, 8, 32, 64, len(names) + 10):
                with self.subTest(case=case, limit=limit):
                    result = scoped.retrieve(query, limit=limit)
                    self.assertEqual(ids(result), expected[:limit])
                    self.assertEqual(len(ids(result)), len(set(ids(result))))
                    for item in result.items:
                        self.assertEqual(
                            item.query_symbol_match,
                            int(item.premise.declaration_id in references),
                        )

    def test_dependency_and_incremental_policies_remain_bound(self) -> None:
        scoped = index(premise("a", "R"), premise("b", "R"), premise("z", "Q"))
        graph = AllowedDependencies(SCOPE, (("a", ("z",)), ("b", ()), ("z", ())))
        old = SymbolicPremiseIndex(scoped.allowed, graph)
        allowed = replace(scoped.allowed, scope_id="2" * 64)
        new_graph = replace(graph, scope_id=allowed.scope_id)
        cold = SymbolicPremiseIndex(allowed, new_graph)
        incremental = old.updated(allowed, new_graph)
        query = RetrievalQuery(
            allowed.scope_id, TypeFeatures("R", ("z",), 0), query_symbol_lane=True
        )
        result = incremental.retrieve(query)
        self.assertEqual(result.to_dict(), cold.retrieve(query).to_dict())
        self.assertEqual(result.policy, DEPENDENCY_QUERY_SYMBOL_POLICY)
        self.assertEqual(result.dependency_graph_id, new_graph.graph_id)
        legacy = cold.retrieve(replace(query, query_symbol_lane=False))
        self.assertEqual(result.postings_visited, legacy.postings_visited)
        self.assertNotEqual(result.query_id, legacy.query_id)

    def test_interruption_during_merge_does_not_mutate_the_index(self) -> None:
        scoped = index(premise("a", "R"), premise("z", "Q"))
        query = RetrievalQuery(
            SCOPE, TypeFeatures("R", ("z",), 0), query_symbol_lane=True
        )
        expected = scoped.retrieve(query)
        calls = 0
        real_smallest = heapq.nsmallest

        def smallest(*args, **kwargs):
            nonlocal calls
            result = real_smallest(*args, **kwargs)
            calls += 1
            return result

        def checkpoint() -> None:
            if calls == 2:
                raise RuntimeError("interrupted at lane merge")

        with patch("agdaprover.retrieval.heapq.nsmallest", side_effect=smallest):
            with patch("agdaprover.retrieval.checkpoint", side_effect=checkpoint):
                with self.assertRaisesRegex(RuntimeError, "interrupted at lane merge"):
                    scoped.retrieve(query)
        self.assertEqual(scoped.retrieve(query), expected)


if __name__ == "__main__":
    unittest.main()
