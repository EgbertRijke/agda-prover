"""Independent small-scope oracle for the opt-in sparse ranking lane."""

from __future__ import annotations

import math
import random
import unittest
from collections import Counter
from dataclasses import replace
from unittest.mock import patch

from agdaprover.retrieval import (
    DEPENDENCY_SYMBOL_RARITY_POLICY,
    SYMBOL_RARITY_POLICY,
    AllowedDependencies,
    AllowedPremise,
    AllowedPremiseSet,
    RetrievalQuery,
    SymbolicPremiseIndex,
    TypeFeatures,
)

SCOPE = "0" * 64


def make_index(rows):
    return SymbolicPremiseIndex(
        AllowedPremiseSet(SCOPE, tuple(sorted(rows, key=lambda p: p.declaration_id)))
    )


def premise(name, symbols=(), head=None):
    return AllowedPremise(
        name, (name,), TypeFeatures(head, tuple(sorted(symbols)), 0), "lifted", "1" * 64
    )


def identifiers(result):
    return [item.premise.declaration_id for item in result.items]


def oracle(index, query):
    """Full sort + destructive-list merge, independent of production top-k."""
    base = index.retrieve(
        replace(query, query_symbol_lane=False, symbol_rarity_lane=False),
        limit=max(1, len(index.allowed.premises)),
    )
    df = Counter(s for p in index.allowed.premises for s in p.features.symbols)
    n = len(index.allowed.premises)
    avg = max(1, sum(df.values()) / max(n, 1))
    scores = {
        p.declaration_id: sum(
            math.log1p((n - df[s] + 0.5) / (df[s] + 0.5))
            for s in p.features.symbols
            if s in query.features.symbols
        )
        * 2.2
        / (1 + 1.2 * (0.25 + 0.75 * len(p.features.symbols) / avg))
        for p in index.allowed.premises
    }
    lanes = [
        list(base.items),
        [p for p in base.items if p.premise.declaration_id in query.features.symbols],
        sorted(
            base.items, key=lambda p: (-scores[p.premise.declaration_id], p.sort_key)
        ),
    ]
    output = []
    while any(lanes):
        for lane in lanes:
            while lane:
                name = lane.pop(0).premise.declaration_id
                if name not in output:
                    output.append(name)
                    break
    return output, scores


class SymbolRarityTests(unittest.TestCase):
    def test_full_sort_oracle_prefix_stability_scores_and_wire(self):
        rng = random.Random(40619)
        for size in (0, 1, 2, 5, 31, 90):
            for case in range(8):
                vocabulary = [f"s{i}" for i in range(8)]
                rows = [
                    premise(
                        f"n{i:03}",
                        rng.sample(vocabulary, rng.randrange(9)),
                        rng.choice(("R", "S", None)),
                    )
                    for i in range(size)
                ]
                index = make_index(rows)
                symbols = tuple(
                    sorted(
                        rng.sample(
                            vocabulary + [p.declaration_id for p in rows],
                            rng.randrange(9),
                        )
                    )
                )
                query = RetrievalQuery(
                    SCOPE,
                    TypeFeatures("R", symbols, 0),
                    query_symbol_lane=True,
                    symbol_rarity_lane=True,
                )
                expected, scores = oracle(index, query)
                for limit in (1, 2, 8, 64, 512):
                    with self.subTest(size=size, case=case, limit=limit):
                        result = index.retrieve(query, limit=limit)
                        self.assertEqual(identifiers(result), expected[:limit])
                        self.assertEqual(result.policy, SYMBOL_RARITY_POLICY)
                        self.assertEqual(
                            result.to_dict()["schema_version"],
                            "agdaprover.symbolic-retrieval.v4",
                        )
                        self.assertEqual(result.candidate_count, size)
                        for item in result.items:
                            self.assertEqual(
                                item.symbol_rarity, scores[item.premise.declaration_id]
                            )
                            self.assertTrue(math.isfinite(item.symbol_rarity))
                            self.assertGreaterEqual(item.symbol_rarity, 0)

    def test_rare_overlap_reaches_a_separate_lane(self):
        index = make_index(
            [premise(f"a{i:03}", ("common",), "R") for i in range(100)]
            + [premise("direct"), premise("z", ("rare",), "S")]
        )
        query = RetrievalQuery(
            SCOPE,
            TypeFeatures("R", ("common", "direct", "rare"), 0),
            query_symbol_lane=True,
            symbol_rarity_lane=True,
        )
        result = index.retrieve(query, limit=3)
        self.assertEqual(identifiers(result), ["a000", "direct", "z"])
        self.assertGreater(result.items[2].symbol_rarity, result.items[0].symbol_rarity)
        renamed = make_index(
            [
                replace(p, aliases=("renamed-" + p.declaration_id,))
                for p in index.allowed.premises
            ]
        )
        self.assertEqual(
            [p.symbol_rarity for p in result.items],
            [p.symbol_rarity for p in renamed.retrieve(query, limit=3).items],
        )
        # A symbol known in the goal cannot admit a hidden declaration or
        # provide document-frequency evidence outside this allowed set.
        hidden = replace(
            query,
            features=replace(
                query.features, symbols=(*query.features.symbols, "secret")
            ),
        )
        self.assertEqual(
            identifiers(index.retrieve(hidden)), identifiers(index.retrieve(query))
        )
        self.assertEqual(index.retrieve(hidden).items, index.retrieve(query).items)

    def test_disabled_wire_id_and_postings_are_unchanged(self):
        index = make_index([premise("a", ("a",)), premise("b", ("a",))])
        base = RetrievalQuery(SCOPE, TypeFeatures(None, ("a",), 0))
        for direct in (False, True):
            query = replace(base, query_symbol_lane=direct)
            old = index.retrieve(query)
            self.assertEqual(
                old.to_dict(),
                index.retrieve(replace(query, symbol_rarity_lane=False)).to_dict(),
            )
            self.assertNotIn("symbol_rarity", old.to_dict()["items"][0]["components"])
            new = index.retrieve(
                replace(query, query_symbol_lane=True, symbol_rarity_lane=True)
            )
            self.assertNotEqual(old.query_id, new.query_id)
            self.assertEqual(old.index_id, new.index_id)
            self.assertEqual(old.postings_visited, new.postings_visited)

    def test_strict_options_and_scope(self):
        for invalid in (None, 0, 1, "true", [], {}):
            with self.assertRaisesRegex(ValueError, "Boolean"):
                RetrievalQuery(
                    SCOPE,
                    TypeFeatures(None, (), 0),
                    query_symbol_lane=True,
                    symbol_rarity_lane=invalid,
                )
        with self.assertRaisesRegex(ValueError, "requires"):
            RetrievalQuery(SCOPE, TypeFeatures(None, (), 0), symbol_rarity_lane=True)
        with self.assertRaisesRegex(ValueError, "scope"):
            make_index([]).retrieve(
                RetrievalQuery(
                    "2" * 64,
                    TypeFeatures(None, (), 0),
                    query_symbol_lane=True,
                    symbol_rarity_lane=True,
                )
            )

    def test_dependency_incremental_updates_recompute_scope_statistics(self):
        old = make_index([premise("a", ("rare",)), premise("b", ("common",))])
        changed = make_index(
            [premise("a", ("rare",)), premise("c", ("rare",)), premise("d", ("rare",))]
        )
        graph = AllowedDependencies(SCOPE, (("a", ("c",)), ("c", ()), ("d", ())))
        cold = SymbolicPremiseIndex(changed.allowed, graph)
        reused = old.updated(changed.allowed, graph)
        query = RetrievalQuery(
            SCOPE,
            TypeFeatures(None, ("a", "rare"), 0),
            query_symbol_lane=True,
            symbol_rarity_lane=True,
        )
        self.assertEqual(cold.retrieve(query), reused.retrieve(query))
        self.assertEqual(cold.retrieve(query).policy, DEPENDENCY_SYMBOL_RARITY_POLICY)
        self.assertEqual(identifiers(cold.retrieve(query)), oracle(cold, query)[0])

    def test_interruption_does_not_mutate_index_or_publish_partial_result(self):
        index = make_index([premise(str(i), ("s",)) for i in range(600)])
        query = RetrievalQuery(
            SCOPE,
            TypeFeatures(None, ("s",), 0),
            query_symbol_lane=True,
            symbol_rarity_lane=True,
        )
        expected = index.retrieve(query)
        for stop in (1, 5, 10):
            calls = 0

            def check(stop=stop):
                nonlocal calls
                calls += 1
                if calls == stop:
                    raise RuntimeError("interrupted")

            with (
                patch("agdaprover.retrieval.checkpoint", side_effect=check),
                self.assertRaisesRegex(RuntimeError, "interrupted"),
            ):
                index.retrieve(query)
            self.assertEqual(index.retrieve(query), expected)


if __name__ == "__main__":
    unittest.main()
