"""Two-view ranking is a pure, prefix-stable operation on one allowed scope."""

from __future__ import annotations

import random
import unittest
from dataclasses import replace
from unittest.mock import patch

from agdaprover.retrieval import (
    AllowedDependencies,
    AllowedPremise,
    AllowedPremiseSet,
    NormalizedQueryView,
    RetrievalQuery,
    SymbolicPremiseIndex,
    TypeFeatures,
)

SCOPE = "a" * 64


def fixture(size, rng, dependencies):
    names = [f"n{i:03}" for i in range(size)]
    vocabulary = ["alias", "underlying", "family", *names]

    def features():
        return TypeFeatures(
            rng.choice(("global:alias", "global:family", "local:0", None)),
            tuple(sorted(rng.sample(vocabulary, min(3, len(vocabulary))))),
            rng.randrange(4),
        )

    allowed = AllowedPremiseSet(
        SCOPE,
        tuple(
            AllowedPremise(n, (n,), features(), "contextual", "b" * 64) for n in names
        ),
    )
    deps = (
        AllowedDependencies(
            SCOPE, tuple((n, tuple(m for m in names[:3] if m != n)) for n in names)
        )
        if dependencies
        else None
    )
    query = RetrievalQuery(
        SCOPE, features(), normalized=NormalizedQueryView(features())
    )
    return SymbolicPremiseIndex(allowed, deps), query


class QueryViewRetrievalTests(unittest.TestCase):
    def test_full_orders_define_all_bounded_prefixes_and_work(self):
        rng = random.Random(93814)
        for size in (0, 1, 2, 13, 91):
            for dependencies in (False, True):
                for symbols, rarity in ((False, False), (True, False), (True, True)):
                    index, query = fixture(size, rng, dependencies)
                    query = replace(
                        query, query_symbol_lane=symbols, symbol_rarity_lane=rarity
                    )
                    raw_query = replace(query, normalized=None)
                    norm_query = replace(raw_query, features=query.normalized.features)
                    raw = index.retrieve(raw_query, limit=max(size, 1))
                    normalized = index.retrieve(norm_query, limit=max(size, 1))
                    # Independent full-order destructive-list merge. No top-k
                    # implementation, interleave helper or private labels.
                    distinct = raw_query.features != norm_query.features
                    results = (raw, normalized) if distinct else (raw,)
                    views = ("raw", "normalized") if distinct else ("raw",)
                    pending = [list(enumerate(r.items, 1)) for r in results]
                    expected = []
                    seen = set()
                    while any(pending):
                        for view, lane in zip(views, pending, strict=True):
                            while lane:
                                rank, item = lane.pop(0)
                                if item.premise.declaration_id not in seen:
                                    seen.add(item.premise.declaration_id)
                                    expected.append(
                                        replace(
                                            item, query_view=view, query_view_rank=rank
                                        )
                                    )
                                    break
                    for limit in (1, 2, 8, 64, 512):
                        with self.subTest(
                            size=size,
                            deps=dependencies,
                            symbols=symbols,
                            rarity=rarity,
                            limit=limit,
                        ):
                            result = index.retrieve(query, limit=limit)
                            self.assertEqual(result.items, tuple(expected[:limit]))
                            self.assertEqual(result.candidate_count, size)
                            self.assertEqual(result.scored_count, len(results) * size)
                            self.assertEqual(
                                result.postings_visited,
                                sum(r.postings_visited for r in results),
                            )
                            self.assertEqual(
                                result.dependency_postings_visited,
                                sum(r.dependency_postings_visited for r in results),
                            )
                            self.assertEqual(result.index_id, raw.index_id)
                            self.assertNotEqual(result.query_id, raw.query_id)
                            self.assertEqual(
                                result.to_dict()["schema_version"],
                                "agdaprover.symbolic-retrieval.v5",
                            )
                            self.assertEqual(
                                index.updated(
                                    index.allowed, index.dependencies
                                ).retrieve(query, limit=limit),
                                result,
                            )

    def test_raw_alias_and_normalized_family_both_remain_available(self):
        def row(name, symbol):
            return AllowedPremise(
                name, (name,), TypeFeatures("R", (symbol,), 0), "contextual", "b" * 64
            )

        index = SymbolicPremiseIndex(
            AllowedPremiseSet(
                SCOPE, (row("a", "alias"), row("b", "alias"), row("z", "underlying"))
            )
        )
        raw = RetrievalQuery(SCOPE, TypeFeatures("R", ("alias",), 0))
        query = replace(
            raw, normalized=NormalizedQueryView(TypeFeatures("R", ("underlying",), 0))
        )
        result = index.retrieve(query, limit=2)
        self.assertEqual([i.premise.declaration_id for i in result.items], ["a", "z"])
        self.assertEqual([i.query_view for i in result.items], ["raw", "normalized"])
        self.assertEqual([i.query_view_rank for i in result.items], [1, 1])
        # Absent/forbidden identities in either query never become candidates.
        hidden = replace(
            query, normalized=NormalizedQueryView(TypeFeatures("R", ("forbidden",), 0))
        )
        self.assertEqual(
            {i.premise.declaration_id for i in index.retrieve(hidden).items},
            {"a", "b", "z"},
        )
        self.assertNotEqual(hidden.query_id, query.query_id)
        self.assertEqual(
            index.retrieve(raw).to_dict()["schema_version"],
            "agdaprover.symbolic-retrieval.v1",
        )
        self.assertNotIn("normalized_query_policy", index.retrieve(raw).to_dict())

    def test_identical_views_do_not_duplicate_candidates(self):
        index, query = fixture(13, random.Random(2), False)
        query = replace(
            query, normalized=NormalizedQueryView(query.features, query.tokens)
        )
        raw = index.retrieve(replace(query, normalized=None))
        result = index.retrieve(query)
        self.assertEqual(
            [x.premise for x in result.items], [x.premise for x in raw.items]
        )
        self.assertEqual(result.scored_count, raw.scored_count)
        self.assertEqual(result.postings_visited, raw.postings_visited)
        self.assertEqual(result.query_views_scored, 1)
        self.assertTrue(all(item.query_view == "raw" for item in result.items))

    def test_invalid_views_scope_and_cancellation(self):
        index, query = fixture(13, random.Random(2), False)
        for invalid in (True, {}, [], "normalized"):
            with self.assertRaises(ValueError):
                replace(query, normalized=invalid)
        with self.assertRaises(ValueError):
            NormalizedQueryView(query.features, policy="partial-normalization")
        with self.assertRaises(ValueError):
            NormalizedQueryView(query.features, tokens=["mutable"])
        with self.assertRaises(ValueError):
            index.retrieve(replace(query, scope_id="f" * 64))

        class Cancelled(Exception):
            pass

        with patch("agdaprover.retrieval.checkpoint", side_effect=Cancelled):
            with self.assertRaises(Cancelled):
                index.retrieve(query)
        self.assertEqual(len(index.retrieve(query).items), 13)

    def test_interruption_in_second_view_or_merge_leaves_index_reusable(self):
        index, query = fixture(31, random.Random(8), True)
        expected = index.retrieve(query)
        original = SymbolicPremiseIndex.retrieve

        class Cancelled(Exception):
            pass

        for phase in ("second-view", "merge"):
            completed = []

            def retrieve(
                instance, candidate, *, limit=64, completed=completed, phase=phase
            ):
                if (
                    candidate.normalized is None
                    and len(completed) == 1
                    and phase == "second-view"
                ):
                    raise Cancelled
                result = original(instance, candidate, limit=limit)
                if candidate.normalized is None:
                    completed.append(result)
                return result

            def checkpoint(completed=completed, phase=phase):
                if len(completed) == 2 and phase == "merge":
                    raise Cancelled

            with (
                patch.object(SymbolicPremiseIndex, "retrieve", retrieve),
                patch("agdaprover.retrieval.checkpoint", checkpoint),
            ):
                with self.assertRaises(Cancelled):
                    index.retrieve(query)
            self.assertEqual(index.retrieve(query), expected)


if __name__ == "__main__":
    unittest.main()
