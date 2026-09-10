"""Generic structural admission, independent bounded orders and old identities."""

from __future__ import annotations

import random
import unittest
from dataclasses import replace
from unittest.mock import patch

from test_query_view_retrieval import fixture

from agdaprover.retrieval import (
    NormalizedQueryView,
    SymbolicPremiseIndex,
    TypeFamilyQueryView,
    TypeFeatures,
)


class TypeFamilyRetrievalTests(unittest.TestCase):
    def test_interrupted_second_view_and_merge_never_publish_partial_rankings(self):
        index, original = fixture(31, random.Random(8), True)
        query = replace(
            original,
            normalized=None,
            features=TypeFeatures("R", ("alias",), 0),
            type_family=TypeFamilyQueryView(TypeFeatures("R", ("underlying",), 0)),
        )
        expected = index.retrieve(query)
        retrieve = SymbolicPremiseIndex.retrieve

        class Interrupted(Exception):
            pass

        for phase in ("second-view", "merge"):
            completed = []

            def attempt(
                instance, candidate, *, limit=64, completed=completed, phase=phase
            ):
                if (
                    candidate.type_family is None
                    and len(completed) == 1
                    and phase == "second-view"
                ):
                    raise Interrupted
                result = retrieve(instance, candidate, limit=limit)
                if candidate.type_family is None:
                    completed.append(result)
                return result

            def checkpoint(completed=completed, phase=phase):
                if len(completed) == 2 and phase == "merge":
                    raise Interrupted

            with (
                patch.object(SymbolicPremiseIndex, "retrieve", attempt),
                patch("agdaprover.retrieval.checkpoint", checkpoint),
            ):
                with self.assertRaises(Interrupted):
                    index.retrieve(query)
            self.assertEqual(index.retrieve(query), expected)

    def test_stable_head_uses_shared_bounded_merge_in_all_lanes(self):
        rng = random.Random(792314)
        for size in (0, 1, 17, 91):
            for deps in (False, True):
                for symbols, rarity in ((False, False), (True, False), (True, True)):
                    index, original = fixture(size, rng, deps)
                    query = replace(
                        original,
                        normalized=None,
                        query_symbol_lane=symbols,
                        symbol_rarity_lane=rarity,
                        features=replace(
                            original.features, result_head="global:family"
                        ),
                    )
                    alternate = replace(
                        original.normalized.features,
                        result_head=query.features.result_head,
                        arity=query.features.arity,
                    )
                    query = replace(query, type_family=TypeFamilyQueryView(alternate))
                    raw_query = replace(query, type_family=None)
                    raw = index.retrieve(raw_query, limit=max(1, size))
                    reduced = index.retrieve(
                        replace(raw_query, features=alternate), limit=max(1, size)
                    )
                    distinct = alternate != query.features
                    lanes = [list(enumerate(raw.items, 1))]
                    names = ["raw"]
                    if distinct:
                        lanes.append(list(enumerate(reduced.items, 1)))
                        names.append("type-family")
                    seen, expected = set(), []
                    while any(lanes):
                        for name, lane in zip(names, lanes, strict=True):
                            while lane:
                                rank, item = lane.pop(0)
                                if item.premise.declaration_id not in seen:
                                    seen.add(item.premise.declaration_id)
                                    expected.append(
                                        replace(
                                            item, query_view=name, query_view_rank=rank
                                        )
                                    )
                                    break
                    for width in (1, 8, 32, 64, 128, 512):
                        result = index.retrieve(query, limit=width)
                        self.assertEqual(result.items, tuple(expected[:width]))
                        self.assertEqual(result.index_id, raw.index_id)
                        self.assertEqual(
                            result.query_views_scored, 2 if distinct else 1
                        )
                        self.assertEqual(
                            result.scored_count, size * result.query_views_scored
                        )
                        self.assertEqual(
                            result.postings_visited,
                            raw.postings_visited
                            + (reduced.postings_visited if distinct else 0),
                        )
                        self.assertEqual(
                            result,
                            index.updated(index.allowed, index.dependencies).retrieve(
                                query, limit=width
                            ),
                        )
                        self.assertEqual(
                            result.to_dict()["schema_version"],
                            "agdaprover.symbolic-retrieval.v6",
                        )

    def test_unknown_changed_or_unavailable_evidence_keeps_exact_raw_order(self):
        index, original = fixture(91, random.Random(174), True)
        query = replace(
            original, features=TypeFeatures("R", ("alias",), 2), normalized=None
        )
        for features, status, classification in (
            (TypeFeatures("S", ("underlying",), 2), "checked", "changed-head"),
            (TypeFeatures("R", ("underlying",), 1), "checked", "changed-arity"),
            (TypeFeatures(None, ("underlying",), 2), "checked", "unknown-head"),
            (query.features, "checked", "identical"),
            (None, "kernel-rejected", "kernel-rejected"),
            (None, "output-limited", "output-limited"),
        ):
            view = TypeFamilyQueryView(
                features, status=status, term_visits=19, type_position_reductions=8
            )
            for width in (8, 64, 512):
                raw = index.retrieve(query, limit=width)
                result = index.retrieve(replace(query, type_family=view), limit=width)
                self.assertEqual(
                    [i.premise for i in result.items], [i.premise for i in raw.items]
                )
                self.assertEqual(result.type_family_classification, classification)
                self.assertEqual(result.postings_visited, raw.postings_visited)
                self.assertEqual(result.query_views_scored, 1)
                self.assertTrue(all(i.query_view == "raw" for i in result.items))
                self.assertNotEqual(result.query_id, raw.query_id)
        self.assertEqual(
            TypeFamilyQueryView(query.features).classification(
                TypeFeatures(None, (), 2), ()
            ),
            "unknown-head",
        )
        # Names are identity evidence, not specially recognized vocabulary.
        for name in ("X", "global:982:7", "local:0"):
            renamed = TypeFeatures(name, ("a",), 2)
            self.assertEqual(
                TypeFamilyQueryView(TypeFeatures(name, ("b",), 2)).classification(
                    renamed, ()
                ),
                "stable-head-and-arity",
            )

    def test_malformed_views_fail_and_old_policy_ids_remain_unchanged(self):
        index, original = fixture(17, random.Random(4), False)
        raw = replace(original, normalized=None)
        self.assertEqual(raw, replace(raw, type_family=None))
        self.assertEqual(
            original.query_id, replace(original, type_family=None).query_id
        )
        self.assertEqual(
            index.retrieve(original).to_dict()["schema_version"],
            "agdaprover.symbolic-retrieval.v5",
        )
        self.assertNotIn("type_family_query_policy", index.retrieve(raw).to_dict())
        for kwargs in (
            {"features": None},
            {"features": raw.features, "status": "output-limited"},
            {"features": None, "status": "kernel-rejected", "tokens": ("forbidden",)},
            {"features": raw.features, "policy": "agda-normalise-query-type-v1"},
            {"features": raw.features, "term_visits": True},
            {"features": raw.features, "term_visits": 1, "type_position_reductions": 2},
        ):
            with self.assertRaises(ValueError):
                TypeFamilyQueryView(**kwargs)
        with self.assertRaises(ValueError):
            replace(original, type_family=TypeFamilyQueryView(raw.features))
        with self.assertRaises(ValueError):
            replace(raw, type_family=NormalizedQueryView(raw.features))


if __name__ == "__main__":
    unittest.main()
