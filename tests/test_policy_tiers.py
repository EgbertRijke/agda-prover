"""The shared policy respects structural tiers without losing candidates."""

import unittest
from unittest.mock import patch

from agdaprover.contracts import GoalInfo
from agdaprover.nnue import NNUEModel
from agdaprover.or_policy import ORPolicyRouter, policy_candidate


class PolicyTierTests(unittest.TestCase):
    def setUp(self):
        self.goal = GoalInfo(0, "A", (), (1, 5))
        self.candidates = tuple(
            policy_candidate(
                family="visible-premise",
                tag="refine-visible-premise",
                expression=name,
                type_text="A",
                symbolic_key=(i, name),
            )
            for i, name in enumerate(("first", "second", "later"))
        )
        self.model = NNUEModel("or-decision-ranking", 1, 1, [0.0], [0.0], [0.0], 0.0, 1)

    def test_scores_reorder_only_within_a_tier_and_trace_matches_execution(self):
        router = ORPolicyRouter(refinement_model=self.model)
        with patch.object(
            self.model, "score_feature_batches", return_value=[0.0, 1.0, 100.0]
        ):
            ranked = router.rank(self.goal, self.candidates, priority_tiers=(0, 0, 1))
        expected = (self.candidates[1], self.candidates[0], self.candidates[2])
        self.assertEqual(ranked.candidates, expected)
        self.assertEqual(router.model_items_scored, 3)
        record = router.recorder.to_list()[0]
        self.assertEqual(record["model_order"], [c.candidate_id for c in expected])
        self.assertEqual(record["provenance"]["priority_tiers"], [0, 0, 1])
        self.assertEqual(record["provenance"]["ranking_policy"], "structural-tiers-v1")
        self.assertEqual(len(record["candidate_set"]), 3)

    def test_unconstrained_batches_keep_full_model_ranking(self):
        router = ORPolicyRouter(refinement_model=self.model)
        with patch.object(
            self.model, "score_feature_batches", return_value=[0.0, 1.0, 100.0]
        ):
            ranked = router.rank(self.goal, self.candidates)
        self.assertEqual(ranked.candidates, tuple(reversed(self.candidates)))

    def test_missing_and_malformed_models_preserve_exact_symbolic_order(self):
        for model in (None, self.model):
            router = ORPolicyRouter(refinement_model=model)
            with patch.object(
                self.model, "score_feature_batches", return_value=[float("nan")] * 3
            ):
                ranked = router.rank(
                    self.goal, self.candidates, priority_tiers=(0, 0, 1)
                )
            self.assertEqual(ranked.candidates, self.candidates)

    def test_invalid_tiers_fail_before_model_work(self):
        router = ORPolicyRouter(refinement_model=self.model)
        for tiers in ((0,), (1, 0, 1), (0, 0, -1), (False, 0, 1), (0, 0, "1")):
            with self.subTest(tiers=tiers), self.assertRaises(ValueError):
                router.rank(self.goal, self.candidates, priority_tiers=tiers)
        self.assertEqual(router.model_items_scored, 0)
        self.assertEqual(router.recorder.to_list(), [])
