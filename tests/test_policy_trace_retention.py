"""Complete OR batches consume bytes, not an arbitrary candidate-count limit."""

import json
import unittest
from unittest.mock import patch

from agdaprover.contracts import GoalInfo
from agdaprover.observability.policy_trace import PolicyTraceRecorder
from agdaprover.or_policy import ORPolicyRouter, policy_candidate


def batch(count, text="Carrier"):
    return tuple(
        policy_candidate(
            family="visible-premise",
            tag="refine-visible-premise",
            expression=f"value{i}",
            type_text=text,
            symbolic_key=(i,),
        )
        for i in range(count)
    )


class PolicyTraceRetentionTests(unittest.TestCase):
    goal = GoalInfo(0, "Carrier", (), (0, 4))

    def router(self, **kwargs):
        return ORPolicyRouter(recorder=PolicyTraceRecorder(**kwargs))

    def test_large_batch_is_complete_and_preserves_symbolic_order(self):
        router = self.router()
        candidates = batch(513)
        ranked = router.rank(self.goal, candidates)
        self.assertEqual(ranked.candidates, candidates)
        trace = router.recorder.to_list()
        self.assertEqual(len(trace), 1)
        self.assertEqual(len(trace[0]["candidate_set"]), 513)
        self.assertEqual(
            trace[0]["symbolic_order"], [c.candidate_id for c in candidates]
        )
        self.assertEqual(trace[0]["model_order"], trace[0]["symbolic_order"])
        self.assertEqual(
            len(router.snapshot_choices("visible-premise", self.goal)), 513
        )

    def test_byte_boundary_is_atomic_and_smaller_later_batch_can_fit(self):
        probe = self.router()
        probe.rank(self.goal, batch(3, "λ界"))
        charge = probe.metrics()["trace_retention"]["charged_bytes"]
        self.assertGreater(charge, 0)
        for allowance, retained in ((charge, 1), (charge - 1, 0)):
            router = self.router(max_bytes=allowance)
            router.rank(self.goal, batch(3, "λ界"))
            self.assertEqual(len(router.recorder.to_list()), retained)
        router = self.router(max_bytes=charge)
        router.rank(self.goal, batch(513))
        self.assertEqual(router.recorder.omitted, 1)
        self.assertEqual(router.snapshot_choices("visible-premise", self.goal), {})
        router.rank(self.goal, batch(2))
        self.assertEqual(len(router.recorder.to_list()), 1)
        self.assertLessEqual(
            router.metrics()["trace_retention"]["charged_bytes"], charge
        )

    def test_inputs_are_snapshotted_and_annotations_stay_accounted(self):
        recorder = PolicyTraceRecorder()
        candidates = batch(2)
        ids = tuple(c.candidate_id for c in candidates)
        state, provenance = {"nested": ["original"]}, {"nested": ["source"]}
        scores = {ids[0]: 1.0}
        decision_id = recorder.record(
            family="visible-premise",
            state=state,
            candidates=candidates,
            symbolic_order=ids,
            model_order=ids,
            model_scores=scores,
            model_id="model",
            budget_envelope={},
            provenance=provenance,
        )
        state["nested"].append("mutation")
        provenance["nested"].append("mutation")
        scores[ids[0]] = 5.0
        recorder.mark(decision_id, ids[0], outcome="valid-unproductive")
        trace = recorder.to_list()
        self.assertEqual(trace[0]["state"], {"nested": ["original"]})
        self.assertEqual(trace[0]["provenance"], {"nested": ["source"]})
        self.assertEqual(trace[0]["candidate_set"][0]["model_score"], 1.0)
        trace[0]["state"]["nested"].append("export mutation")
        trace[0]["provenance"]["nested"].append("export mutation")
        trace = recorder.to_list()
        self.assertNotIn("mutation", str(trace))
        compact = json.dumps(
            trace[0], ensure_ascii=False, sort_keys=True, separators=(",", ":")
        )
        self.assertLessEqual(len(compact.encode()), recorder.metrics()["charged_bytes"])

    def test_invalid_outcome_does_not_mutate_exploration(self):
        router = self.router()
        router.rank(self.goal, batch(2))
        choice = router.snapshot_choices("visible-premise", self.goal)["value0"]
        before = router.recorder.to_list()
        with self.assertRaises(ValueError):
            router.recorder.mark(
                choice.decision_id, choice.candidate_id, outcome="unknown"
            )
        self.assertEqual(router.recorder.to_list(), before)

    def test_complete_proof_credit_is_reserved_before_any_annotation(self):
        router = self.router()
        choices = []
        for _ in range(2):
            router.rank(self.goal, batch(2))
            choice = router.snapshot_choices("visible-premise", self.goal)["value0"]
            router.recorder.mark(choice.decision_id, choice.candidate_id)
            choices.append(choice)
        before = router.recorder.to_list()
        # One annotation fits, but the complete two-decision proof does not.
        router.recorder.max_bytes = (
            router.metrics()["trace_retention"]["charged_bytes"] + 40
        )
        router.recorder.mark_validated_proof(
            tuple(choices), evidence={"receipt": "checked"}
        )
        self.assertEqual(router.recorder.to_list(), before)
        self.assertEqual(
            router.metrics()["trace_retention"]["proof_credits_omitted"], 2
        )

    def test_credit_growth_is_atomic_and_does_not_discard_checked_choices(self):
        router = self.router()
        router.rank(self.goal, batch(2))
        choice = router.snapshot_choices("visible-premise", self.goal)["value1"]
        router.recorder.mark(choice.decision_id, choice.candidate_id)
        before = router.recorder.to_list()
        router.recorder.max_bytes = router.metrics()["trace_retention"]["charged_bytes"]
        router.recorder.mark_validated_proof((choice,), evidence={"receipt": "checked"})
        self.assertEqual(router.recorder.to_list(), before)
        self.assertEqual(
            router.metrics()["trace_retention"]["proof_credits_omitted"], 1
        )
        router.recorder.max_bytes += 1000
        router.recorder.mark_validated_proof((choice,), evidence={"receipt": "checked"})
        self.assertEqual(
            router.recorder.to_list()[0]["candidate_set"][1]["outcome"],
            "on-validated-proof",
        )

    def test_settings_and_optional_count_limit(self):
        for settings in (
            {"max_bytes": True},
            {"max_bytes": 0},
            {"max_bytes": 1.5},
            {"max_decisions": True},
            {"max_decisions": 0},
        ):
            with self.subTest(settings=settings), self.assertRaises(ValueError):
                PolicyTraceRecorder(**settings)
        router = self.router(max_decisions=1)
        router.rank(self.goal, batch(2))
        router.rank(self.goal, batch(3))
        self.assertEqual(len(router.recorder.to_list()), 1)
        self.assertEqual(router.recorder.omitted, 1)

    def test_default_does_not_stop_at_the_old_decision_count(self):
        router = self.router()
        candidates = batch(2)
        for _ in range(4097):
            router.rank(self.goal, candidates)
        self.assertEqual(router.recorder.recorded_decisions, 4097)
        with patch.object(router.recorder, "to_list", side_effect=AssertionError):
            metrics = router.metrics()
        self.assertEqual(metrics["trace_decisions"], 4097)
        self.assertIsNone(metrics["trace_retention"]["max_decisions"])


if __name__ == "__main__":
    unittest.main()
