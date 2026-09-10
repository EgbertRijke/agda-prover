"""Proof-path credit is exact, conservative and independent of ranking order."""

import unittest
from dataclasses import replace

from agdaprover.constructor_search import ProofPlan
from agdaprover.contracts import GoalInfo
from agdaprover.observability.policy_trace import PolicyChoice, validated_proof_evidence
from agdaprover.or_policy import ORPolicyRouter, policy_candidate


class PolicyCreditTests(unittest.TestCase):
    def setUp(self):
        self.goal = GoalInfo(0, "Carrier", (), (0, 4))
        self.router = ORPolicyRouter()
        self.candidates = tuple(
            policy_candidate(
                family="constructor-choice",
                tag="construct",
                expression=name,
                type_text="Carrier",
                symbolic_key=(index,),
            )
            for index, name in enumerate(("first", "second", "third"))
        )
        self.router.rank(self.goal, self.candidates)
        self.choices = self.router.snapshot_choices("constructor-choice", self.goal)

    def mark(self, name, **kwargs):
        choice = self.choices[name]
        self.router.recorder.mark(choice.decision_id, choice.candidate_id, **kwargs)

    def test_child_decision_cannot_steal_parent_credit(self):
        self.mark("first", outcome="invalid")
        self.mark("second")
        child_goal = replace(self.goal, goal_id=1)
        self.router.rank(child_goal, self.candidates)
        self.assertEqual(
            self.router.snapshot_choices("constructor-choice", self.goal), {}
        )
        self.router.recorder.mark_validated_proof(
            (self.choices["second"],), evidence={"receipt": "checked"}
        )
        parent, child = self.router.recorder.to_list()
        self.assertEqual(
            [c["outcome"] for c in parent["candidate_set"]],
            ["invalid", "on-validated-proof", "budget-censored"],
        )
        self.assertTrue(
            all(c["outcome"] == "budget-censored" for c in child["candidate_set"])
        )
        self.assertFalse(any(c["explored"] for c in child["candidate_set"]))

    def test_conflicting_unknown_unexplored_or_rejected_choices_are_atomic(self):
        self.mark("first")
        self.mark("second", outcome="invalid")
        for bad in (
            self.choices["second"],
            self.choices["third"],
            PolicyChoice("missing", "missing"),
        ):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.router.recorder.mark_validated_proof(
                    (self.choices["first"], bad), evidence={}
                )
            self.assertNotIn("on-validated-proof", str(self.router.recorder.to_list()))
        self.mark("third")
        with self.assertRaises(ValueError):
            self.router.recorder.mark_validated_proof(
                (self.choices["first"], self.choices["third"]), evidence={}
            )

    def test_proof_plan_collects_only_its_own_path_without_changing_rendering(self):
        child = ProofPlan("value", policy_choices=(self.choices["second"],))
        plan = ProofPlan("wrap ?", (child,), policy_choices=(self.choices["first"],))
        self.assertEqual(plan.render(), "wrap value")
        self.assertEqual(
            plan.choices_on_proof(), (self.choices["first"], self.choices["second"])
        )
        self.assertEqual(ProofPlan("other").choices_on_proof(), ())

    def test_republication_cannot_create_two_positives(self):
        self.mark("first")
        self.mark("second")
        self.router.recorder.mark_validated_proof((self.choices["first"],), evidence={})
        self.router.recorder.mark_validated_proof((self.choices["first"],), evidence={})
        with self.assertRaises(ValueError):
            self.router.recorder.mark_validated_proof(
                (self.choices["second"],), evidence={}
            )

    def test_unrecorded_singleton_does_not_reuse_previous_batch(self):
        self.router.rank(self.goal, self.candidates[:1])
        self.assertEqual(
            self.router.snapshot_choices("constructor-choice", self.goal), {}
        )

    def test_evidence_requires_fresh_success_and_binds_every_result_component(self):
        inputs = dict(
            task_id="task",
            source_sha256="a" * 64,
            patch={"replacement": "value"},
            validation={
                "checked": True,
                "fresh_process": True,
                "timed_out": False,
                "exit_status": 0,
            },
            trust_report={
                "agda_version": "2.8.0",
                "fresh_process": True,
                "offline": True,
                "checker_exit_status": 0,
            },
        )
        expected = validated_proof_evidence(**inputs)
        self.assertIsNotNone(expected)
        for field, value in (
            ("checked", False),
            ("fresh_process", False),
            ("timed_out", True),
            ("exit_status", 1),
            ("exit_status", False),
        ):
            self.assertIsNone(
                validated_proof_evidence(
                    **{**inputs, "validation": {**inputs["validation"], field: value}}
                )
            )
        for field in ("patch", "trust_report", "validation"):
            self.assertIsNone(validated_proof_evidence(**{**inputs, field: None}))
        for field, value in (
            ("fresh_process", False),
            ("offline", False),
            ("checker_exit_status", 1),
            ("checker_exit_status", False),
        ):
            self.assertIsNone(
                validated_proof_evidence(
                    **{
                        **inputs,
                        "trust_report": {**inputs["trust_report"], field: value},
                    }
                )
            )
        self.assertNotEqual(
            expected,
            validated_proof_evidence(**{**inputs, "patch": {"replacement": "other"}}),
        )
        self.assertNotEqual(
            expected,
            validated_proof_evidence(
                **{
                    **inputs,
                    "trust_report": {
                        **inputs["trust_report"],
                        "agda_version": "different",
                    },
                }
            ),
        )
