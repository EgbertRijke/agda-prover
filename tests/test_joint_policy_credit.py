"""Joint search credits only choices retained by its freshly checked branch."""

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.case_search import CaseBatchResult, CaseBatchStats
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.observability.policy_trace import validated_proof_evidence
from agdaprover.presentation import apply_source_edit
from agdaprover.resource_budget import ResourceLimitError, ResourceScope

CHOICES = """{-# OPTIONS --safe --without-K #-}
module Choices where
data Flag : Set where first second : Flag
left : Flag
left = {!!}
right : Flag
right = {!!}
"""

BACKTRACK = """{-# OPTIONS --safe --without-K #-}
module Choices where
data Void : Set where
data Unit : Set where star : Unit
data Flag : Set where first second : Flag
Accept : Flag → Set
Accept first = Void
Accept second = Unit
value : Flag
value = {!!}
witness : Accept value
witness = {!!}
"""

CASE = """{-# OPTIONS --safe --without-K #-}
module Choices where
data Box (A : Set) : Set where wrap : A → Box A
unpack : (A : Set) → Box A → A
unpack = {!!}
"""


def positives(result):
    return [
        (decision, candidate)
        for decision in result.policy_trace
        for candidate in decision["candidate_set"]
        if candidate["outcome"] == "on-validated-proof"
    ]


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class JointPolicyCreditTests(unittest.TestCase):
    def run_joint(self, text=CHOICES, **kwargs):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Choices.agda"
            source.write_text(text)
            result = prove_joint_prefix(
                TaskSpec(source, timeout_seconds=15, ranker="symbolic", **kwargs)
            )
            self.assertEqual(source.read_text(), text)
            return result

    def assert_bound(self, result):
        self.assertEqual(result.status, "verified", result.diagnostics)
        evidence = validated_proof_evidence(
            task_id=result.task_id,
            source_sha256=result.source_hash,
            patch=result.patch,
            validation=result.validation,
            trust_report=result.trust_report,
        )
        self.assertIsNotNone(evidence)
        for decision, candidate in positives(result):
            self.assertTrue(candidate["explored"])
            self.assertEqual(decision["provenance"]["validated_result"], evidence)
            self.assertEqual(
                sum(
                    c["outcome"] == "on-validated-proof"
                    for c in decision["candidate_set"]
                ),
                1,
            )

    def test_multiple_goals_retain_their_constructor_choices(self):
        result = self.run_joint()
        self.assert_bound(result)
        self.assertEqual(len(positives(result)), 2)
        self.assertEqual(
            {d["family"] for d, _c in positives(result)}, {"constructor-choice"}
        )
        self.assertTrue(all(c["expression"] == "first" for _d, c in positives(result)))

    def test_rejected_branch_does_not_receive_the_winning_branch_credit(self):
        result = self.run_joint(BACKTRACK)
        self.assert_bound(result)
        self.assertEqual([c["expression"] for _d, c in positives(result)], ["second"])
        choices = [c for d in result.policy_trace for c in d["candidate_set"]]
        self.assertTrue(
            any(c["expression"] == "first" and c["explored"] for c in choices)
        )
        self.assertTrue(
            all(
                c["outcome"] != "on-validated-proof"
                for c in choices
                if c["expression"] == "first"
            )
        )

    def test_case_batch_choices_reach_joint_validation(self):
        result = self.run_joint(CASE)
        self.assert_bound(result)
        self.assertTrue(positives(result))
        self.assertEqual(
            {d["family"] for d, _c in positives(result)}, {"case-variable"}
        )

    def test_direct_case_alternatives_retain_the_selected_choice(self):
        with patch(
            "agdaprover.joint.batched_case_prove",
            return_value=CaseBatchResult("unsolved", None, None, CaseBatchStats()),
        ):
            result = self.run_joint(CASE)
        self.assert_bound(result)
        self.assertTrue(positives(result))
        self.assertEqual(
            {d["family"] for d, _c in positives(result)}, {"case-variable"}
        )

    def test_composed_record_evidence_survives_the_joint_queue(self):
        result = self.run_joint(
            """{-# OPTIONS --safe --without-K #-}
module Choices where
record Pair (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B
open Pair
map : {A B C D : Set} → (A → C) → (B → D) → Pair A B → Pair C D
map = {!!}
"""
        )
        self.assert_bound(result)
        self.assertEqual(len(positives(result)), 3)
        self.assertEqual(
            {d["family"] for d, _c in positives(result)}, {"evidence-application-v1"}
        )

    def test_prefix_credit_does_not_solve_or_credit_the_unselected_suffix(self):
        result = self.run_joint(goal_id=0)
        self.assertEqual(result.status, "verified", result.diagnostics)
        # The v1 training receipt requires a hole-free fresh check. A prefix
        # certificate remains useful to the editor but is not that receipt.
        self.assertEqual(positives(result), [])
        updated = apply_source_edit(CHOICES, result.patch)
        self.assertIn("right = {!!}", updated)
        self.assertEqual(len(result.joint_goals), 1)

    def test_failed_fresh_validation_leaves_choices_censored(self):
        with patch(
            "agdaprover.joint.validate_reconstruction",
            return_value=(
                {
                    "checked": False,
                    "fresh_process": True,
                    "timed_out": True,
                    "exit_status": None,
                },
                {},
            ),
        ):
            result = self.run_joint()
        self.assertEqual(result.status, "resource-exhausted", result.diagnostics)
        self.assertTrue(result.policy_trace)
        self.assertEqual(positives(result), [])

    def test_final_resource_refusal_grants_no_credit(self):
        finish = ResourceScope.finish

        def refuse(scope):
            return finish(scope) or ResourceLimitError("final resource refusal")

        with patch("agdaprover.joint.ResourceScope.finish", refuse):
            result = self.run_joint()
        self.assertEqual(result.status, "resource-exhausted", result.diagnostics)
        self.assertTrue(result.policy_trace)
        self.assertEqual(positives(result), [])

    def test_bad_lineage_does_not_change_proof_acceptance_or_emit_partial_credit(self):
        with patch(
            "agdaprover.joint.PolicyTraceRecorder.mark_validated_proof",
            side_effect=ValueError("invalid diagnostic lineage"),
        ):
            result = self.run_joint()
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertEqual(positives(result), [])
        self.assertTrue(any(d["kind"] == "training-trace" for d in result.diagnostics))


if __name__ == "__main__":
    unittest.main()
