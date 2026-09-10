"""Automatic-introduction recovery preserves parent state and source scope."""

import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.search import prove
from agdaprover.step import propose_step
from agdaprover.type_syntax import telescope_introduction
from agdaprover.verifier_budget import VerifierCallLimitExceeded, VerifierCallScope

SOURCE = """module PatternTelescope where
open import Agda.Builtin.Sigma

project : {A : Set} {P : A → Set} → ((a , b) : Σ A P) → P a
project = {!!}

untouched : {A : Set} → A → A
untouched = {!!}
"""


def agda_available():
    executable = shutil.which("agda")
    return (
        bool(executable)
        and subprocess.run(
            [executable, "--numeric-version"],
            capture_output=True,
            text=True,
            check=False,
        ).stdout.strip()
        == "2.8.0"
    )


class TelescopeRenderingTests(unittest.TestCase):
    def test_fresh_explicit_names_do_not_copy_internal_pattern_labels(self):
        self.assertEqual(
            telescope_introduction(
                "(arg1 : A) → (.internal : Pair A B) → B",
                frozenset({"arg0"}),
                implicit_only=False,
            ),
            "λ arg2 arg3 → ?",
        )
        self.assertIsNone(telescope_introduction("A → B", frozenset()))

    def test_hidden_and_adjacent_binders_preserve_visibility(self):
        self.assertEqual(
            telescope_introduction(
                "{A : Set} → (x y : A) → A", frozenset(), implicit_only=False
            ),
            "λ {A = arg0} arg1 arg2 → ?",
        )
        for unsupported in ("A", "(", "{x = y : A} → B", "⦃x : A⦄ → B"):
            self.assertIsNone(
                telescope_introduction(unsupported, frozenset(), implicit_only=False)
            )


@unittest.skipUnless(agda_available(), "Agda 2.8.0 is required")
class PatternTelescopeIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.source = Path(self.temporary.name) / "PatternTelescope.agda"
        self.source.write_text(SOURCE)

    def test_speculative_and_committed_intros_drop_noop_metas_and_replay_parent(self):
        with AgdaSession(timeout_seconds=15) as session:
            goals = session.load_module(self.source)
            goal = session.inspect_goal(goals[0])
            parent = session.current_state()
            speculative = session.check_refinement(goal.goal_id, "")
            self.assertTrue(speculative.accepted)
            self.assertTrue(speculative.preview.startswith("λ "))
            self.assertEqual(len(speculative.generated_goals), 1)
            self.assertEqual(session.inspect_state(parent)[0].target, goal.target)
            committed = session.commit_proof_action(
                parent, kind="refine", goal_id=goal.goal_id, expression=""
            )
            self.assertTrue(committed.accepted)
            self.assertEqual(committed.preview, speculative.preview)
            self.assertEqual(len(committed.generated_goals), 1)
            child = committed.child_state
            self.assertIsNotNone(child)
            self.assertEqual(len(session.inspect_state(child)), 2)
            self.assertEqual(session.internal_obligation_counts(child), (0, 0))
            # Switching away and back must replay the explicit successful
            # action, not the failed automatic intro with orphaned metas.
            self.assertEqual(len(session.inspect_state(parent)), 2)
            self.assertEqual(len(session.inspect_state(child)), 2)
            self.assertEqual(session.internal_obligation_counts(child), (0, 0))
        self.assertEqual(self.source.read_text(), SOURCE)

    def test_step_and_prove_do_not_report_a_valid_pattern_goal_as_invalid(self):
        task = TaskSpec(self.source, goal_id=0, timeout_seconds=15, ranker="symbolic")
        step = propose_step(task)
        self.assertEqual(step.status, "accepted-step", step.diagnostics)
        proof = prove(task)
        self.assertEqual(proof.status, "verified", proof.diagnostics)
        self.assertTrue(proof.validation["fresh_process"])
        joint = prove_joint_prefix(task)
        self.assertEqual(joint.status, "verified", joint.diagnostics)
        self.assertTrue(joint.validation["fresh_process"])
        self.assertEqual(self.source.read_text(), SOURCE)

    def test_unrenderable_fallback_rejects_only_the_action(self):
        with AgdaSession(timeout_seconds=15) as session:
            goals = session.load_module(self.source)
            parent = session.current_state()
            with patch(
                "agdaprover.bridge.compat_p0.telescope_introduction", return_value=None
            ):
                checked = session.commit_proof_action(
                    parent, kind="refine", goal_id=goals[0].goal_id, expression=""
                )
            self.assertFalse(checked.accepted)
            self.assertEqual(checked.rejection_code, "agda-intro-no-progress")
            self.assertIsNone(checked.child_state)
            self.assertEqual(checked.generated_goals, ())
            self.assertEqual(len(session.inspect_state(parent)), 2)
            self.assertEqual(session.internal_obligation_counts(parent), (0, 0))

    def test_noop_and_recovery_obey_the_physical_query_budget(self):
        with AgdaSession(timeout_seconds=15) as session:
            goals = session.load_module(self.source)
            quota = VerifierCallScope()
            quota.open(1)
            try:
                with self.assertRaises(VerifierCallLimitExceeded):
                    session.check_refinement(goals[0].goal_id, "")
                self.assertEqual(quota.report()["used"], 1)
                self.assertGreater(quota.report()["denied_calls"], 0)
            finally:
                quota.close()
        self.assertEqual(self.source.read_text(), SOURCE)
