"""Checked introductions need not print implicit function abstractions."""

import shutil
import tempfile
import unittest
from pathlib import Path

from agdaprover.contracts import GoalInfo, TaskSpec
from agdaprover.kernel.p0 import AgdaSession
from agdaprover.reconstruction import apply_source_edit, reconstruct_intro
from agdaprover.step import propose_step
from agdaprover.verification import (
    validate_partial_reconstruction,
    validate_reconstruction,
)


def source(field_type):
    return (
        "{-# OPTIONS --safe --without-K #-}\n"
        "module Introduction where\n"
        "data Token : Set where\n  token : Token\n"
        "data Eq {A : Set} (x : A) : A → Set where\n  same : Eq x x\n"
        "record Box : Set where\n  constructor box\n  field item : Token\n"
        "record Bundle : Set where\n"
        f"  field contents : {field_type}\n"
        "test : Bundle\n"
        "test = record { contents = {!!} }\n"
    )


class IntroductionReconstructionTests(unittest.TestCase):
    def test_constructor_previews_stay_inside_the_selected_hole(self):
        text = "test = record { first = {!!}; second = keep }\n"
        start = text.index("{!!}") + 1
        goal = GoalInfo(0, "{A : Set} → F A", (), (start, start + 4))
        for preview in ("same", "box ?", "record { value = ? }", "left , right"):
            with self.subTest(preview=preview):
                edit = reconstruct_intro(text, goal, preview)
                self.assertEqual(edit["style"], "term")
                self.assertEqual(edit["binders"], [])
                self.assertEqual(edit["source_range"], [start, start + 4])
                self.assertEqual(
                    apply_source_edit(text, edit),
                    text.replace("{!!}", f"({preview})"),
                )

    def test_explicit_lambda_still_hoists_at_a_whole_clause(self):
        text = "test = {!!}\n"
        goal = GoalInfo(0, "A → B", (), (8, 12))
        edit = reconstruct_intro(text, goal, "λ x y → ?")
        self.assertEqual(edit["style"], "clause-intro")
        self.assertEqual(edit["replacement"], "test x y = {!!}")

    def test_embedded_lambda_and_hidden_binders_are_not_hoisted(self):
        text = "test = keep , {!!}\n"
        start = text.index("{!!}") + 1
        goal = GoalInfo(0, "{A : Set} → A → A", (), (start, start + 4))
        for preview in ("λ x → ?", "λ {A} x → ?"):
            edit = reconstruct_intro(text, goal, preview)
            self.assertEqual(edit["style"], "term")
            self.assertEqual(
                apply_source_edit(text, edit), text.replace("{!!}", f"({preview})")
            )

    def test_empty_previews_and_nonhole_ranges_remain_invalid(self):
        text = "test = {!!}\n"
        goal = GoalInfo(0, "A", (), (8, 12))
        for preview in ("", " \n "):
            with self.assertRaisesRegex(ValueError, "empty"):
                reconstruct_intro(text, goal, preview)
        with self.assertRaises(ValueError):
            reconstruct_intro(text, GoalInfo(0, "A", (), (1, 5)), "same")

    def test_stale_source_is_still_rejected(self):
        text = "test = {!!}\n"
        edit = reconstruct_intro(text, GoalInfo(0, "A", (), (8, 12)), "same")
        with self.assertRaises(ValueError):
            apply_source_edit(text.replace("{!!}", "token"), edit)


@unittest.skipUnless(shutil.which("agda"), "Agda 2.8 is required")
class CheckedIntroductionReconstructionTests(unittest.TestCase):
    def test_actual_hidden_function_introductions_freshly_recheck(self):
        for field_type, preview, complete in (
            ("{t : Token} → Token", "token", True),
            ("{t : Token} → Eq t t", "same", True),
            ("{{t : Token}} → Token", "token", True),
            ("{t : Token} → Box", "box ?", False),
        ):
            with (
                self.subTest(field_type=field_type),
                tempfile.TemporaryDirectory() as directory,
            ):
                path = Path(directory) / "Introduction.agda"
                text = source(field_type)
                path.write_text(text)
                with AgdaSession(timeout_seconds=15) as session:
                    goal = session.inspect_goal(session.load_module(path)[0])
                    checked = session.check_refinement(goal.goal_id, "")
                    self.assertTrue(checked.accepted)
                    self.assertEqual(checked.preview, preview)
                    edit = reconstruct_intro(text, goal, checked.preview)
                validation = validate_partial_reconstruction(
                    path, edit, timeout_seconds=15
                )
                self.assertTrue(validation["fresh_process"])
                self.assertTrue(validation["loaded"])
                self.assertFalse(validation["complete_proof"])
                self.assertEqual(len(validation["open_goals"]), 0 if complete else 1)
                if complete:
                    final, _ = validate_reconstruction(path, edit, timeout_seconds=15)
                    self.assertTrue(final["checked"], final)
                    self.assertTrue(final["fresh_process"])
                self.assertEqual(path.read_text(), text)

    def test_public_one_step_accepts_a_nonlambda_function_introduction(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Introduction.agda"
            text = source("{t : Token} → Eq t t")
            path.write_text(text)
            result = propose_step(TaskSpec(path, ranker="symbolic", timeout_seconds=15))
            self.assertEqual(result.status, "accepted-step", result.diagnostics)
            self.assertEqual(result.action["tag"], "introduce-lambda")
            self.assertEqual(result.action["source_edit"]["replacement"], "(same)")
            self.assertTrue(result.action["reconstruction_validation"]["loaded"])
            self.assertEqual(
                result.action["reconstruction_validation"]["open_goals"], []
            )
            self.assertFalse(
                result.action["reconstruction_validation"]["complete_proof"]
            )
            self.assertEqual(path.read_text(), text)


if __name__ == "__main__":
    unittest.main()
