"""Goal-directed joins must not depend on names, relations or lexical rank."""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.contracts import GoalInfo, TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.premise_search import ScopePremiseAction, rank_scope_premises
from agdaprover.reasoning.backward import supported_applications
from agdaprover.reasoning.evidence import EvidenceApplication, EvidenceTerm
from agdaprover.search import prove


def proposals(target, declarations, excluded=frozenset()):
    return tuple(
        supported_applications(
            GoalInfo(0, target, (), (1, 2)),
            tuple(ScopePremiseAction(n, t, n) for n, t in declarations),
            excluded_names=excluded,
        )
    )


class BackwardSupportTests(unittest.TestCase):
    def test_hidden_values_and_different_families_under_renaming(self):
        for source, target, consume, evidence in (
            ("R", "S", "convert", "known"),
            ("P", "Q", "unrelated-name", "Library.fact"),
        ):
            with self.subTest(source=source):
                rows = (
                    (consume, f"{{a b : X}} → {source} a b → {target} b a"),
                    (evidence, f"{{x = v : X}} → {source} (f v) v"),
                )
                found = proposals(f"{target} p (f p)", rows)
                self.assertEqual(
                    [p.expression for p in found], [f"{consume} {evidence}"]
                )
                self.assertEqual(found[0].arguments[0].type_text, rows[1][1])

    def test_multiple_inputs_and_function_values_are_not_relation_specific(self):
        rows = (
            ("combine", "(u v : Package A) → (A → B) → Result B"),
            ("first", "Package A"),
            ("second", "Package A"),
            ("function", "A → B"),
        )
        self.assertEqual(
            {p.expression for p in proposals("Result B", rows)},
            {
                "combine first first function",
                "combine first second function",
                "combine second first function",
                "combine second second function",
            },
        )

    def test_result_determined_leaf_application_retains_grouping(self):
        rows = (
            ("consume", "{t : X} → Evidence t → Result t"),
            ("produce", "(t : X) → Evidence t"),
        )
        self.assertEqual(
            [p.expression for p in proposals("Result (f (g x))", rows)],
            ["consume (produce (f (g x)))"],
        )
        self.assertEqual(
            proposals("Result (f (g x))", rows)[0].arguments[0].type_text, ""
        )

    def test_missing_inconsistent_and_excluded_inputs_do_not_gain_support(self):
        rows = (
            ("convert", "{a b : X} → R a b → S b a"),
            ("source", "{a : X} → R a a"),
        )
        self.assertEqual(proposals("S a b", rows), ())
        self.assertEqual(proposals("S a a", rows, frozenset({"source"})), ())
        self.assertEqual(proposals("S a a", rows, frozenset({"convert"})), ())
        self.assertEqual(proposals("S a a", rows[:1]), ())

    def test_dependency_not_fixed_by_result_is_left_to_kernel_search(self):
        self.assertEqual(
            proposals("Output", (("f", "{A : Set} → A → Output"), ("x", "B"))),
            (),
        )

    def test_support_is_found_beyond_the_lexical_shortlist(self):
        rows = (
            ("turn", "{a b : X} → R a b → R b a"),
            ("unit-law", "{a : X} → R (op a unit) a"),
            *((f"noise{i}", "R p (op p unit) → R p (op p unit)") for i in range(80)),
        )
        goal = GoalInfo(0, "R p (op p unit)", (), (1, 2))
        self.assertNotIn("turn", {a.name for a in rank_scope_premises(goal, rows)})
        self.assertIn(
            "turn unit-law", {p.expression for p in proposals(goal.target, rows)}
        )

    def test_unsupported_surface_syntax_does_not_block_other_proposals(self):
        rows = (("broken", "{x : X → R"), ("f", "P → Q"), ("p", "P"))
        self.assertEqual([p.expression for p in proposals("Q", rows)], ["f p"])

    def test_cancellation_is_not_swallowed_as_a_missing_proposal(self):
        def stop():
            raise TimeoutError("cancel this search")

        with self.assertRaisesRegex(TimeoutError, "cancel this search"):
            tuple(
                supported_applications(
                    GoalInfo(0, "Q", (), (1, 2)),
                    (ScopePremiseAction("f", "P → Q", "f"),),
                    poll=stop,
                )
            )


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class BackwardSupportIntegrationTests(unittest.TestCase):
    def check(self, source, *, joint=False, ranker="nnue"):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.agda"
            path.write_text(source)
            result = (prove_joint_prefix if joint else prove)(
                TaskSpec(path, ranker=ranker, timeout_seconds=15, max_candidates=160)
            )
            self.assertEqual(path.read_text(), source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["checked"])
        self.assertTrue(result.validation["fresh_process"])
        return result

    def test_record_consumer_with_a_function_valued_source(self):
        # The source is a noninductive function type, the target a record.
        source = """{-# OPTIONS --safe --without-K #-}
module Example where
record Box (A : Set) : Set where
  constructor box
  field value : A
module _ {A : Set} (a : A) where
  known : A → A
  known x = x
  package : (A → A) → Box A
  package f = box (f a)
  goal : Box A
  goal = {!!}
"""
        result = self.check(source)
        self.assertIn("package known", result.proof_term)

    def test_supplied_rule_and_implicit_value_beyond_shortlist(self):
        # No built-in equality and no library/operator vocabulary in the engine.
        source = """{-# OPTIONS --safe --without-K #-}
module Example where
data Link {A : Set} (x : A) : A → Set where
  same : Link x x
then : {A : Set} {x y z : A} → Link x y → Link y z → Link x z
then same q = q
turn : {A : Set} {x y : A} → Link x y → Link y x
turn same = same
known : {A : Set} {x y : A} {p : Link x y} → Link (then p same) p
known {p = same} = same
"""
        source += "".join(
            f"noise{i} : {{A : Set}} {{x y : A}} {{p : Link x y}} → "
            f"Link p (then p same) → Link p (then p same)\n"
            f"noise{i} h = h\n"
            for i in range(80)
        )
        source += (
            "goal : {A : Set} {x y : A} (p : Link x y) → Link p (then p same)\n"
            "goal {A} {x} {y} p = {!!}\n"
        )
        for joint, ranker in ((False, "nnue"), (True, "symbolic")):
            with self.subTest(joint=joint, ranker=ranker):
                result = self.check(source, joint=joint, ranker=ranker)
                if not joint:
                    self.assertIn("turn known", result.proof_term)

    def test_rejected_support_preserves_fallback(self):
        # Inject a deliberately wrong proposal at the untrusted boundary.
        # The common checker must reject it and retain ordinary construction.
        source = """{-# OPTIONS --safe --without-K #-}
module Example where
data One : Set where one : One
record Box (A : Set) : Set where
  constructor box
  field value : A
bad : {A : Set} → A → Box A
bad = box
wrong : One
wrong = one
module _ {A : Set} (a : A) where
  goal : Box A
  goal = {!!}
"""
        invalid = EvidenceApplication(
            EvidenceTerm("bad", "{A : Set} → A → Box A"),
            (EvidenceTerm("wrong", "One"),),
        )
        with patch(
            "agdaprover.constructor_search.supported_applications",
            return_value=iter((invalid,)),
        ):
            result = self.check(source)
        self.assertNotIn("bad wrong", result.proof_term)

    def test_no_inductivity_or_symmetry_is_assumed_of_supplied_relation(self):
        source = """{-# OPTIONS --safe --without-K #-}
module Example where
record Output {A : Set} (x y : A) : Set where
  constructor pack
  field witness : A
module _ {A : Set} (R : A → A → Set)
  (convert : {x y : A} → R x y → Output y x)
  (fact : {x : A} → R x x) (a : A) where
  goal : Output a a
  goal = {!!}
"""
        result = self.check(source)
        self.assertIn("convert fact", result.proof_term)


if __name__ == "__main__":
    unittest.main()
