"""Whole-function reuse uses expected types, not record-specific templates."""

from __future__ import annotations

import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.constructor_search import constructor_tree_prove
from agdaprover.contracts import GoalInfo, TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.premise_search import ScopePremiseAction, premise_function_shape_matches
from agdaprover.validation import validate_candidate


class FunctionValueShapeTests(unittest.TestCase):
    def matches(self, target, candidate):
        return premise_function_shape_matches(
            GoalInfo(0, target, (), (0, 4)),
            ScopePremiseAction("provided", candidate, "provided"),
        )

    def test_whole_telescope_specializes_hidden_parameters_consistently(self):
        self.assertTrue(
            self.matches(
                "{X Y : Set} → (X → Y) → Choice L X → Choice L Y",
                "{A B C : Set} → (B → C) → Choice A B → Choice A C",
            )
        )

    def test_named_domains_and_repeated_variables_are_preserved(self):
        self.assertTrue(self.matches("(x : X) → P x → P x", "(a : X) → P a → P a"))
        self.assertFalse(
            self.matches("{X Y : Set} → X → Y → Y", "{A B : Set} → A → B → A")
        )

    def test_renamed_infix_families_follow_the_same_rule(self):
        self.assertTrue(
            self.matches(
                "{X Y : Set} → (X → Y) → L ◇ X → L ◇ Y",
                "{A B C : Set} → (B → C) → A ◇ B → A ◇ C",
            )
        )
        self.assertFalse(
            self.matches(
                "{X Y : Set} → (X → Y) → L ◇ X → L ◇ Y",
                "{A B C : Set} → (B → C) → A ◆ B → A ◆ C",
            )
        )

    def test_different_arity_or_rigid_module_family_is_not_a_match(self):
        self.assertFalse(self.matches("X → X", "X → X → X"))
        self.assertFalse(self.matches("G X → G X", "F X → F X"))
        self.assertFalse(self.matches("X", "X"))

    def test_unknown_and_malformed_shapes_retain_the_fallback(self):
        for target, candidate in (
            ("X → (", "X → X"),
            ("X → X", "X → ("),
            ("X → _A_12", "X → X"),
        ):
            self.assertFalse(self.matches(target, candidate))

    def test_shape_hint_is_not_authority_for_hidden_instance_constraints(self):
        self.assertTrue(
            self.matches("{A : Set} → A → A", "{{t : Token}} → {A : Set} → A → A")
        )


SOURCE = """{-# OPTIONS --safe --without-K --exact-split #-}
module FunctionValues where
data Choice (A B : Set) : Set where
  left : A → Choice A B
  right : B → Choice A B
convert : {A B C : Set} → (B → C) → Choice A B → Choice A C
convert f (left a) = left a
convert f (right b) = right (f b)
record Mapper (F : Set → Set) : Set₁ where
  field
    lift : {A B : Set} → (A → B) → F A → F B
module Fixed (L : Set) where
  target : Mapper (Choice L)
  target = {!!}
"""
NATIVE = (
    Path(__file__).resolve().parents[1]
    / "native/agda-bridge/target/agdaprover-agda-bridge-2.8"
)


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_SCOPE") == "1"
    and NATIVE.is_file()
    and shutil.which("agda"),
    "opt-in native scoped-retrieval profile is required",
)
class FunctionValueKernelTests(unittest.TestCase):
    def check_source(self, source, expected, *, control=False, direct=False):
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.dict(
                os.environ,
                {
                    "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                    "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                    "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                    "AGDAPROVER_SCOPED_DEPENDENCIES": "0",
                    "AGDAPROVER_SCOPED_QUERY_VIEWS": "0",
                    "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "0",
                },
            ),
        ):
            path = Path(directory) / "FunctionValues.agda"
            path.write_text(source)
            if direct:
                with AgdaSession(timeout_seconds=10) as session:
                    (goal,) = session.load_module(path)
                    result = constructor_tree_prove(
                        session,
                        goal,
                        action_budget=96,
                        timeout_seconds=10,
                        max_depth=None,
                        excluded_premises=frozenset({"target"}),
                    )
                    self.assertEqual(result.status, "solved", result.stats.to_dict())
                    expression = result.solutions[0].proof_text
                    self.assertIn(expected, expression)
                checked, trust = validate_candidate(
                    path, goal, expression, timeout_seconds=10
                )
                self.assertTrue(checked["checked"], checked)
                self.assertTrue(checked["fresh_process"])
                self.assertEqual(trust["admitted_axioms_and_primitives"], [])
                self.assertEqual(path.read_text(), source)
                return {
                    "proof_term": expression,
                    "search_stats": result.stats.to_dict(),
                }
            task = TaskSpec(path, max_candidates=96, timeout_seconds=10)
            if control:
                with patch(
                    "agdaprover.constructor_search.premise_function_shape_matches",
                    return_value=False,
                ):
                    baseline = prove_joint_prefix(task)
                self.assertNotEqual(baseline.status, "verified")
            result = prove_joint_prefix(task)
            self.assertEqual(result.status, "verified", result.to_dict())
            self.assertIn(expected, result.proof_term)
            self.assertTrue(result.validation["checked"])
            self.assertTrue(result.validation["fresh_process"])
            self.assertTrue(all(c["passed"] for c in result.validation["checks"]))
            self.assertEqual(result.trust_report["admitted_axioms_and_primitives"], [])
            self.assertEqual(path.read_text(), source)
            return result.to_dict()

    def test_supplied_function_fills_record_field_without_reconstruction(self):
        result = self.check_source(SOURCE, "lift = convert", control=True)
        self.assertLess(result["cost"]["actions_expanded"], 16)
        attempts = result["search_stats"]["premise_attempts"]
        self.assertTrue(
            any(
                a.get("tag") == "reuse-visible-function" and a["accepted"]
                for a in attempts
            )
        )

    def test_infix_presentation_uses_the_same_boundary(self):
        source = SOURCE.replace("data Choice", "infixr 15 _◇_\ndata _◇_")
        for first, second in (("A", "B"), ("A", "C")):
            source = source.replace(f"Choice {first} {second}", f"{first} ◇ {second}")
        source = source.replace("Mapper (Choice L)", "Mapper (λ X → L ◇ X)")
        self.check_source(source, "lift = convert")

    def test_plain_function_goals_do_not_require_a_record(self):
        source = SOURCE.replace(
            "target : Mapper (Choice L)",
            "target : {X Y : Set} → (X → Y) → Choice L X → Choice L Y",
        )
        result = self.check_source(source, "convert", direct=True)
        self.assertEqual(result["proof_term"], "convert")

    def test_hidden_instance_rejection_keeps_function_introduction(self):
        source = """{-# OPTIONS --safe --without-K --exact-split #-}
module FunctionValues where
data Token : Set where
needs : {{t : Token}} → {A : Set} → A → A
needs x = x
target : {A : Set} → A → A
target = {!!}
"""
        result = self.check_source(source, "λ", direct=True)
        self.assertNotIn("needs", result["proof_term"])
        self.assertTrue(
            any(
                a.get("tag") == "reuse-visible-function"
                for a in result["search_stats"]["premise_attempts"]
            )
        )
