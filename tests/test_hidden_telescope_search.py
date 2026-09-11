"""Kernel-owned clause introduction preserves the complete telescope."""

import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.contracts import ContextEntry, GoalInfo, TaskSpec
from agdaprover.dependency_planner import build_dependency_plan
from agdaprover.joint import prove_joint_prefix
from agdaprover.search import prove

PREFIX = """{-# OPTIONS --safe --without-K --exact-split #-}
module Hidden where
data Flag : Set where a b : Flag
data Unit : Set where star : Unit
Family : Flag → Set
Family a = Unit
Family b = Unit
"""


class BindingPriorityTests(unittest.TestCase):
    def test_hidden_dependencies_can_be_ranked_without_becoming_eliminations(self):
        plan = build_dependency_plan(
            GoalInfo(
                0,
                "Family x witness",
                (
                    ContextEntry("Index", "Set", True),
                    ContextEntry("x", "Index", False),
                    ContextEntry("witness", "Relation x x", False),
                ),
                (1, 5),
            )
        )
        self.assertLess(
            plan.priority("witness", include_hidden=True),
            plan.priority("x", include_hidden=True),
        )
        self.assertIsNone(plan.elimination_action("witness"))
        self.assertIsNone(plan.tower.visible_node("witness"))
        self.assertEqual(plan.priority("witness"), plan.priority("missing"))


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class HiddenTelescopeSearchTests(unittest.TestCase):
    def run_prover(self, source, *, joint=True, enabled=True):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Hidden.agda"
            path.write_text(source)
            with patch.dict(
                os.environ,
                {"AGDAPROVER_CONTEXT_BINDING": "1" if enabled else "0"},
            ):
                result = (prove_joint_prefix if joint else prove)(
                    TaskSpec(path, max_candidates=200, timeout_seconds=15)
                )
            self.assertEqual(path.read_text(), source)
        return result

    def assert_verified(self, result):
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["checked"])
        self.assertTrue(result.validation["fresh_process"])

    def test_implicit_family_input_is_exposed_in_single_and_joint_search(self):
        source = PREFIX + "f : {x : Flag} → Family x\nf = {!!}\n"
        for joint in (False, True):
            for variant in (source, source.replace("Flag", "Colour")):
                with self.subTest(joint=joint, source=variant):
                    result = self.run_prover(variant, joint=joint)
                    self.assert_verified(result)
                    stats = (
                        result.search_stats
                        if joint
                        else result.search_stats["case_batch"]
                    )
                    self.assertGreater(stats["context_bindings"], 0)

    def test_dependent_record_field_can_use_the_same_hidden_input(self):
        result = self.run_prover(
            PREFIX
            + """record Box (x : Flag) : Set where
  constructor box
  field value : Family x
f : {x : Flag} → Box x
f = {!!}
"""
        )
        self.assert_verified(result)
        self.assertGreater(result.search_stats["context_bindings"], 0)

    def test_dependent_hidden_and_instance_arguments_follow_explicit_inputs(self):
        for binder in ("{value : Carrier}", "⦃ value : Carrier ⦄"):
            with self.subTest(binder=binder):
                result = self.run_prover(
                    PREFIX + f"f : (Carrier : Set) {binder} → Carrier\nf = {{!!}}\n"
                )
                self.assert_verified(result)

    def test_ablation_does_not_synthesize_an_unavailable_index(self):
        result = self.run_prover(
            PREFIX + "f : {x : Flag} → Family x\nf = {!!}\n", enabled=False
        )
        self.assertNotEqual(result.status, "verified")
        self.assertEqual(result.search_stats["context_bindings"], 0)

    def test_hidden_value_is_available_to_evidence_composition(self):
        source = (
            PREFIX
            + """data Path {A : Set} (x : A) : A → Set where
  point : Path x x
join : {A : Set} {x y z : A} → Path x y → Path y z → Path x z
join point q = q
unit : {A : Set} {x y : A} (p : Path x y) → Path (join p point) p
unit point = point
"""
        )
        for target in (
            "{A : Set} {x : A} {q : Path x x} → Path point (join q point) → Path point q",
            "{A : Set} {x y z : A} (r : Path y z) {p q : Path x y} → Path (join p r) (join q r) → Path p q",
        ):
            with self.subTest(target=target):
                result = self.run_prover(
                    source + f"cancel : {target}\ncancel = {{!!}}\n"
                )
                self.assert_verified(result)

    def test_exposing_a_type_parameter_does_not_invent_an_inhabitant_or_loop(self):
        result = self.run_prover(PREFIX + "f : {A : Set} → A\nf = {!!}\n")
        self.assertEqual(result.status, "unsolved", result.diagnostics)
        self.assertEqual(result.search_stats["context_bindings"], 1)
        self.assertIsNone(result.patch)

    def test_local_helper_composes_above_a_section_specialized_operation(self):
        source = (
            PREFIX
            + """data Path {A : Set} (x : A) : A → Set where
  point : Path x x
module _ {A : Set} where
  join : {x y z : A} → Path x y → Path y z → Path x z
  join point q = q
  unit : {x y : A} (p : Path x y) → Path (join p point) p
  unit point = point
  cancel : {x : A} {q : Path x x} → Path point (join q point) → Path point q
  cancel = {!!}
"""
        )
        result = self.run_prover(source)
        self.assert_verified(result)
        self.assertIn("proverHelper", result.patch["replacement"])
        self.assertFalse(any(d["kind"] == "training-trace" for d in result.diagnostics))

    def test_search_expands_a_with_clause_ellipsis_through_agda(self):
        result = self.run_prover(
            PREFIX + "f : Flag → Flag\nf x with x\n... | a = {!!}\n... | b = b\n"
        )
        self.assert_verified(result)
