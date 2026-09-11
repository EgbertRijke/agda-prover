"""Autonomous, type-neutral recursion under kernel-generated copatterns."""

from __future__ import annotations

import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.case_search import _is_result_projection
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix


def specimen(name="Pulse", head="readout", tail="next", *, function_field=False):
    rest = f"A → {name} A" if function_field else f"{name} A"
    return f"""{{-# OPTIONS --guardedness --without-K #-}}
module Example where
record {name} (A : Set) : Set where
  coinductive
  field
    {head} : A
    {tail} : {rest}
open {name}
repeat : {{A : Set}} → A → {name} A
repeat = {{!!}}
"""


class CopatternProvenanceTests(unittest.TestCase):
    def test_argument_introduction_is_not_projection_provenance(self):
        for parent, generated in (
            ("", "read f"),
            ("f", "f x"),
            ("f x", "f x₁ .read"),
            ("f x", "read (g x)"),
            ("f x", "read (f x) y"),
        ):
            self.assertFalse(_is_result_projection(parent, generated))
        for generated in ("f x .read", "read (f x)", "Module.read (f x)"):
            self.assertTrue(_is_result_projection("  f x", generated))


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class CopatternSearchTests(unittest.TestCase):
    def solve(self, source, *, enabled=True, ranker="nnue", goal_id=0):
        with (
            tempfile.TemporaryDirectory(
                prefix="agdaprover-copattern-search-"
            ) as folder,
            patch.dict(
                os.environ, {"AGDAPROVER_COPATTERN_SEARCH": "1" if enabled else "0"}
            ),
        ):
            path = Path(folder) / "Example.agda"
            path.write_text(source)
            result = prove_joint_prefix(
                TaskSpec(
                    path,
                    goal_id=goal_id,
                    max_candidates=300,
                    max_verifier_calls=1000,
                    timeout_seconds=10,
                    ranker=ranker,
                )
            )
            self.assertEqual(path.read_text(), source)
            return result

    def test_repeated_values_are_autonomous_under_renaming_and_symbolic_fallback(self):
        for names, ranker in (
            (("Pulse", "readout", "next"), "nnue"),
            (("Orbit", "peek", "resume"), "symbolic"),
        ):
            with self.subTest(names=names, ranker=ranker):
                result = self.solve(specimen(*names), ranker=ranker)
                self.assertEqual(result.status, "verified", result.diagnostics)
                self.assertTrue(result.validation["fresh_process"])
                self.assertEqual(result.search_stats["copattern_clauses_generated"], 2)
                self.assertIn(
                    "refine-copattern-owner",
                    str(result.search_stats["recursive_actions"]),
                )
                self.assertIn(f".{names[2]}", result.patch["replacement"])

    def test_disabled_ablation_retains_original_exhaustion(self):
        result = self.solve(specimen(), enabled=False)
        self.assertEqual(result.status, "resource-exhausted")
        self.assertEqual(result.search_stats["result_split_queries"], 0)
        self.assertEqual(result.search_stats["copattern_clauses_generated"], 0)

    def test_function_valued_copattern_field_can_recurse_after_introduction(self):
        result = self.solve(specimen(function_field=True))
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["fresh_process"])

    def test_indexed_corecursive_composition_reuses_fields_at_unknown_middle_type(self):
        source = """{-# OPTIONS --guardedness --without-K #-}
module Example where
record Shape : Set₁ where
  coinductive
  field
    Point : Set
    Edge : Point → Point → Shape
open Shape
record Mapping (A B : Shape) : Set where
  coinductive
  field
    object : Point A → Point B
    arrow : {x y : Point A} → Mapping (Edge A x y)
      (Edge B (object x) (object y))
open Mapping
compose : {A B C : Shape} → Mapping B C → Mapping A B → Mapping A C
compose = {!!}
"""
        for text, ranker in (
            (source, "nnue"),
            (
                source.replace("Shape", "Geometry")
                .replace("Mapping", "Morphism")
                .replace("Point", "Vertex")
                .replace("Edge", "PathSpace")
                .replace("object", "vertices")
                .replace("arrow", "paths")
                .replace("compose", "chain")
                .replace("--guardedness", "--guardedness --no-postfix-projections"),
                "symbolic",
            ),
        ):
            with self.subTest(ranker=ranker):
                result = self.solve(text, ranker=ranker)
                self.assertEqual(result.status, "verified", result.diagnostics)
                self.assertTrue(result.validation["fresh_process"])

    def test_ordinary_record_composition_still_uses_supplied_fields(self):
        source = """{-# OPTIONS --safe --without-K #-}
module Example where
record Hom (A B : Set) : Set where
  field run : A → B
open Hom
record Box (A B : Set) : Set where
  field get : Hom A B
open Box
connect : {A B C : Set} → Hom B C → Hom A B → Hom A C
run (connect f g) x = run f (run g x)
assemble : {A B C : Set} → Box B C → Box A B → Hom A C
assemble = {!!}
"""
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["fresh_process"])

    def test_prefix_copattern_notation_is_autonomous(self):
        source = specimen().replace(
            "--guardedness", "--guardedness --no-postfix-projections"
        )
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["fresh_process"])
        self.assertIn("next (repeat", result.patch["replacement"])

    def test_dependent_fields_and_module_parameters_remain_scoped(self):
        source = """{-# OPTIONS --guardedness --without-K #-}
module Example where
record Packet (A : Set) (B : A → Set) : Set where
  coinductive
  field
    first : A
    second : B first
    later : Packet A B
open Packet
module _ {A : Set} {B : A → Set} (a : A) (b : B a) where
  assemble : Packet A B
  assemble = {!!}
"""
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertIn("assemble .first = a", result.patch["replacement"])
        self.assertIn("assemble .second = b", result.patch["replacement"])
        self.assertIn("assemble .later = assemble", result.patch["replacement"])

    def test_corecursive_builder_composes_observations_and_local_functions(self):
        source = (
            specimen().split("repeat :", 1)[0]
            + """build : {A B : Set} → (A → B) → Pulse A → Pulse B
build = {!!}
"""
        )
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["fresh_process"])
        self.assertIn(
            "refine-copattern-owner", str(result.search_stats["recursive_actions"])
        )
        self.assertIn(".readout", result.patch["replacement"])
        self.assertIn(".next", result.patch["replacement"])

    def test_ordinary_dependent_record_still_constructs(self):
        source = """{-# OPTIONS --without-K #-}
module Example where
record Package (A : Set) (B : A → Set) : Set where
  field
    value : A
    witness : B value
open Package
pack : {A : Set} {B : A → Set} → (a : A) → B a → Package A B
pack = {!!}
"""
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["fresh_process"])

    def test_inductive_record_copatterns_do_not_certify_recursion(self):
        result = self.solve(specimen().replace("  coinductive", "  inductive"))
        self.assertNotEqual(result.status, "verified")
        self.assertIsNone(result.patch)

    def test_missing_guardedness_is_not_silently_added(self):
        result = self.solve(specimen().replace("--guardedness ", ""))
        self.assertNotEqual(result.status, "verified")
        self.assertIsNone(result.patch)

    def test_uninhabited_head_cannot_use_its_own_observation(self):
        source = specimen().replace("A → Pulse A", "Pulse A")
        result = self.solve(source)
        self.assertNotEqual(result.status, "verified")
        self.assertIsNone(result.patch)

    def test_joint_prefix_does_not_edit_later_goals(self):
        source = specimen() + "\nleave : {A : Set} → A → A\nleave = {!!}\n"
        result = self.solve(source)
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertEqual(result.patch["target_goal_count"], 1)
        self.assertNotIn("leave", result.patch["replacement"])


if __name__ == "__main__":
    unittest.main()
