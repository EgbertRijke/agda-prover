"""Source observations are proposals, never cuts or constructor authority."""

import shutil
import tempfile
import unittest
from pathlib import Path

from agdaprover.contracts import TaskSpec
from agdaprover.joint import _search_state_digest, prove_joint_prefix

PREFIX = """{-# OPTIONS --safe --without-K #-}
module Example where
data Flag : Set where first second : Flag
data _≈_ (x : Flag) : Flag → Set where
  witness : {y : Flag} → x ≈ y
infix 6 _≈_
"""


class ObservationStateTests(unittest.TestCase):
    def test_continuation_kinds_have_distinct_search_identities(self):
        self.assertEqual(
            len(
                {
                    _search_state_digest(
                        "source", frozenset(), False, focused, observed
                    )
                    for focused in (False, True)
                    for observed in (False, True)
                }
            ),
            4,
        )


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class ObservationFallbackTests(unittest.TestCase):
    def run_joint(self, source, *, max_candidates=160):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.agda"
            path.write_text(source)
            result = prove_joint_prefix(
                TaskSpec(path, max_candidates=max_candidates, timeout_seconds=15)
            )
            self.assertEqual(path.read_text(), source)
        return result

    def assert_verified(self, result):
        self.assertEqual(result.status, "verified", result.diagnostics)
        self.assertTrue(result.validation["checked"])
        self.assertTrue(result.validation["fresh_process"])
        self.assertGreater(result.search_stats["observation_fallbacks_resumed"], 0)

    def test_defined_function_application_is_not_a_constructor_pattern(self):
        # Both rigid heads exist in scope, but only Agda can establish whether
        # they are legal patterns. Rejecting that proposal must preserve search.
        source = (
            PREFIX
            + """pretend : Flag → Flag
pretend x = x
convert : Flag → Flag
convert = {!!}
law-first : convert (pretend first) ≈ first
law-first = {!!}
law-second : convert (pretend second) ≈ second
law-second = {!!}
"""
        )
        for variant in (source, source.replace("pretend", "unrelated-name")):
            with self.subTest(source=variant):
                result = self.run_joint(variant)
                self.assert_verified(result)
                self.assertGreater(result.search_stats["dead_states"], 0)

    def test_nullary_observation_cannot_discard_a_later_valid_choice(self):
        source = (
            PREFIX
            + """data Void : Set where
data Unit : Set where star : Unit
Need : Flag → Set
Need first = Void
Need second = Unit
chosen : Flag
chosen = {!!}
hint : chosen ≈ first
hint = {!!}
required : Need chosen
required = {!!}
"""
        )
        result = self.run_joint(source)
        self.assert_verified(result)
        self.assertIn("chosen = second", result.proof_term)

    def test_rejected_observation_keeps_the_original_action_budget(self):
        source = (
            PREFIX
            + """pretend : Flag → Flag
pretend x = x
convert : Flag → Flag
convert = {!!}
law-first : convert (pretend first) ≈ first
law-first = {!!}
law-second : convert (pretend second) ≈ second
law-second = {!!}
"""
        )
        result = self.run_joint(source, max_candidates=1)
        self.assertEqual(result.status, "resource-exhausted", result.diagnostics)
        self.assertLessEqual(result.candidates_generated, 1)
        self.assertIsNone(result.patch)
        self.assertIsNone(result.validation)
