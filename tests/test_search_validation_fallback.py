"""A local success rejected by fresh checking must not cut off alternatives."""

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.budget import SearchBudget
from agdaprover.contracts import GoalInfo, ProverResult, TaskSpec
from agdaprover.search import (
    _finish_guided_candidate,
    _finish_verified_candidate,
    prove,
)
from agdaprover.terms import Term
from agdaprover.verification import validate_reconstruction


class ValidationOutcomeTests(unittest.TestCase):
    def test_rejection_is_retryable_but_timeout_and_missing_checker_are_not(self):
        for guided in (False, True):
            for failure, expected in (
                ({}, "unsolved"),
                ({"timed_out": True}, "resource-exhausted"),
                ({"prefix_validation": {"status": "unavailable"}}, "toolchain-error"),
            ):
                with self.subTest(guided=guided, failure=failure):
                    result = ProverResult(
                        "test", "internal-error", "test.agda", "", "symbolic"
                    )
                    kwargs = {
                        "source_file": Path("test.agda"),
                        "budget": SearchBudget(10, 2),
                        "agda_executable": "agda",
                        "agda_version": "2.8.0",
                    }
                    validation = {
                        "checked": False,
                        "timed_out": False,
                        "diagnostic": "dependent declaration rejected",
                        **failure,
                    }
                    with (
                        patch(
                            "agdaprover.search.validate_reconstruction",
                            return_value=(validation, {}),
                        ),
                        patch(
                            "agdaprover.search.reconstruct_term_as_clause",
                            return_value={"replacement": "x"},
                        ),
                        patch.object(Path, "read_text", return_value="choose = {!!}"),
                    ):
                        if guided:
                            terminal = _finish_guided_candidate(
                                result,
                                patch={"replacement": "x"},
                                proof_text="x",
                                **kwargs,
                            )
                        else:
                            terminal = _finish_verified_candidate(
                                result,
                                goal=GoalInfo(0, "A", (), (10, 14)),
                                term=Term.local("x"),
                                rendered="x",
                                **kwargs,
                            )
                    self.assertEqual(result.status, expected)
                    self.assertEqual(terminal, expected != "unsolved")
                    self.assertIsNone(result.patch)
                    self.assertIsNone(result.proof_term)
                    if not terminal:
                        self.assertEqual(
                            result.search_stats["terminal_validation_rejections"], 1
                        )


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class SearchValidationFallbackTests(unittest.TestCase):
    def test_rejected_focused_and_guided_candidates_do_not_hide_another_local(self):
        original = """{-# OPTIONS --safe --without-K #-}
module ValidationFallback where
module _ {A : Set} (x y : A) where
  choose : A
  choose = {!!}
"""
        attempts = []

        def validate(source, candidate, **kwargs):
            body = candidate.get("body", candidate["replacement"]).strip()
            attempts.append(body)
            if body == "x" or body.endswith("= x"):
                return {
                    "checked": False,
                    "timed_out": False,
                    "diagnostic": "later declaration needs the other choice",
                }, {}
            return validate_reconstruction(source, candidate, **kwargs)

        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "ValidationFallback.agda"
            source.write_text(original)
            with patch(
                "agdaprover.search.validate_reconstruction", side_effect=validate
            ):
                result = prove(
                    TaskSpec(
                        source, ranker="symbolic", timeout_seconds=10, max_candidates=80
                    )
                )
            self.assertEqual(source.read_text(), original)
        self.assertEqual(result.status, "verified", (result.diagnostics, attempts))
        self.assertTrue(
            result.proof_term.strip() in {"y", "choose = y"}, result.proof_term
        )
        self.assertTrue(result.validation["fresh_process"])
        self.assertTrue(result.validation["checked"])
        self.assertGreater(result.search_stats["terminal_validation_rejections"], 0)
        self.assertGreater(result.cost.fresh_validation_runs, 0)


if __name__ == "__main__":
    unittest.main()
