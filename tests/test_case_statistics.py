"""Nested case work must survive normal returns and interrupted search."""

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.case_search import CaseBatchResult, batched_case_prove
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.resource_budget import ResourceLimitError
from agdaprover.search import prove
from agdaprover.verifier_budget import VerifierCallLimitExceeded


def completed_work(stats):
    stats.actions_considered = 7
    stats.actions_generated = 11
    stats.refinement_queries = 3
    stats.case_queries = 2
    stats.premise_catalog_queries = 5
    stats.goal_inspections = 4
    stats.kernel_loads = 2
    stats.kernel_load_elapsed_ms = 8.5
    stats.model_calls = 13
    stats.model_batches = 3
    stats.model_elapsed_ms = 1.25
    stats.source_bytes_materialized = 91
    stats.source_bytes_written = 91


class CaseStatisticsTests(unittest.TestCase):
    def test_callback_publishes_once_and_preserves_return_or_exception(self):
        for error in (
            None,
            TimeoutError("deadline"),
            VerifierCallLimitExceeded("quota"),
            ResourceLimitError("cpu"),
            RuntimeError("protocol"),
            KeyboardInterrupt(),
        ):
            observed = []

            def run(*args, stats, failure=error, **kwargs):
                completed_work(stats)
                if failure is not None:
                    raise failure
                return CaseBatchResult("no-proof", None, None, stats)

            with (
                self.subTest(error=type(error).__name__),
                patch("agdaprover.case_search._batched_case_prove", side_effect=run),
            ):
                options = dict(
                    action_budget=20,
                    timeout_seconds=1,
                    max_depth=None,
                    focused_model=None,
                    refinement_model=None,
                    on_statistics=observed.append,
                )
                if error is None:
                    result = batched_case_prove(Path("unused"), None, **options)
                    self.assertEqual(result.status, "no-proof")
                    self.assertIs(result.stats, observed[0])
                else:
                    with self.assertRaises(type(error)) as raised:
                        batched_case_prove(Path("unused"), None, **options)
                    self.assertIs(raised.exception, error)
            self.assertEqual(len(observed), 1)
            self.assertEqual(observed[0].actions_considered, 7)
            self.assertEqual(observed[0].model_calls, 13)
            self.assertGreaterEqual(observed[0].elapsed_ms, 0)

    def test_source_failure_publishes_zero_work_once(self):
        observed = []
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(FileNotFoundError):
                batched_case_prove(
                    Path(directory) / "Missing.agda",
                    None,
                    action_budget=20,
                    timeout_seconds=1,
                    max_depth=None,
                    focused_model=None,
                    refinement_model=None,
                    on_statistics=observed.append,
                )
        self.assertEqual(len(observed), 1)
        self.assertEqual(observed[0].actions_considered, 0)


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class CaseStatisticsIntegrationTests(unittest.TestCase):
    def test_both_controllers_retain_nested_work_on_resource_exhaustion(self):
        source_text = """{-# OPTIONS --safe --without-K #-}
module CaseWork where
data Box (A : Set) : Set where wrap : A → Box A
unpack : (A : Set) → Box A → A
unpack = {!!}
"""

        def interrupted(*args, stats, **kwargs):
            completed_work(stats)
            raise ResourceLimitError("interrupted nested case search")

        for controller in (prove, prove_joint_prefix):
            with (
                self.subTest(controller=controller.__name__),
                tempfile.TemporaryDirectory() as directory,
                patch(
                    "agdaprover.case_search._batched_case_prove",
                    side_effect=interrupted,
                ) as child,
            ):
                source = Path(directory) / "CaseWork.agda"
                source.write_text(source_text)
                result = controller(
                    TaskSpec(source, ranker="symbolic", timeout_seconds=10)
                )
                self.assertEqual(source.read_text(), source_text)
            self.assertEqual(child.call_count, 1)
            self.assertEqual(result.status, "resource-exhausted", result.diagnostics)
            self.assertIsNone(result.patch)
            self.assertEqual(result.model_calls, 13)
            self.assertEqual(result.model_elapsed_ms, 1.25)
            self.assertEqual(result.cost.model_items_scored, 13)
            self.assertEqual(result.cost.model_batches, 3)
            self.assertEqual(result.cost.refinement_checks, 3)
            self.assertEqual(result.cost.case_split_checks, 2)
            self.assertGreaterEqual(result.cost.actions_expanded, 7)
            self.assertGreaterEqual(result.verifier_calls, 10)
            stats = (
                result.search_stats["case_batch"]
                if controller is prove
                else result.search_stats
            )
            self.assertEqual(stats["model_calls"], 13)
            self.assertEqual(stats["model_batches"], 3)
            self.assertGreaterEqual(stats["premise_catalog_queries"], 5)
            self.assertGreaterEqual(stats["kernel_load_elapsed_ms"], 8.5)


if __name__ == "__main__":
    unittest.main()
