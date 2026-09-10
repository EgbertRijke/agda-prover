"""Search statistics cross the controller boundary even on interruption."""

import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

from agdaprover.constructor_search import ConstructorStats, constructor_tree_prove
from agdaprover.resource_budget import ResourceLimitError
from agdaprover.verifier_budget import VerifierCallLimitExceeded


class ConstructorStatisticsTests(unittest.TestCase):
    def invoke(self, observer, **options):
        return constructor_tree_prove(
            None,
            None,
            action_budget=options.get("action_budget", 10),
            timeout_seconds=1,
            max_depth=None,
            on_statistics=observer,
        )

    def test_success_and_failure_publish_once_without_changing_the_outcome(self):
        for error in (
            None,
            TimeoutError("deadline"),
            VerifierCallLimitExceeded("quota"),
            ResourceLimitError("cpu"),
            RuntimeError("protocol"),
            KeyboardInterrupt(),
        ):
            stats = ConstructorStats(actions_considered=7, premise_refinement_queries=3)
            engine = SimpleNamespace(
                stats=stats,
                solve=Mock(return_value=(), side_effect=error),
                focused_policy=SimpleNamespace(actions_scored=2),
                saw_exhaustion=False,
            )
            published = []
            with (
                self.subTest(error=type(error).__name__),
                patch(
                    "agdaprover.constructor_search._ConstructorSearch",
                    return_value=engine,
                ),
            ):
                if error is None:
                    result = self.invoke(published.append)
                    self.assertEqual(result.status, "no-proof")
                    self.assertIs(result.stats, stats)
                else:
                    with self.assertRaises(type(error)) as raised:
                        self.invoke(published.append)
                    self.assertIs(raised.exception, error)
            self.assertEqual(published, [stats])
            self.assertEqual(stats.actions_considered, 7)
            self.assertEqual(stats.premise_refinement_queries, 3)
            self.assertEqual(stats.focused["nnue_actions_scored"], 2)
            self.assertGreaterEqual(stats.elapsed_ms, 0)

    def test_empty_allowance_and_setup_failure_publish_zero_work_once(self):
        published = []
        with patch("agdaprover.constructor_search._ConstructorSearch") as setup:
            result = self.invoke(published.append, action_budget=0)
        setup.assert_not_called()
        self.assertEqual(result.status, "resource-exhausted")
        self.assertEqual(published, [result.stats])
        error = VerifierCallLimitExceeded("initial query")
        published = []
        with patch(
            "agdaprover.constructor_search._ConstructorSearch", side_effect=error
        ):
            with self.assertRaises(VerifierCallLimitExceeded) as raised:
                self.invoke(published.append)
        self.assertIs(raised.exception, error)
        self.assertEqual(len(published), 1)
        self.assertEqual(published[0].actions_considered, 0)
