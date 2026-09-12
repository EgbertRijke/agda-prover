import json
import math
import unittest
from itertools import islice
from unittest.mock import patch

from agdaprover.budget import SearchBudget, action_limit_view
from agdaprover.constructor_search import ConstructorStats


class _ManualClock:
    def __init__(self) -> None:
        self.now = 0.0

    def __call__(self) -> float:
        return self.now


class SearchBudgetTests(unittest.TestCase):
    def test_unbounded_actions_preserve_exact_costs_and_shared_deadline(self) -> None:
        clock = _ManualClock()
        budget = SearchBudget(None, 2.0, clock=clock)
        self.assertTrue(budget.charge_action(8001))
        budget.account_actions(10**20)
        self.assertEqual(budget.actions_used, 10**20 + 8001)
        self.assertIsInstance(budget.actions_used, int)
        self.assertEqual(budget.remaining_actions(), math.inf)
        self.assertFalse(budget.exhausted())
        clock.now = 2.0
        self.assertTrue(budget.exhausted())
        self.assertFalse(budget.charge_action())

    def test_unbounded_budget_still_polls_physical_resources(self) -> None:
        budget = SearchBudget(None, None)
        with patch(
            "agdaprover.budget.checkpoint", side_effect=RuntimeError("resource stop")
        ):
            for operation in (
                budget.exhausted,
                budget.remaining_actions,
                budget.charge_action,
            ):
                with (
                    self.subTest(operation=operation),
                    self.assertRaisesRegex(RuntimeError, "resource stop"),
                ):
                    operation()

    def test_action_limit_wire_view_is_strict_json_and_has_no_slice_cap(self) -> None:
        allowance = action_limit_view(SearchBudget(None, None).remaining_actions())
        self.assertEqual(
            json.dumps({"max_actions": allowance}, allow_nan=False),
            '{"max_actions": null}',
        )
        self.assertEqual(list(islice(range(8002), allowance)), list(range(8002)))
        self.assertEqual(action_limit_view(17), 17)
        stats = ConstructorStats(premise_query_limit=math.inf).to_dict()
        self.assertIsNone(stats["premise_query_limit"])
        json.dumps(stats, allow_nan=False)
        for invalid in (-1, -math.inf, math.nan):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                action_limit_view(invalid)

    def test_action_limit_rejects_invalid_configurations(self) -> None:
        for invalid in (0, -1, True, 1.5, math.inf):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                SearchBudget(invalid, None)

    def test_action_limit_is_exact(self) -> None:
        clock = _ManualClock()
        budget = SearchBudget(2, 1.0, clock=clock)
        self.assertTrue(budget.charge_action())
        self.assertTrue(budget.charge_action())
        self.assertFalse(budget.charge_action())
        self.assertEqual(budget.actions_used, 2)

    def test_every_child_uses_the_same_absolute_deadline(self) -> None:
        clock = _ManualClock()
        budget = SearchBudget(10, 1.0, clock=clock)
        clock.now = 0.75
        self.assertAlmostEqual(budget.remaining_seconds(), 0.25)
        clock.now = 1.0
        with self.assertRaises(TimeoutError):
            budget.require_time("test")

    def test_child_cannot_overdraw_its_allowance(self) -> None:
        budget = SearchBudget(2, 1.0)
        with self.assertRaises(ValueError):
            budget.account_actions(3)

    def test_omitted_wall_limit_never_expires(self) -> None:
        clock = _ManualClock()
        budget = SearchBudget(2, None, clock=clock)
        clock.now = 10_000_000.0
        self.assertFalse(budget.wall_exhausted())
        self.assertEqual(budget.require_time("test"), float("inf"))


if __name__ == "__main__":
    unittest.main()
