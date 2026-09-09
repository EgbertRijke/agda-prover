import unittest

from agdaprover.budget import SearchBudget


class _ManualClock:
    def __init__(self) -> None:
        self.now = 0.0

    def __call__(self) -> float:
        return self.now


class SearchBudgetTests(unittest.TestCase):
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
