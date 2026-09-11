"""Sorts are not absurd-pattern candidates, regardless of their spelling."""

import unittest

from agdaprover.contracts import ContextEntry, GoalInfo
from agdaprover.zero_constructor import generate_zero_constructor_actions


class ZeroConstructorSortTests(unittest.TestCase):
    def test_kernel_identified_sort_is_not_an_absurd_elimination(self):
        for name in ("Set", "Cosmos", "Local.Types"):
            with self.subTest(name=name):
                goal = GoalInfo(
                    0,
                    "Result",
                    (
                        ContextEntry("Carrier", f"{name} level", True),
                        ContextEntry("impossible", "EmptyFamily index", True),
                    ),
                    (1, 5),
                    universe_names=frozenset((name,)),
                )
                (action,) = generate_zero_constructor_actions(goal, max_actions=1)
                self.assertEqual(action.scrutinee.name, "impossible")

    def test_a_shadowed_sort_spelling_is_not_classified_by_name(self):
        goal = GoalInfo(
            0,
            "Result",
            (ContextEntry("impossible", "Set", True),),
            (1, 5),
            universe_names=frozenset(("Cosmos",)),
        )
        (action,) = generate_zero_constructor_actions(goal, max_actions=1)
        self.assertEqual(action.scrutinee.name, "impossible")

    def test_sort_valued_arguments_remain_available_to_other_applications(self):
        goal = GoalInfo(
            0,
            "Result",
            (
                ContextEntry("Carrier", "Cosmos", True),
                ContextEntry("reject", "Cosmos → Void", True),
            ),
            (1, 5),
            universe_names=frozenset(("Cosmos",)),
        )
        (action,) = generate_zero_constructor_actions(goal, max_actions=1)
        self.assertIn("reject Carrier", action.expression)
