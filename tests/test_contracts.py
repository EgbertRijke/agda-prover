import unittest
from pathlib import Path

from agdaprover.contracts import CostMetrics, TaskSpec, task_identity


class ContractTests(unittest.TestCase):
    def test_task_identity_covers_ranker_model_toolchain_and_policy(self) -> None:
        source = Path("Example.agda")
        symbolic = TaskSpec(source, ranker="symbolic")
        neural = TaskSpec(source, ranker="nnue", model_path=Path("model.apnnue"))

        def identity(task: TaskSpec, **changes: object) -> str:
            values = {
                "mode": "prove",
                "policy_profile": "policy-a",
                "toolchain_id": "agda-a",
                "model_ids": {"primary": "model-a"},
            }
            values.update(changes)
            return task_identity(task, "source", **values)

        baseline = identity(symbolic)
        self.assertNotEqual(baseline, identity(neural))
        self.assertNotEqual(baseline, identity(symbolic, toolchain_id="agda-b"))
        self.assertNotEqual(baseline, identity(symbolic, policy_profile="policy-b"))
        self.assertNotEqual(
            baseline, identity(symbolic, model_ids={"primary": "model-b"})
        )

    def test_cost_metrics_reject_negative_or_unknown_units(self) -> None:
        cost = CostMetrics()
        cost.add(
            actions_generated=2,
            candidate_terms_checked=1,
            refinement_checks=2,
            case_split_checks=3,
            kernel_load_elapsed_ms=1.5,
        )
        self.assertEqual(cost.actions_generated, 2)
        self.assertEqual(cost.candidate_terms_checked, 1)
        self.assertEqual(cost.refinement_checks, 2)
        self.assertEqual(cost.case_split_checks, 3)
        with self.assertRaises(ValueError):
            cost.add(actions_generated=-1)
        with self.assertRaises(ValueError):
            cost.add(verifier_calls=1)


if __name__ == "__main__":
    unittest.main()
