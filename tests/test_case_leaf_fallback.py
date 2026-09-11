"""Case trees retain term construction when Agda rejects further splitting."""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.case_search import batched_case_prove
from agdaprover.constructor_search import (
    ConstructorResult,
    ConstructorStats,
    constructor_tree_prove,
)
from agdaprover.contracts import CandidateCheck
from agdaprover.validation import validate_candidate, validate_reconstruction

SOURCE = """{-# OPTIONS --safe --without-K #-}
module GuardedSequence where
open import Agda.Primitive using (Level)
data Void : Set where
data Seq {l : Level} (A : Set l) : Set l where
  stop : Seq A
  push : A → Seq A → Seq A
data Path {l : Level} {A : Set l} (x : A) : A → Set l where
  same : Path x x
absurd : {l : Level} {A : Set l} → Void → A
absurd ()
Guard : {l : Level} {A : Set l} → Seq A → Set l
Guard s = Path s stop → Void
take : {l : Level} {A : Set l} (s : Seq A) → Guard s → A
take = {!!}
"""


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class CaseLeafFallbackTests(unittest.TestCase):
    def run_batch(self, source=SOURCE, *, action_budget=128):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "GuardedSequence.agda"
            path.write_text(source)
            with AgdaSession(timeout_seconds=10) as session:
                (goal,) = session.load_module(path)
            result = batched_case_prove(
                path,
                goal,
                action_budget=action_budget,
                timeout_seconds=10,
                max_depth=None,
                focused_model=None,
                refinement_model=None,
            )
            self.assertLessEqual(result.stats.actions_considered, action_budget)
            if result.status == "solved":
                checked, trust = validate_reconstruction(
                    path, result.patch, timeout_seconds=10
                )
                self.assertTrue(checked["checked"], checked)
                self.assertTrue(checked["fresh_process"])
                self.assertEqual(trust["admitted_axioms_and_primitives"], [])
            self.assertEqual(path.read_text(), source)
            return result

    def test_function_application_closes_a_case_leaf(self):
        result = self.run_batch()
        self.assertEqual(result.status, "solved", result.diagnostic)
        self.assertGreater(result.stats.structural_leaf_closures, 0)

    def test_alias_and_constructor_names_do_not_control_the_fallback(self):
        source = SOURCE.replace("Guard s → A", "(Path s stop → Void) → A")
        for old, new in (("Seq", "Chain"), ("stop", "end"), ("push", "link")):
            source = source.replace(old, new)
        result = self.run_batch(source)
        self.assertEqual(result.status, "solved", result.diagnostic)

    def test_local_application_does_not_require_a_ready_global_eliminator(self):
        source = (
            SOURCE[: SOURCE.index("take :")]
            + """take : (Path {A = Seq Void} stop stop → Void) → Void
take = {!!}
"""
        )
        with (
            tempfile.TemporaryDirectory() as directory,
            # Isolate the local-refinement fallback; supported composition
            # can independently close this goal without a refinement query.
            patch.dict(
                "os.environ",
                {
                    "AGDAPROVER_LOCAL_ELIMINATOR_READINESS": "1",
                    "AGDAPROVER_BACKWARD_SUPPORT": "0",
                },
            ),
        ):
            path = Path(directory) / "GuardedSequence.agda"
            path.write_text(source)
            with AgdaSession(timeout_seconds=10) as session:
                (goal,) = session.load_module(path)
                result = constructor_tree_prove(
                    session,
                    goal,
                    action_budget=64,
                    timeout_seconds=10,
                    max_depth=None,
                    excluded_premises=frozenset({"take"}),
                )
            self.assertEqual(result.status, "solved", result.diagnostic)
            self.assertGreater(result.stats.local_refinement_queries, 0)
            checked, _trust = validate_candidate(
                path, goal, result.solutions[0].proof_text, timeout_seconds=10
            )
            self.assertTrue(checked["checked"])
            self.assertTrue(checked["fresh_process"])
            self.assertEqual(path.read_text(), source)

    def test_exhausted_leaf_preserves_shared_budget_and_status(self):
        def exhausted(_session, _goal, **kwargs):
            stats = ConstructorStats(actions_considered=kwargs["action_budget"])
            kwargs["on_statistics"](stats)
            return ConstructorResult(
                "resource-exhausted",
                (),
                stats,
                "leaf allowance exhausted",
            )

        with patch(
            "agdaprover.case_search.constructor_tree_prove", side_effect=exhausted
        ) as constructor:
            result = self.run_batch(action_budget=64)
        self.assertEqual(result.status, "resource-exhausted")
        self.assertIsNone(result.patch)
        self.assertEqual(result.stats.actions_considered, 64)
        constructor.assert_called_once()
        self.assertLess(constructor.call_args.kwargs["action_budget"], 64)
        self.assertLessEqual(constructor.call_args.kwargs["timeout_seconds"], 10)
        self.assertEqual(
            constructor.call_args.kwargs["excluded_premises"], frozenset({"take"})
        )
        self.assertIsNone(constructor.call_args.kwargs["recursive_call"])

    def test_rejected_cases_release_the_reserved_construction_allowance(self):
        source = """{-# OPTIONS --safe --without-K #-}
module GuardedSequence where
data Wrap (A : Set) : Set where
  wrap : A → Wrap A
take : {A B : Set} → Wrap A → (A → B) → B
take = {!!}
"""
        allowances = []

        def sliced(session, goal, **kwargs):
            allowances.append(kwargs["action_budget"])
            if len(allowances) == 1:
                # Model a useful constructor search that needs more than its
                # preliminary slice. Other local split proposals still exist.
                stats = ConstructorStats(actions_considered=kwargs["action_budget"])
                kwargs["on_statistics"](stats)
                return ConstructorResult(
                    "resource-exhausted", (), stats, "preliminary slice exhausted"
                )
            return constructor_tree_prove(session, goal, **kwargs)

        with (
            patch("agdaprover.case_search.constructor_tree_prove", side_effect=sliced),
            patch.dict("os.environ", {"AGDAPROVER_CONTEXT_BINDING": "0"}),
            # Isolate construction after case splitting from shallow closures.
            patch.object(
                AgdaSession,
                "check_complete_candidate",
                return_value=CandidateCheck(False, None, "route isolation", ()),
            ),
        ):
            result = self.run_batch(source, action_budget=180)
        self.assertEqual(result.status, "solved", result.diagnostic)
        self.assertGreaterEqual(len(allowances), 2)
        self.assertEqual(allowances[0], 64)
        self.assertGreater(allowances[1], allowances[0])
        self.assertLess(allowances[1], 180 - allowances[0])


if __name__ == "__main__":
    unittest.main()
