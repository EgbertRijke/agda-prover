"""Composed evidence carries only actually selected input dependencies."""

import shutil
import tempfile
import time
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import Mock, patch

from agdaprover.constructor_search import _ConstructorSearch
from agdaprover.contracts import ContextEntry, GoalInfo, TaskSpec
from agdaprover.observability.policy_trace import PolicyCandidate
from agdaprover.or_policy import ORPolicyRouter
from agdaprover.ranking.evidence_policy import EvidencePolicy
from agdaprover.reasoning.evidence import (
    EvidenceApplication,
    EvidenceTerm,
    evidence_applications,
)
from agdaprover.relation_path import RelationHead, solve_relation_path
from agdaprover.search import prove

SOURCE = """{-# OPTIONS --safe --without-K #-}
module EvidenceChoices where
record Pair (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B
open Pair
map : {A B C D : Set} → (A → C) → (B → D) → Pair A B → Pair C D
map = {!!}
"""


def application(name, argument="x", *, domain="A", codomain="B"):
    return EvidenceApplication(
        EvidenceTerm(name, f"{domain} → {codomain}"), (EvidenceTerm(argument, domain),)
    )


class EvidencePolicyTests(unittest.TestCase):
    def setUp(self):
        self.goal = GoalInfo(0, "B", (), (0, 4))
        self.router = ORPolicyRouter()
        self.policy = EvidencePolicy(self.router, self.goal)

    def accept(self, selection):
        if selection.choice is not None:
            self.router.recorder.mark(
                selection.choice.decision_id, selection.choice.candidate_id
            )
        self.policy.retain(selection)

    def test_complete_order_deduplication_and_versioned_roundtrip(self):
        proposals = [application("z"), application("a"), application("z")]
        selected = self.policy.select(iter(proposals))
        self.assertEqual(selected.application.expression, "a x")
        decision = self.router.recorder.to_list()[0]
        self.assertEqual(
            [c["expression"] for c in decision["candidate_set"]], ["a x", "z x"]
        )
        self.assertEqual(decision["symbolic_order"], decision["model_order"])
        self.assertEqual(decision["family"], "evidence-application-v1")
        for candidate in self.router.recorder._decisions[0].candidates:
            self.assertEqual(PolicyCandidate.from_dict(candidate.to_dict()), candidate)
        with self.assertRaises(ValueError):
            replace(
                self.router.recorder._decisions[0].candidates[0],
                family="evidence-application-v2",
            )

    def test_exact_function_and_argument_lineage_excludes_unused_observations(self):
        function = self.policy.select(
            [application("f", codomain="B → C"), application("z")]
        )
        self.accept(function)
        argument = self.policy.select([application("g"), application("z")])
        self.accept(argument)
        unused = self.policy.select([application("h"), application("z")])
        self.accept(unused)
        composed = EvidenceApplication(
            EvidenceTerm("f x", "B → C", 1), (EvidenceTerm("g x", "B", 1),)
        )
        last = self.policy.select([composed, application("longer", codomain="C")])
        # The original symbolic tiers prioritize shallower applications.
        self.assertNotEqual(last.application, composed)
        last = self.policy.select([composed])
        self.assertIsNone(last.choice)
        self.accept(last)
        choices = self.policy.dependencies((composed.expression,))
        self.assertEqual(choices, (function.choice, argument.choice))
        self.assertNotIn(unused.choice, choices)
        self.assertEqual(self.policy.dependencies(("wrapper (f x)",)), ())
        self.assertEqual(
            EvidencePolicy(self.router, self.goal).dependencies((composed.expression,)),
            (),
        )
        self.router.recorder.mark_validated_proof(
            choices, evidence={"receipt": "unit-test"}
        )
        positives = [
            (d["decision_id"], c["expression"])
            for d in self.router.recorder.to_list()
            for c in d["candidate_set"]
            if c["outcome"] == "on-validated-proof"
        ]
        self.assertEqual([expr for _d, expr in positives], ["f x", "g x"])

    def test_omitted_decisions_preserve_candidates_and_do_not_borrow_credit(self):
        first = self.policy.select([application("f"), application("z")])
        self.accept(first)
        self.router.recorder.max_decisions = 1
        next_ = self.policy.select(
            [
                EvidenceApplication(
                    EvidenceTerm("f x", "B → C", 1), (EvidenceTerm("y", "B"),)
                ),
                EvidenceApplication(
                    EvidenceTerm("g x", "B → C", 1), (EvidenceTerm("y", "B"),)
                ),
            ]
        )
        self.assertIsNone(next_.choice)
        self.accept(next_)
        self.assertEqual(
            self.policy.dependencies((next_.application.expression,)), (first.choice,)
        )
        self.assertEqual(self.router.recorder.omitted, 1)
        large = EvidencePolicy(ORPolicyRouter(), self.goal)
        large.router.recorder.max_bytes = 1
        selected = large.select(application(f"f{i:03}") for i in range(300))
        self.assertEqual(selected.application.expression, "f000 x")
        self.assertIsNone(selected.choice)
        self.assertEqual(large.router.recorder.omitted, 1)

    def test_model_reorders_only_the_generated_batch_and_bad_scores_fall_back(self):
        model = Mock()
        model.model_id = "test"
        model.input_size = 128
        model.supports_policy_family.return_value = True
        model.accumulator.return_value = [0.0]
        model.score_feature_batches.return_value = [0.0, 2.0]
        policy = EvidencePolicy(ORPolicyRouter(refinement_model=model), self.goal)
        proposals = [application("f"), application("z")]
        self.assertEqual(policy.select(proposals).application.expression, "z x")
        record = policy.router.recorder.to_list()[0]
        self.assertEqual(set(record["model_order"]), set(record["symbolic_order"]))
        self.assertEqual(policy.router.model_items_scored, 2)
        for scores in ([float("nan"), 1.0], [1.0], []):
            model.score_feature_batches.return_value = scores
            self.assertEqual(policy.select(proposals).application.expression, "f x")
        model.score_feature_batches.reset_mock()
        self.assertIsNone(policy.select(proposals[:1]).choice)
        model.score_feature_batches.assert_not_called()

    def test_generator_preserves_actual_inputs_in_every_application_form(self):
        f, x, box = (
            EvidenceTerm("f", "A → B", 1),
            EvidenceTerm("x", "A"),
            EvidenceTerm("box", "Box A"),
        )
        proposals = list(
            evidence_applications(
                (f, x, box),
                (("map", "(A → B) → Box A → Box B"), ("project", "Box A → A")),
                endpoint_terms=frozenset(),
                relation_heads=frozenset(),
            )
        )
        by_expression = {p.expression: p for p in proposals}
        self.assertEqual(by_expression["f x"].function, f)
        self.assertEqual(by_expression["f x"].arguments, (x,))
        self.assertEqual(by_expression["map f box"].arguments, (f, box))
        self.assertEqual(by_expression["project box"].arguments, (box,))
        self.assertTrue(all(p.type_text == "" for p in proposals))

    def test_relation_path_reports_used_seeds_and_operators_only(self):
        session = Mock()
        session.infer_type.side_effect = lambda _s, **kw: {"follow p q": "R a c"}.get(
            kw["expression"]
        )
        result = solve_relation_path(
            session,
            Mock(),
            GoalInfo(0, "R a c", (), (0, 4)),
            (RelationHead("follow", "{x y z : A} → R x y → R y z → R x z", 0),),
            query_budget=10,
            deadline=time.monotonic() + 10,
            seed_terms=(("p", "R a b"), ("q", "R b c"), ("unused", "R d e")),
            prefix_heads={"R": 2},
        )
        self.assertEqual(result.expression, "follow p q")
        self.assertEqual(result.inputs, frozenset({"follow", "p", "q"}))

    def test_kernel_rejection_meta_or_interruption_have_distinct_outcomes(self):
        for outcome, expected in (
            (None, "invalid"),
            ("_B_123", "budget-censored"),
            (TimeoutError("budget"), "budget-censored"),
        ):
            with self.subTest(outcome=outcome):
                router, session, state = ORPolicyRouter(), Mock(), object()
                session.infer_type = Mock()
                if isinstance(outcome, Exception):
                    session.infer_type.side_effect = outcome
                else:
                    session.infer_type.return_value = outcome
                engine = _ConstructorSearch(
                    session,
                    action_budget=2,
                    deadline=time.monotonic() + 10,
                    max_depth=None,
                    solution_limit=1,
                    focused_model=None,
                    refinement_model=None,
                    policy_router=router,
                    excluded_premises=frozenset(),
                    defer_concrete_premises=False,
                    recursive_call=None,
                    preferred_constructor_arity=None,
                    require_recursive_call=False,
                )
                engine._ordered_premise_actions = Mock(return_value=())
                engine._has_opaque_type_head = Mock(return_value=True)
                goal = GoalInfo(
                    0,
                    "B",
                    (
                        ContextEntry("f", "A → B", True),
                        ContextEntry("g", "A → B", True),
                        ContextEntry("x", "A", True),
                    ),
                    (0, 4),
                )
                if isinstance(outcome, Exception):
                    with self.assertRaises(TimeoutError):
                        engine._solve_with_contextual_evidence(
                            state, goal, action_slice=512
                        )
                else:
                    self.assertEqual(
                        engine._solve_with_contextual_evidence(
                            state, goal, action_slice=512
                        ),
                        (),
                    )
                # A larger local allocation cannot expand the parent's budget.
                self.assertEqual(session.infer_type.call_count, 1)
                record = router.recorder.to_list()[0]
                first, second = record["candidate_set"]
                self.assertTrue(first["explored"])
                self.assertEqual(first["outcome"], expected)
                self.assertFalse(second["explored"])
                self.assertEqual(second["outcome"], "budget-censored")
                self.assertEqual(engine._evidence_choices(state, goal, "f x"), ())
                self.assertEqual(engine._evidence_choices(object(), goal, "f x"), ())
                session.commit_proof_action.assert_not_called()


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class EvidenceCreditKernelTests(unittest.TestCase):
    def test_record_maps_receive_fresh_exact_credit_and_failed_validation_does_not(
        self,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "EvidenceChoices.agda"
            path.write_text(SOURCE)
            result = prove(TaskSpec(path, timeout_seconds=15, ranker="symbolic"))
            self.assertEqual(result.status, "verified", result.diagnostics)
            evidence = [
                d
                for d in result.policy_trace
                if d["family"] == "evidence-application-v1"
            ]
            self.assertTrue(evidence)
            positives = [
                c
                for d in evidence
                for c in d["candidate_set"]
                if c["outcome"] == "on-validated-proof"
            ]
            self.assertTrue(positives)
            self.assertTrue(all(c["explored"] for c in positives))
            self.assertEqual(path.read_text(), SOURCE)
            self.assertTrue(result.validation["fresh_process"])
            self.assertFalse(
                any(d.get("kind") == "training-trace" for d in result.diagnostics)
            )
            with patch(
                "agdaprover.search.validate_reconstruction",
                return_value=(
                    {
                        "fresh_process": True,
                        "checked": False,
                        "timed_out": True,
                        "exit_status": None,
                        "diagnostic": "deadline",
                    },
                    {},
                ),
            ):
                rejected = prove(TaskSpec(path, timeout_seconds=15, ranker="symbolic"))
            self.assertEqual(rejected.status, "resource-exhausted")
            self.assertTrue(rejected.policy_trace)
            self.assertFalse(
                any(
                    c["outcome"] == "on-validated-proof"
                    for d in rejected.policy_trace
                    for c in d["candidate_set"]
                )
            )
            self.assertEqual(path.read_text(), SOURCE)


if __name__ == "__main__":
    unittest.main()
