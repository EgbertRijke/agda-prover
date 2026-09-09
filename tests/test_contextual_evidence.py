"""Generic field/function evidence, independent of mathematical vocabulary."""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

from agdaprover.bridge.compat_p0 import AgdaBridgeError, AgdaSession
from agdaprover.bridge.contracts import (
    BridgeBudget,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
)
from agdaprover.constructor_search import ProofPlan, constructor_tree_prove
from agdaprover.contracts import TaskSpec
from agdaprover.joint import (
    _can_amortize_budget_widening,
    _DeferredBudgetWidening,
    _search_state_digest,
    prove_joint_prefix,
)
from agdaprover.reasoning.evidence import (
    EvidenceTerm,
    evidence_applications,
    family_names,
    telescope_introduction,
)
from agdaprover.reconstruction import apply_source_edit
from agdaprover.relation_path import parse_relation, relation_operation_shape
from agdaprover.resource_budget import ResourceLimitError
from agdaprover.step import propose_step
from agdaprover.validation import validate_candidate


class EvidenceProposalTests(unittest.TestCase):
    def test_restart_policy_respects_the_shared_remaining_allowance(self):
        self.assertFalse(_can_amortize_budget_widening(500, 9))
        self.assertFalse(_can_amortize_budget_widening(160, 1))
        self.assertTrue(_can_amortize_budget_widening(161, 1))
        self.assertTrue(_can_amortize_budget_widening(8000, 31))

    def test_only_an_exhausted_local_slice_requires_a_wider_replay(self):
        pending = _DeferredBudgetWidening(Mock(), "source", 6, 2, 9, 160)
        self.assertFalse(pending.exhausted(9))
        self.assertFalse(pending.exhausted(168))
        self.assertTrue(pending.exhausted(169))
        self.assertTrue(pending.exhausted(170))

    def test_wider_budget_state_cannot_alias_a_declaration_widening(self):
        self.assertNotEqual(
            _search_state_digest("body", frozenset(), True),
            _search_state_digest("body", frozenset({"budget-widened-v1"})),
        )
        self.assertNotEqual(
            _search_state_digest("body", frozenset()),
            _search_state_digest("body", frozenset(), True),
        )
        self.assertEqual(
            _search_state_digest("body", frozenset({"b", "a"})),
            _search_state_digest("body", frozenset({"a", "b"}), False),
        )

    def test_malformed_family_observation_is_not_a_recognition(self):
        self.assertEqual(
            family_names((("Bad", "("), ("Good", "A → A → Set"))), {"Good": 2}
        )

    def test_hidden_telescope_is_capture_free_and_preserved_as_lambda(self):
        introduction = telescope_introduction(
            "A → {x y : A} → R x y", frozenset({"arg0"})
        )
        self.assertEqual(introduction, "λ arg1 {x = arg2} {y = arg3} → ?")
        plan = ProofPlan(introduction, (ProofPlan("f arg1 arg2 arg3"),))
        self.assertEqual(
            plan.clause_parts(),
            ((), "λ arg1 {x = arg2} {y = arg3} → (f arg1 arg2 arg3)"),
        )
        for unsupported in ("A → B", "{x = z : A} → B", "⦃x : A⦄ → {y : A} → B"):
            self.assertIsNone(telescope_introduction(unsupported, frozenset()))

    def test_prefix_relation_requires_typed_family_and_preserves_parameters(self):
        families = family_names((("Link", "(A : Set) → A → A → Set"),))
        view = parse_relation("Link A (f x) y", prefix_heads=families)
        self.assertEqual(
            (view.left, view.operator, view.right), ("(f x)", "Link A", "y")
        )
        self.assertIsNone(parse_relation("function argument result"))
        self.assertIsNone(
            parse_relation(
                "Link B x y", expected_operator="Link A", prefix_heads=families
            )
        )
        for text in (
            "Link A x",
            "(p : Link A x y) → Link A y x",
            "Link A (x y",
            "Link A x {y}",
        ):
            with self.subTest(text=text):
                self.assertIsNone(parse_relation(text, prefix_heads=families))

    def test_operator_wiring_is_generic_and_not_assumed(self):
        families = {"R": 2}
        self.assertEqual(
            relation_operation_shape(
                "{x y : A} → R x y → R y x", prefix_heads=families
            ),
            "reverse",
        )
        self.assertEqual(
            relation_operation_shape(
                "{x y z : A} → R x y → R y z → R x z", prefix_heads=families
            ),
            "chain",
        )
        self.assertEqual(
            relation_operation_shape(
                "{x y : A} → R (f x) (f y) → R x y", prefix_heads=families
            ),
            "reflect",
        )
        self.assertIsNone(
            relation_operation_shape("R x y → S y x", prefix_heads=families)
        )
        self.assertIsNone(
            relation_operation_shape("R x y → R z w → R x w", prefix_heads=families)
        )

    def test_dependent_function_application_uses_observed_domain(self):
        terms = (
            EvidenceTerm("field w", "(z : A) → Link (anchor w) z", 1),
            EvidenceTerm("x", "A"),
            EvidenceTerm("bad", "B"),
        )
        proposals = tuple(
            evidence_applications(
                terms,
                (),
                endpoint_terms=frozenset({"x"}),
                relation_heads=frozenset({"Link"}),
            )
        )
        self.assertEqual([p.expression for p in proposals], ["(field w) x"])
        self.assertEqual(proposals[0].type_text, "")


class EvidenceFailureTests(unittest.TestCase):
    def test_inference_does_not_hide_resource_or_protocol_failures(self):
        session = AgdaSession.__new__(AgdaSession)
        session._budget = BridgeBudget()
        session._session = Mock()
        for method in (session.infer_type, session._expanded_refinement):
            for failure, exception in (
                (BridgeFailure.TIMEOUT, TimeoutError),
                (BridgeFailure.RESOURCE_EXHAUSTED, ResourceLimitError),
                (BridgeFailure.PROTOCOL_FAILURE, AgdaBridgeError),
            ):
                with self.subTest(method=method.__name__, failure=failure):
                    session._session.infer.side_effect = BridgeError(
                        failure,
                        BridgeDiagnostic("test-failure", "infer", "error", "failure"),
                    )
                    with self.assertRaises(exception):
                        method(Mock(), goal_id=0, expression="f x")
            session._session.infer.side_effect = BridgeError(
                BridgeFailure.AGDA_REJECTION,
                BridgeDiagnostic("test-rejection", "infer", "error", "rejected"),
            )
            self.assertIsNone(method(Mock(), goal_id=0, expression="f x"))


HEADER = """{-# OPTIONS --safe --without-K --exact-split #-}
module Evidence where
open import Agda.Primitive using (Level; _⊔_)
data Link {l : Level} {A : Set l} (x : A) : A → Set l where
  stay : Link x x
infix 6 _≈_
_≈_ : {l : Level} {A : Set l} → A → A → Set l
x ≈ y = Link x y
turn : {l : Level} {A : Set l} {x y : A} → x ≈ y → y ≈ x
turn stay = stay
follow : {l : Level} {A : Set l} {x y z : A} → x ≈ y → y ≈ z → x ≈ z
follow stay q = q
lift : {l k : Level} {A : Set l} {B : Set k} (f : A → B) {x y : A} → Link x y → Link (f x) (f y)
lift f stay = stay
move : {A : Set} (P : A → Set) {x y : A} → Link x y → P x → P y
move P stay d = d
record Bundle {l k : Level} (A : Set l) (R : A → A → Set k) : Set (l ⊔ k) where
  constructor bundle
  field
    anchor : A
    reach : (x : A) → R anchor x
open Bundle public
record Tuple {l k : Level} (A : Set l) (B : Set k) : Set (l ⊔ k) where
  constructor tuple
  field
    first : A
    second : B
open Tuple public
merge : {A B : Set} {s t : Tuple A B} → Link (first s) (first t) → Link (second s) (second t) → Link s t
merge {s = tuple a b} {tuple .a .b} stay stay = stay
cancel : {A : Set} {x y : A} (p : Link x y) → Link (follow (turn p) p) stay
cancel stay = stay
data Choice (A B : Set) : Set where
  left : A → Choice A B
  right : B → Choice A B
data Void : Set where
absurd : {A : Set} → Void → A
absurd ()
faithful-left : {A B : Set} {x y : A} → Link (left {A} {B} x) (left y) → Link x y
faithful-left stay = stay
separate : {A B : Set} {x : A} {y : B} → Link (left x) (right y) → Void
separate ()
connect : {A : Set} → Bundle A Link → {x y : A} → Link x y
connect C {x} {y} = follow (turn (reach C x)) (reach C y)
"""


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class EvidenceKernelTests(unittest.TestCase):
    def check(self, signature, *, expected=True):
        source = HEADER + "\ngoal : " + signature + "\ngoal = {!!}\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Evidence.agda"
            path.write_text(source)
            with AgdaSession(timeout_seconds=20) as session:
                (goal,) = session.load_module(path)
                result = constructor_tree_prove(
                    session,
                    goal,
                    action_budget=180,
                    timeout_seconds=15,
                    max_depth=None,
                    excluded_premises=frozenset({"goal"}),
                )
            if not expected:
                self.assertNotEqual(result.status, "solved", result.stats.to_dict())
                return None
            self.assertEqual(result.status, "solved", result.stats.to_dict())
            expression = result.solutions[0].proof_text
            validation, trust = validate_candidate(
                path, goal, expression, timeout_seconds=10
            )
            self.assertTrue(validation["checked"], validation)
            self.assertTrue(validation["fresh_process"])
            self.assertEqual(trust["admitted_axioms_and_primitives"], [])
            self.assertEqual(path.read_text(), source)
            return expression, result.stats

    def test_dependent_record_field_composes_without_case_splitting(self):
        expression, stats = self.check(
            "{l : Level} {A : Set l} → Bundle A Link → (x y : A) → Link x y"
        )
        self.assertIn("reach", expression)
        self.assertGreater(stats.evidence_terms, 0)
        self.assertGreater(stats.evidence_path_queries, 0)

    def test_unpacked_function_has_the_same_capability(self):
        self.check(
            "{l : Level} {A : Set l} → (c : A) → ((z : A) → c ≈ z) → (x y : A) → x ≈ y"
        )

    def test_arbitrary_relation_uses_only_supplied_conditional_operations(self):
        self.check(
            "{A : Set} (R : A → A → Set) → ({x y : A} → R x y → R y x) → ({x y z : A} → R x y → R y z → R x z) → Bundle A R → (x y : A) → R x y"
        )

    def test_trailing_hidden_endpoints_are_available_to_composition(self):
        self.check("{l : Level} {A : Set l} → Bundle A Link → {x y : A} → Link x y")

    def test_observed_function_transports_and_composes_evidence(self):
        self.check(
            "{A B : Set} (f : A → B) (g : B → A) (b : B) → ((x : A) → Link (g (f x)) x) → ((z : B) → Link b z) → (x : A) → Link (g b) x"
        )

    def test_projection_map_constrains_a_structured_function_argument(self):
        self.check("{A B : Set} → Bundle (Tuple A B) Link → Bundle A Link")

    def test_binary_evidence_refinement_uses_instantiated_fields(self):
        self.check(
            "{A B : Set} → Bundle A Link → Bundle B Link → Bundle (Tuple A B) Link"
        )

    def test_dependent_evidence_is_transferred_using_a_supplied_operation(self):
        self.check("{A : Set} {P : A → Set} (a b : A) → Link a b → P a → P b")

    def test_structured_builder_preserves_evidence_for_dependent_transfer(self):
        expression, _ = self.check(
            "{A : Set} {P : A → Set} {U : Set} → "
            "(make : Bundle A Link → ((z : A) → Bundle (P z) Link) → U) → "
            "Bundle A Link → (a : A) → Bundle (P a) Link → U"
        )
        self.assertIn("make", expression)

    def test_pattern_elimination_inside_a_dependent_record_field(self):
        self.check("{A : Set} → Bundle A Link → (x y : A) → Bundle (Link x y) Link")

    def test_supplied_reflection_law_uses_structured_evidence(self):
        self.check("{A B : Set} → Bundle (Choice A B) Link → A → Bundle A Link")

    def test_projected_value_elimination_preserves_the_record(self):
        self.check("{A B : Set} → Bundle (Choice A B) Link → (B → Void) → A")

    def test_relational_consequence_instantiates_supplied_hidden_endpoints(self):
        self.check("{A B : Set} → Bundle (Choice A B) Link → A → B → Void")

    def test_no_unprovided_reversal_or_composition_is_assumed(self):
        self.check(
            "{A : Set} (R : A → A → Set) → Bundle A R → (x y : A) → R x y",
            expected=False,
        )

    def test_pattern_elimination_does_not_assume_axiom_K(self):
        self.check("{A : Set} {x : A} (p : Link x x) → Link p stay", expected=False)

    def test_feature_can_be_disabled_without_disabling_ordinary_search(self):
        with patch.dict("os.environ", {"AGDAPROVER_CONTEXTUAL_EVIDENCE": "0"}):
            _, stats = self.check("{A : Set} → A → A")
        self.assertFalse(stats.contextual_evidence_enabled)
        self.assertEqual(stats.evidence_inference_queries, 0)
        self.assertEqual(stats.evidence_path_queries, 0)

    def test_joint_completion_inside_a_record_preserves_its_sibling(self):
        source = (
            HEADER + "\ngoal : {A : Set} → A → Tuple A (A → A)\ngoal a = tuple a {!!}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Evidence.agda"
            path.write_text(source)
            result = prove_joint_prefix(
                TaskSpec(path, timeout_seconds=15, max_candidates=180)
            )
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertTrue(result.validation and result.validation["fresh_process"])
            self.assertIn("goal a = tuple a", apply_source_edit(source, result.patch))
            self.assertEqual(path.read_text(), source)

    def test_step_introduction_inside_a_record_preserves_its_sibling(self):
        source = (
            HEADER + "\ngoal : {A : Set} → A → Tuple A (A → A)\ngoal a = tuple a {!!}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Evidence.agda"
            path.write_text(source)
            result = propose_step(TaskSpec(path, timeout_seconds=15))
            self.assertEqual(result.status, "accepted-step", result.diagnostics)
            self.assertEqual(result.action["source_edit"]["style"], "term")
            self.assertIn(
                "goal a = tuple a",
                apply_source_edit(source, result.action["source_edit"]),
            )
            self.assertTrue(result.action["reconstruction_validation"]["loaded"])
            self.assertEqual(path.read_text(), source)

    def test_projection_views_share_an_endpoint_key(self):
        families = {"Link": 2}
        a = parse_relation("Link (anchor w) (reach w x)", prefix_heads=families)
        b = parse_relation("Link (w .anchor) (w .reach x)", prefix_heads=families)
        self.assertEqual(a.key, b.key)


if __name__ == "__main__":
    unittest.main()
