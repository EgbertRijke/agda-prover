"""Shared, kernel-checked composition into contextual type families."""

from __future__ import annotations

import os
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.constructor_search import constructor_tree_prove
from agdaprover.reasoning.evidence import (
    EvidenceTerm,
    evidence_applications,
    ready_evidence_declarations,
)
from agdaprover.validation import validate_candidate

MAP = ("convert", "{A B C : Set} → (B → C) → Container A B → Container A C")
CONSUMER = ("consume", "{A B : Set} → Container A (F B) → F (Container A B)")
TERMS = (EvidenceTerm("f", "B → F C"), EvidenceTerm("v", "Container A B"))


class SuppliedMapProposalTests(unittest.TestCase):
    def test_ready_function_and_structured_input_support_a_complete_prefix(self):
        heads = tuple(
            ready_evidence_declarations("F (Container A C)", TERMS, (MAP, CONSUMER))
        )
        self.assertEqual(heads, (MAP, CONSUMER))
        proposals = tuple(
            evidence_applications(
                TERMS, heads, endpoint_terms=frozenset(), relation_heads=frozenset()
            )
        )
        complete = next(p for p in proposals if p.expression == "convert f v")
        self.assertEqual(complete.type_text, "")
        self.assertEqual(complete.depth, 1)
        # A head comparison only proposes the consumer; it does not certify
        # that the unchanged input has its required instantiated type.
        self.assertIn("consume v", [p.expression for p in proposals])

    def test_no_invented_function_or_scope_members(self):
        for terms in (
            (),
            TERMS[:1],
            TERMS[1:],
            (EvidenceTerm("f", "{T : Set} → T → T"), TERMS[1]),
        ):
            heads = tuple(
                ready_evidence_declarations("F (Container A C)", terms, (MAP,))
            )
            self.assertEqual(heads, ())
        self.assertEqual(
            tuple(ready_evidence_declarations("F (Container A C)", TERMS, ())), ()
        )
        self.assertEqual(
            tuple(ready_evidence_declarations("G (Container A C)", TERMS, (CONSUMER,))),
            (),
        )

    def test_wrong_structure_is_not_a_supported_input(self):
        wrong = (TERMS[0], EvidenceTerm("v", "Other A B"))
        self.assertEqual(
            tuple(
                ready_evidence_declarations("F (Container A C)", wrong, (MAP, CONSUMER))
            ),
            (),
        )
        proposals = tuple(
            evidence_applications(
                wrong, (MAP,), endpoint_terms=frozenset(), relation_heads=frozenset()
            )
        )
        self.assertNotIn("convert f v", [p.expression for p in proposals])

    def test_infix_operands_are_not_confused_with_the_application_head(self):
        declarations = (
            ("act", "{P Q R : Set} → (Q → R) → P ◇ Q → P ◇ R"),
            ("finish", "{P Q : Set} → (_◇_) P (F Q) → F (P ◇ Q)"),
        )
        terms = (TERMS[0], EvidenceTerm("v", "A ◇ B"))
        heads = tuple(ready_evidence_declarations("F (A ◇ C)", terms, declarations))
        self.assertEqual(heads, declarations)
        proposals = tuple(
            evidence_applications(
                terms, heads, endpoint_terms=frozenset(), relation_heads=frozenset()
            )
        )
        self.assertIn("act f v", [p.expression for p in proposals])
        self.assertIn("finish v", [p.expression for p in proposals])

    def test_malformed_views_do_not_supply_an_application_head(self):
        self.assertEqual(
            tuple(
                ready_evidence_declarations(
                    "F (Container A C)", (EvidenceTerm("v", "(bad"),), (MAP, CONSUMER)
                )
            ),
            (),
        )
        self.assertEqual(
            tuple(ready_evidence_declarations("(bad", TERMS, (MAP, CONSUMER))), ()
        )
        self.assertEqual(
            tuple(
                ready_evidence_declarations(
                    "F (Container A C)", TERMS, (("bad", "X → ("),)
                )
            ),
            (),
        )

    def test_renaming_and_application_depth_do_not_change_the_rule(self):
        renamed = (("act", MAP[1].replace("Container", "Wrapper")),)
        terms = (EvidenceTerm("k", "B → F C", 2), EvidenceTerm("w", "Wrapper A B", 3))
        heads = tuple(ready_evidence_declarations("F (Wrapper A C)", terms, renamed))
        proposals = tuple(
            evidence_applications(
                terms, heads, endpoint_terms=frozenset(), relation_heads=frozenset()
            )
        )
        self.assertEqual(
            next(p.depth for p in proposals if p.expression == "act k w"), 4
        )

    def test_enumeration_observes_the_callers_resource_checkpoint(self):
        with patch(
            "agdaprover.reasoning.evidence.checkpoint",
            side_effect=RuntimeError("cancelled"),
        ):
            with self.assertRaisesRegex(RuntimeError, "cancelled"):
                tuple(ready_evidence_declarations("F (Container A C)", TERMS, (MAP,)))


SOURCE = """{-# OPTIONS --safe --without-K --exact-split #-}
module SuppliedEvidence where
data Container (A B : Set) : Set where
  left : A → Container A B
  right : B → Container A B
convert : {A B C : Set} → (B → C) → Container A B → Container A C
convert f (left a) = left a
convert f (right b) = right (f b)
record Operations (F : Set → Set) : Set₁ where
  field
    inject : {X : Set} → X → F X
    transform : {X Y : Set} → (X → Y) → F X → F Y
module Experiment (F : Set → Set) (ops : Operations F) where
  open Operations ops
  consume : {A B : Set} → Container A (F B) → F (Container A B)
  consume (left a) = inject (left a)
  consume (right b) = transform right b
  goal : {A B C : Set} → (B → F C) → Container A B → F (Container A C)
  goal {A} {B} {C} f v = {!!}
"""
NATIVE = (
    Path(__file__).resolve().parents[1]
    / "native/agda-bridge/target/agdaprover-agda-bridge-2.8"
)


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_SCOPE") == "1"
    and NATIVE.is_file()
    and shutil.which("agda"),
    "opt-in native scoped-retrieval profile is required",
)
class SuppliedMapKernelTests(unittest.TestCase):
    def check_composition(self, source, expected_type):
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.dict(
                os.environ,
                {
                    "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                    "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                    "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                    "AGDAPROVER_SCOPED_DEPENDENCIES": "0",
                    "AGDAPROVER_SCOPED_QUERY_VIEWS": "0",
                    "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "0",
                },
            ),
        ):
            path = Path(directory) / "SuppliedEvidence.agda"
            path.write_text(source)
            with AgdaSession(timeout_seconds=20) as session:
                (goal,) = session.load_module(path)
                state = session.current_state()
                partial = session.infer_type(
                    state, goal_id=goal.goal_id, expression="convert f"
                )
                complete = session.infer_type(
                    state, goal_id=goal.goal_id, expression="convert f v"
                )
                self.assertRegex(partial, r"_[^\s]*_\d+")
                self.assertEqual(complete, expected_type)
                self.assertEqual(session.current_state(), state)
                with patch(
                    "agdaprover.constructor_search.ready_evidence_declarations",
                    side_effect=lambda *args: iter(()),
                ):
                    control = constructor_tree_prove(
                        session,
                        goal,
                        action_budget=128,
                        timeout_seconds=10,
                        max_depth=None,
                        excluded_premises=frozenset({"goal"}),
                    )
                self.assertNotEqual(control.status, "solved")
            with AgdaSession(timeout_seconds=20) as session:
                (goal,) = session.load_module(path)
                result = constructor_tree_prove(
                    session,
                    goal,
                    action_budget=128,
                    timeout_seconds=10,
                    max_depth=None,
                    excluded_premises=frozenset({"goal"}),
                )
                self.assertEqual(result.status, "solved", result.stats.to_dict())
                expression = result.solutions[0].proof_text
                self.assertIn("consume", expression)
                self.assertIn("convert", expression)
                self.assertGreater(result.stats.evidence_inference_queries, 0)
                self.assertEqual(result.stats.premise_refinement_queries, 0)
            checked, trust = validate_candidate(
                path, goal, expression, timeout_seconds=10
            )
            self.assertTrue(checked["checked"], checked)
            self.assertTrue(checked["fresh_process"])
            self.assertEqual(trust["admitted_axioms_and_primitives"], [])
            self.assertEqual(path.read_text(), source)

    def test_supported_prefix_uses_inference_not_a_guessed_partial_type(self):
        self.check_composition(SOURCE, "Container A (F C)")

    def test_infix_type_constructor_keeps_the_same_composition(self):
        source = SOURCE.replace("data Container", "infixr 15 _◇_\ndata _◇_")
        for tail in ("(F B)", "B", "C"):
            source = source.replace(f"Container A {tail}", f"A ◇ {tail}")
        self.check_composition(source, "A ◇ F C")

    def test_record_inputs_use_the_same_composition(self):
        source = (
            SOURCE.replace(
                "data Container (A B : Set) : Set where\n  left : A → Container A B\n  right : B → Container A B",
                "record Container (A B : Set) : Set where\n  constructor pair\n  field\n    first : A\n    second : B\nopen Container public",
            )
            .replace(
                "convert f (left a) = left a\nconvert f (right b) = right (f b)",
                "convert f (pair a b) = pair a (f b)",
            )
            .replace(
                "  consume (left a) = inject (left a)\n  consume (right b) = transform right b",
                "  consume (pair a b) = transform (pair a) b",
            )
        )
        self.check_composition(source, "Container A (F C)")

    def test_an_unrelated_module_family_is_not_supplied_by_these_maps(self):
        source = SOURCE.replace(
            "module Experiment (F : Set → Set)",
            "module Experiment (F G : Set → Set)",
        ).replace(
            "  goal : {A B C : Set} → (B → F C) → Container A B → F (Container A C)",
            "  goal : {A B C : Set} → (B → F C) → Container A B → G (Container A C)",
        )
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.dict(
                os.environ,
                {
                    "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                    "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                    "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                    "AGDAPROVER_SCOPED_DEPENDENCIES": "0",
                    "AGDAPROVER_SCOPED_QUERY_VIEWS": "0",
                    "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "0",
                },
            ),
        ):
            path = Path(directory) / "SuppliedEvidence.agda"
            path.write_text(source)
            with AgdaSession(timeout_seconds=20) as session:
                (goal,) = session.load_module(path)
                result = constructor_tree_prove(
                    session,
                    goal,
                    action_budget=128,
                    timeout_seconds=10,
                    max_depth=None,
                    excluded_premises=frozenset({"goal"}),
                )
            self.assertNotEqual(result.status, "solved")
            self.assertEqual(path.read_text(), source)
