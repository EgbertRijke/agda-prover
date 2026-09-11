"""New observations remain usable across optimizations and proof stages."""

import itertools
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import Mock

from agdaprover.contracts import ContextEntry, GoalInfo, TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.reasoning.agenda import EvidenceAgenda
from agdaprover.relation_path import RelationHead, solve_relation_path


class EvidenceAgendaTests(unittest.TestCase):
    def test_relation_parser_is_independently_importable(self):
        for module in ("agdaprover.relation_path", "agdaprover.premise_search"):
            with self.subTest(module=module):
                result = subprocess.run(
                    [sys.executable, "-c", f"import {module}"],
                    capture_output=True,
                    text=True,
                    timeout=10,
                )
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_lazy_fair_expansion_and_late_admission(self):
        agenda = EvidenceAgenda()
        agenda.add("first", iter(range(10)))
        agenda.add("second", iter(("a", "b")))
        self.assertEqual(agenda.pop(), 0)
        agenda.add("late", iter(("new",)))
        self.assertEqual([agenda.pop() for _ in range(5)], ["a", 1, "new", "b", 2])
        self.assertEqual(agenda.peak_pending, 3)
        self.assertFalse(agenda.add("late", iter(("duplicate",))))
        self.assertEqual([agenda.pop() for _ in range(7)], list(range(3, 10)))
        self.assertIsNone(agenda.pop())
        self.assertEqual(agenda.pending, 0)

    def test_infinite_expansion_does_not_starve_another_witness(self):
        agenda = EvidenceAgenda()
        agenda.add("one witness", itertools.count())
        agenda.add("another witness of the same type", iter(("useful",)))
        self.assertEqual(agenda.pop(), 0)
        self.assertEqual(agenda.pop(), "useful")
        self.assertEqual(agenda.pop(), 1)

    def test_new_branch_does_not_inherit_seen_keys(self):
        first, second = EvidenceAgenda(), EvidenceAgenda()
        first.add("same expression", iter((1,)))
        self.assertTrue(second.add("same expression", iter((2,))))
        self.assertEqual(first.pop(), 1)
        self.assertEqual(second.pop(), 2)


class IncrementalRelationEvidenceTests(unittest.TestCase):
    def search(self, target, locals_, heads, inferred, **options):
        calls = []
        session = Mock()

        def infer(_state, *, goal_id, expression):
            calls.append(expression)
            return inferred.get(expression)

        session.infer_type.side_effect = infer
        result = solve_relation_path(
            session,
            Mock(),
            GoalInfo(
                0, target, tuple(ContextEntry(n, ty, True) for n, ty in locals_), (0, 4)
            ),
            tuple(RelationHead(n, ty, i) for i, (n, ty) in enumerate(heads)),
            query_budget=options.pop("query_budget", 128),
            deadline=options.pop("deadline", time.monotonic() + 10),
            prefix_heads=options.pop("prefix_heads", {"R": 2}),
            **options,
        )
        self.assertEqual(len(calls), len(set(calls)))
        self.assertEqual(result.stats.inference_queries, len(calls))
        return result, calls

    def test_early_unary_observations_feed_further_applications(self):
        for incremental in (False, True):
            with self.subTest(incremental=incremental):
                result, calls = self.search(
                    "R (F (F a)) (F (F b))",
                    (("p", "R a b"),),
                    (("lift", "{x y : A} → R x y → R (F x) (F y)"),),
                    {
                        "lift p": "R (F a) (F b)",
                        "lift (lift p)": "R (F (F a)) (F (F b))",
                    },
                    incremental=incremental,
                )
                self.assertEqual(
                    result.expression, "lift (lift p)" if incremental else None
                )
                if incremental:
                    self.assertEqual(calls, ["lift p", "lift (lift p)"])
                    self.assertGreater(result.stats.worklist_expansions, 0)

    def test_binary_observation_can_be_reversed_then_composed(self):
        result, calls = self.search(
            "R (combine b c) d",
            (("p", "R a b"), ("q", "R (combine a c) d"), ("r", "R u c")),
            (
                ("turn", "{x y : A} → R x y → R y x"),
                ("follow", "{x y z : A} → R x y → R y z → R x z"),
                (
                    "carry",
                    "{x y u v : A} → R x y → R u v → R (combine x v) (combine y v)",
                ),
            ),
            {
                "carry p r": "R (combine a c) (combine b c)",
                "turn (carry p r)": "R (combine b c) (combine a c)",
                "follow (turn (carry p r)) q": "R (combine b c) d",
            },
        )
        self.assertEqual(result.expression, "follow (turn (carry p r)) q")
        self.assertEqual(
            result.inputs, frozenset({"carry", "turn", "follow", "p", "r", "q"})
        )
        self.assertIn("turn (carry p r)", calls)

    def test_composition_can_feed_a_later_unary_transformation(self):
        for incremental in (False, True):
            with self.subTest(incremental=incremental):
                result, _ = self.search(
                    "R (F a) (F c)",
                    (("p", "R a b"), ("q", "R b c")),
                    (
                        ("follow", "{x y z : A} → R x y → R y z → R x z"),
                        ("carry", "{x y : A} → R x y → R (F x) (F y)"),
                    ),
                    {
                        "follow p q": "R a c",
                        "carry (follow p q)": "R (F a) (F c)",
                    },
                    incremental=incremental,
                )
                self.assertEqual(
                    result.expression, "carry (follow p q)" if incremental else None
                )

    def test_distinct_witnesses_of_one_type_are_not_merged(self):
        result, calls = self.search(
            "R final done",
            (("p", "R a b"),),
            (
                ("first", "R a b → R u v"),
                ("second", "R a b → R u v"),
                ("third", "R a b → R u v"),
                ("use", "R u v → R final done"),
            ),
            {
                "first p": "R u v",
                "second p": "R u v",
                "third p": "R u v",
                "use (third p)": "R final done",
            },
        )
        self.assertEqual(result.expression, "use (third p)")
        self.assertIn("use (first p)", calls)
        self.assertIn("use (second p)", calls)

    def test_new_values_can_fill_both_binary_argument_positions(self):
        result, _ = self.search(
            "R result result'",
            (("p", "R a b"),),
            (
                ("f", "R a b → R c d"),
                ("g", "R a b → R e f"),
                ("join", "R c d → R e f → R result result'"),
            ),
            {"f p": "R c d", "g p": "R e f", "join (f p) (g p)": "R result result'"},
        )
        self.assertEqual(result.expression, "join (f p) (g p)")

    def test_infix_relations_have_the_same_incremental_path(self):
        result, _ = self.search(
            "F (F a) ≈ F (F b)",
            (("p", "a ≈ b"),),
            (("lift", "{x y : A} → x ≈ y → F x ≈ F y"),),
            {"lift p": "F a ≈ F b", "lift (lift p)": "F (F a) ≈ F (F b)"},
            prefix_heads=None,
        )
        self.assertEqual(result.expression, "lift (lift p)")

    def test_unavailable_or_rejected_reversal_is_not_assumed(self):
        for heads in ((), (("turn", "{x y : A} → R x y → R y x"),)):
            result, _ = self.search("R b a", (("p", "R a b"),), heads, {})
            self.assertIsNone(result.expression)

    def test_cycles_stop_at_the_shared_term_allowance(self):
        result, calls = self.search(
            "R c d",
            (("p", "R a b"),),
            (("turn", "{x y : A} → R x y → R y x"),),
            {
                "turn p": "R b a",
                "turn (turn p)": "R a b",
                "turn (turn (turn p))": "R b a",
            },
            max_terms=3,
        )
        self.assertIsNone(result.expression)
        self.assertEqual(calls, ["turn p", "turn (turn p)"])
        self.assertEqual(result.stats.edges_retained, 3)
        self.assertLessEqual(result.stats.worklist_peak, 3)

    def test_budget_deadline_and_excluded_completions_remain_authoritative(self):
        kwargs = dict(
            target="R b a",
            locals_=(("p", "R a b"),),
            heads=(("turn", "{x y : A} → R x y → R y x"),),
            inferred={"turn p": "R b a", "turn (turn p)": "R a b"},
        )
        for options in ({"query_budget": 0}, {"deadline": time.monotonic() - 1}):
            result, calls = self.search(**kwargs, **options)
            self.assertIsNone(result.expression)
            self.assertEqual(calls, [])
        result, calls = self.search(
            **kwargs, excluded_expressions=frozenset({"turn p"})
        )
        self.assertIsNone(result.expression)
        self.assertEqual(calls, ["turn p"])
        result, calls = self.search(**{**kwargs, "target": "R c d"}, query_budget=1)
        self.assertIsNone(result.expression)
        self.assertEqual(len(calls), 1)

    def test_kernel_interruption_propagates(self):
        session = Mock()
        session.infer_type.side_effect = TimeoutError("cancelled")
        with self.assertRaisesRegex(TimeoutError, "cancelled"):
            solve_relation_path(
                session,
                Mock(),
                GoalInfo(0, "R b a", (ContextEntry("p", "R a b", True),), (0, 4)),
                (RelationHead("turn", "{x y : A} → R x y → R y x", 0),),
                query_budget=10,
                deadline=time.monotonic() + 10,
                prefix_heads={"R": 2},
            )


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class EvidenceAgendaKernelTests(unittest.TestCase):
    def test_record_evidence_composes_through_an_abstract_relation(self):
        source = """{-# OPTIONS --without-K #-}
module EvidenceClosure where

module _
  {A : Set} (R : A → A → Set) (F : A → A)
  (turn : {x y : A} → R x y → R y x)
  (follow : {x y z : A} → R x y → R y z → R x z)
  (carry : {x y : A} → R x y → R (F x) (F y))
  where

  record Witness (a b : A) : Set where
    constructor pack
    field
      edge : R a b
  open Witness

  finish : {a b c : A} → Witness a b → R (F a) c → R (F b) c
  finish w q = {!!}
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "EvidenceClosure.agda"
            path.write_text(source)
            result = prove_joint_prefix(TaskSpec(path, timeout_seconds=20))
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertTrue(result.validation["checked"])
            self.assertTrue(result.validation["fresh_process"])
            for name in ("turn", "follow", "carry", "edge"):
                self.assertIn(name, result.patch["replacement"])
            self.assertEqual(path.read_text(), source)
