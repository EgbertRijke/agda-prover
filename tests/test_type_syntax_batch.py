"""Exact, bounded lexical reuse must not change structural search inputs."""

from __future__ import annotations

import random
import unittest
from concurrent.futures import ThreadPoolExecutor
from contextvars import copy_context
from unittest.mock import patch

from agdaprover import type_syntax as syntax
from agdaprover.contracts import ContextEntry, GoalInfo
from agdaprover.premise_search import (
    ScopePremiseAction,
    premise_static_priority,
    rank_scope_premises,
)


class TypeSyntaxBatchTests(unittest.TestCase):
    def test_exact_keys_and_caller_mutation(self):
        with syntax.syntax_scan_batch() as batch:
            original = syntax._scan("(A) → B", "→")
            self.assertEqual(original, ([4], {0: 2}))
            original[0].clear()
            original[1].clear()
            self.assertEqual(syntax._scan("(A) → B", "→"), ([4], {0: 2}))
            self.assertEqual(syntax._scan("(A) → B", ":"), ([], {0: 2}))
            self.assertEqual(syntax._scan("( A ) → B", "→"), ([6], {0: 4}))
            self.assertEqual(batch.hits, 1)
            self.assertEqual(batch.misses, 3)
        self.assertFalse(batch.active)
        self.assertEqual(batch.retained_bytes, 0)
        self.assertFalse(batch.entries)

    def test_eviction_and_oversize_do_not_reject_syntax(self):
        with syntax.syntax_scan_batch(max_bytes=1400) as batch:
            for i in range(40):
                text = f"(entry{i} : A) → B"
                self.assertEqual(
                    syntax._scan(text, "→"), syntax._scan_uncached(text, "→")
                )
                self.assertLessEqual(batch.retained_bytes, 1400)
            self.assertLess(len(batch.entries), 40)
            large = "(" * 1000 + "A → B" + ")" * 1000
            self.assertEqual(syntax.strip_outer_delimiters(large), "A → B")
            self.assertNotIn((large, "\0"), batch.entries)
            self.assertLessEqual(batch.retained_bytes, 1400)
        with syntax.syntax_scan_batch(max_bytes=0) as disabled:
            self.assertEqual(syntax.split_top_level_arrows("A → B"), ("A", "B"))
            self.assertFalse(disabled.entries)

    def test_failures_cleanup_and_nested_context(self):
        class Cancelled(BaseException):
            pass

        with syntax.syntax_scan_batch() as outer:
            syntax._scan("A", "→")
            with self.assertRaises(Cancelled):
                with syntax.syntax_scan_batch() as inner:
                    syntax._scan("A", "→")
                    raise Cancelled()
            self.assertFalse(inner.active)
            self.assertFalse(inner.entries)
            syntax._scan("A", "→")
            self.assertEqual(outer.hits, 1)
            for _ in range(2):
                with self.assertRaisesRegex(ValueError, "unbalanced type delimiters"):
                    syntax._scan("(broken", "→")
            self.assertNotIn(("(broken", "→"), outer.entries)
        self.assertIsNone(syntax._scan_batch.get())
        for invalid in (True, -1, 1.5, "1"):
            with (
                self.assertRaises(ValueError),
                syntax.syntax_scan_batch(max_bytes=invalid),
            ):
                self.fail("invalid reservation accepted")

    def test_copied_context_cannot_share_mutable_cache_across_threads(self):
        with syntax.syntax_scan_batch() as batch:
            syntax._scan("A → B", "→")
            context = copy_context()
            with ThreadPoolExecutor(max_workers=1) as executor:
                self.assertEqual(
                    executor.submit(context.run, syntax._scan, "A → B", "→").result(),
                    ([2], {}),
                )
            self.assertEqual(batch.hits, 0)
            self.assertEqual(batch.misses, 1)
        # A copied context retained after exit must not retain or refill data.
        self.assertEqual(context.run(syntax._scan, "A → B", "→"), ([2], {}))
        self.assertFalse(batch.entries)

    def test_seeded_scans_and_public_parsers_equal_uncached_behavior(self):
        rng = random.Random(871)
        samples = ["", "(A", "[x)", "{{i : A}}", "⦃i : F x⦄", "(x : A) (y : B x)"]
        for _ in range(250):
            value = rng.choice(("A", "λ x → B x", "x ＝ y", "f {x} y", "(x y : A)"))
            for _ in range(rng.randrange(1, 9)):
                opening, closing = rng.choice(
                    (("(", ")"), ("{", "}"), ("[", "]"), ("⦃", "⦄"))
                )
                value = opening + value + closing
                if rng.choice((False, True)):
                    value += " → F a"
            samples.append(value)
        operations = (
            syntax.strip_outer_delimiters,
            syntax.split_top_level_arrows,
            syntax.parse_named_binder,
            syntax.binder_domains,
            syntax.split_adjacent_binders,
            syntax.split_top_level_application,
            syntax.top_level_arrow_count,
            syntax.result_head,
        )

        def observed(operation, text):
            try:
                return ("value", operation(text))
            except ValueError as error:
                return ("error", str(error))

        with patch.object(syntax, "_scan", syntax._scan_uncached):
            expected = [observed(op, text) for text in samples for op in operations]
        for capacity in (0, 1400, 2 * 1024**2):
            with syntax.syntax_scan_batch(max_bytes=capacity):
                self.assertEqual(
                    [observed(op, text) for text in samples for op in operations],
                    expected,
                )

    def test_generic_priority_and_legacy_ranking_are_unchanged(self):
        declarations = (
            ("transport", "(B : A → Set) {x y : A} → x ＝ y → B x → B y"),
            ("first", "{A : Set} {B : A → Set} → Σ A B → A"),
            ("next", "U → U"),
            ("combine", "{x y z : A} → x ＝ y → y ＝ z → x ＝ z"),
            ("opaque", "(unbalanced"),
            ("duplicate", "{{i : A}} → {x : A} → R i x"),
        )
        actions = [ScopePremiseAction(name, ty, name) for name, ty in declarations[:-2]]
        goals = [
            GoalInfo(0, ty, (ContextEntry("p", "x ＝ y", True),), (0, 1))
            for ty in ("x ＝ z", "Σ A B", "U", "(A → B) → A → B")
        ]
        for goal in goals:
            with patch.object(syntax, "_scan", syntax._scan_uncached):
                priorities = [
                    premise_static_priority(goal, action) for action in actions
                ]
                ranked = rank_scope_premises(goal, declarations)
            with syntax.syntax_scan_batch() as batch:
                self.assertEqual(
                    [premise_static_priority(goal, action) for action in actions],
                    priorities,
                )
                self.assertGreater(batch.hits, 0)
            self.assertEqual(rank_scope_premises(goal, declarations), ranked)
