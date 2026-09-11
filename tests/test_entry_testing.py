"""Independent, read-only per-entry solving and streaming reports."""

import io
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from agdaprover.application.entry_testing import test_entries as run_entries
from agdaprover.application.service import default_application
from agdaprover.bridge.contracts import BridgeBudget
from agdaprover.bridge.source_entries import decode_entries, inspect_entries
from agdaprover.bridge.source_prefix import parser_executable
from agdaprover.contracts import TaskSpec
from agdaprover.presentation.entry_testing import virtual_entry
from agdaprover.project.entries import SourceEntry

SOURCE = """{-# OPTIONS --without-K #-}
module EntryExamples where

data Bit : Set where
  off on : Bit

flip : Bit → Bit
flip off = on
flip on = off

keep : {A : Set} → A → A
keep x = x

module _ {A : Set} where
  first : A → A → A
  first x y = x
"""


def observed_result(status="verified", fresh=True):
    return SimpleNamespace(
        status=status,
        validation={"fresh_process": fresh, "checked": True},
        patch={"replacement": "NEW PROOF"},
        proof_term="NEW PROOF",
        diagnostics=[],
        elapsed_ms=1,
        cost=SimpleNamespace(to_dict=lambda: {}),
    )


class EntryTestingTests(unittest.TestCase):
    def run_case(self, solve):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Input.agda"
            original = "module Input where\nf : Set\nf = Set\ng : Set\ng = Set\n"
            source.write_text(original)
            rows = tuple(
                SourceEntry(
                    name,
                    ((original.index(name + " ="), original.index(name + " =") + 7),),
                )
                for name in ("f", "g")
            )
            seen, events = [], []

            def workspace(_source, text, root, **_kwargs):
                target = root / "Input.agda"
                target.write_text(text)
                return SimpleNamespace(source_file=target, configuration=None)

            def attempt(task):
                seen.append(task.source_file.read_text())
                self.assertNotEqual(task.source_file, source)
                self.assertEqual(task.ranker, "nnue")
                self.assertEqual(task.max_candidates, 71)
                self.assertEqual(
                    seen[-1][task.goal_position - 1 : task.goal_position + 3], "{!!}"
                )
                return solve(len(seen), source)

            with (
                patch(
                    "agdaprover.application.entry_testing.inspect_entries",
                    return_value=rows,
                ),
                patch(
                    "agdaprover.application.entry_testing.prepare_project_overlay",
                    workspace,
                ),
                patch(
                    "agdaprover.application.entry_testing.inspect_prefix",
                    side_effect=lambda _path, source, *_: {
                        "status": "parsed",
                        "boundary": {"prefix_end": len(source)},
                    },
                ),
            ):
                outcome = run_entries(
                    TaskSpec(source, max_candidates=71),
                    solve=attempt,
                    publish=lambda event, data: events.append((event, data)),
                )
            return outcome, seen, events, source.read_text(), original

    def test_each_test_resets_to_the_original_and_streams_before_continuing(self):
        outcome, seen, events, after, original = self.run_case(
            lambda *_: observed_result()
        )
        self.assertEqual(outcome.payload["status"], "completed")
        self.assertEqual(outcome.payload["solved"], 2)
        self.assertIn("g = Set", seen[0])
        self.assertIn("f = Set", seen[1])
        self.assertTrue(
            all(s.count("{!!}") == 1 and "NEW PROOF" not in s for s in seen)
        )
        self.assertEqual(
            [event for event, _ in events],
            [
                "started",
                "entry-started",
                "entry-result",
                "entry-started",
                "entry-result",
            ],
        )
        self.assertEqual(after, original)

    def test_first_unsuccessful_entry_stops_the_run(self):
        for status in (
            "unsolved",
            "resource-exhausted",
            "invalid-task",
            "toolchain-error",
        ):
            with self.subTest(status=status):
                outcome, seen, events, after, original = self.run_case(
                    lambda *_, status=status: observed_result(status)
                )
                self.assertEqual(len(seen), 1)
                self.assertEqual(outcome.payload["status"], "stopped")
                self.assertEqual(events[-1][1]["status"], status)
                self.assertEqual(after, original)

    def test_cancel_and_missing_validation_do_not_report_success(self):
        def cancel(*_):
            raise KeyboardInterrupt

        for solve, status in (
            (cancel, "cancelled"),
            (lambda *_: observed_result(fresh=False), "stopped"),
        ):
            outcome, seen, _events, after, original = self.run_case(solve)
            self.assertEqual(outcome.payload["status"], status)
            self.assertEqual(outcome.payload["solved"], 0)
            self.assertEqual(len(seen), 1)
            self.assertEqual(after, original)

    def test_a_later_failure_retains_previous_successes(self):
        outcome, seen, events, after, original = self.run_case(
            lambda index, _: observed_result("verified" if index == 1 else "unsolved")
        )
        self.assertEqual(len(seen), 2)
        self.assertEqual(outcome.payload["solved"], 1)
        self.assertEqual(outcome.payload["failed_entry"]["name"], "g")
        self.assertEqual(
            [data["status"] for event, data in events if event == "entry-result"],
            ["verified", "unsolved"],
        )
        self.assertEqual(after, original)

    def test_missing_parser_has_an_actionable_error(self):
        with patch(
            "agdaprover.bridge.source_entries.parser_executable", return_value=None
        ):
            with self.assertRaisesRegex(ValueError, "build-source-parser"):
                inspect_entries(Path("unused.agda"), "", BridgeBudget())

    def test_changed_source_stops_without_publishing_stale_success(self):
        def change(_index, source):
            source.write_text(source.read_text() + "-- changed\n")
            return observed_result()

        outcome, seen, events, _after, _original = self.run_case(change)
        self.assertEqual(outcome.payload["status"], "stopped")
        self.assertIn("changed", outcome.payload["diagnostic"])
        self.assertEqual(len(seen), 1)
        self.assertFalse(any(event == "entry-result" for event, _ in events))

    def test_parser_response_is_strict_and_overlaps_are_rejected(self):
        value = {
            "schema_version": "agdaprover.source-entries.v1",
            "parser_version": "2.8.0",
            "source_characters": 5,
            "parse_warning_count": 0,
            "entries": [{"name": "x", "parts": [[0, 3]], "reason": ""}],
        }
        self.assertEqual(decode_entries(value, "abcde")[0].name, "x")
        for key, wrong in (
            ("schema_version", "unknown"),
            ("source_characters", True),
            ("parse_warning_count", 1),
            ("entries", [{"name": "x", "parts": [[-1, 3]], "reason": ""}]),
        ):
            with self.subTest(key=key), self.assertRaises(ValueError):
                decode_entries({**value, key: wrong}, "abcde")
        with self.assertRaisesRegex(ValueError, "Overlapping"):
            decode_entries({**value, "entries": value["entries"] * 2}, "abcde")


@unittest.skipUnless(
    parser_executable() and shutil.which("agda"),
    "Agda and the source parser are required",
)
class EntryTestingKernelTests(unittest.TestCase):
    def test_later_entries_use_original_definitions_not_earlier_solutions(self):
        original = """{-# OPTIONS --safe --without-K #-}
module IndependentContext where
open import Agda.Builtin.Equality
module _ {A : Set} (x y : A) where
  selected : A
  selected = y
  original-witness : selected ≡ y
  original-witness = refl
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "IndependentContext.agda"
            source.write_text(original)
            events = []
            result = default_application.test_entries(
                TaskSpec(source, ranker="symbolic", timeout_seconds=15),
                publish=lambda event, data: events.append((event, data)),
            )
            self.assertEqual(result.payload["status"], "completed", result.payload)
            self.assertEqual(source.read_text(), original)
        solutions = [data for event, data in events if event == "entry-result"]
        self.assertEqual(len(solutions), 2)
        self.assertIn(solutions[0]["solution"].strip(), {"x", "selected = x"})
        self.assertEqual(solutions[1]["solution"].strip(), "original-witness = refl")
        self.assertTrue(all(s["validation_scope"] == "entry-prefix" for s in solutions))

    def test_type_definition_can_differ_while_later_proof_sees_original_relation(self):
        original = """{-# OPTIONS --safe --without-K #-}
module IndependentType where
open import Agda.Builtin.Equality
module _ {A : Set} (x y : A) where
  relation : Set
  relation = x ≡ y
module _ {A : Set} (x : A) where
  diagonal : relation x x
  diagonal = refl
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "IndependentType.agda"
            source.write_text(original)
            events = []
            result = default_application.test_entries(
                TaskSpec(source, ranker="symbolic", timeout_seconds=15),
                publish=lambda event, data: events.append((event, data)),
            )
            self.assertEqual(result.payload["status"], "completed", result.payload)
            self.assertEqual(source.read_text(), original)
        solutions = [
            data["solution"].strip()
            for event, data in events
            if event == "entry-result"
        ]
        self.assertIn(solutions[0], {"A", "relation = A"})
        self.assertEqual(solutions[1], "diagonal = refl")

    def test_literate_prose_inside_an_entry_is_preserved(self):
        original = """# Example
```agda
module LiterateEntry where
identity : {A : Set} → A → A
identity x =
```
This explanation belongs to the document, not to the erased proof.
```agda
  x
```
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "LiterateEntry.lagda.md"
            source.write_text(original)
            rows = inspect_entries(source, original, BridgeBudget.for_run(10))
            self.assertEqual(len(rows), 1)
            candidate, _ = virtual_entry(original, rows[0], literate=True)
            self.assertIn("This explanation belongs", candidate)
            self.assertEqual(candidate.count("```"), 4)
            result = default_application.test_entries(
                TaskSpec(source, timeout_seconds=15),
                publish=lambda *_: None,
            )
            self.assertEqual(result.payload["status"], "completed", result.payload)
            self.assertEqual(source.read_text(), original)

    def test_inline_layout_is_rejected_without_erasing_neighbours(self):
        original = "module Inline where\nf : {A : Set} → A → A\nf x = x; g : {A : Set} → A → A\ng x = x\n"
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Inline.agda"
            source.write_text(original)
            rows = inspect_entries(source, original, BridgeBudget.for_run(10))
            self.assertEqual(rows[0].reason, "inline-declaration-boundary")
            with self.assertRaisesRegex(ValueError, "inline-declaration"):
                virtual_entry(original, rows[0])

    def test_whole_bodies_include_absurd_clauses_where_helpers_and_record_methods(self):
        original = """module Boundaries where
data Empty : Set where
absurd : {A : Set} → Empty → A
absurd () -- preserve this comment; and this }
identity : {A : Set} → A → A
identity {A} x = helper
  where
  helper : A
  helper = x
record Box (A : Set) : Set where
  constructor box
  field
    value : A
  retrieve : A
  retrieve = value
open Box
build : {A : Set} → A → Box A
value (build x) = x
mutual
  echo : {A : Set} → A → A
  echo x = other x
  other : {A : Set} → A → A
  other x = x {- Preserve a
    multiline trailing comment. -}
"""
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Boundaries.agda"
            source.write_text(original)
            rows = inspect_entries(source, original, BridgeBudget.for_run(10))
            self.assertEqual(
                [row.name for row in rows],
                ["absurd", "identity", "retrieve", "build", "echo", "other"],
            )
            for row in rows:
                with self.subTest(entry=row.name):
                    self.assertFalse(row.reason)
                    candidate, position = virtual_entry(original, row)
                    self.assertEqual(candidate[position - 1 : position + 3], "{!!}")
                    if row.name == "identity":
                        self.assertNotIn("helper", candidate)
                    source.write_text(candidate)
                    check = subprocess.run(
                        [
                            "agda",
                            "--no-libraries",
                            "--allow-unsolved-metas",
                            "-i",
                            directory,
                            str(source),
                        ],
                        capture_output=True,
                        text=True,
                        timeout=15,
                    )
                    self.assertEqual(check.returncode, 0, check.stdout + check.stderr)

    def test_named_where_and_unsigned_entries_are_reported_not_skipped(self):
        sources = (
            (
                "f : {A : Set} → A → A\nf {A} x = helper\n  module W where\n    helper : A\n    helper = x\n",
                "exported-where-module",
            ),
            ("f = Set\n", "missing-fixed-signature"),
        )
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Unsupported.agda"
            for body, reason in sources:
                with self.subTest(reason=reason):
                    original = "module Unsupported where\n" + body
                    source.write_text(original)
                    rows = inspect_entries(source, original, BridgeBudget.for_run(10))
                    self.assertEqual(len(rows), 1)
                    self.assertEqual(rows[0].reason, reason)
                    with patch.object(default_application.__class__, "prove") as solve:
                        result = default_application.test_entries(
                            TaskSpec(source),
                            publish=lambda *_: None,
                        )
                    solve.assert_not_called()
                    self.assertEqual(result.payload["status"], "stopped")
                    self.assertEqual(source.read_text(), original)

    def test_multiclause_and_scoped_entries_are_independent_and_freshly_verified(self):
        for literate in (False, True):
            with (
                self.subTest(literate=literate),
                tempfile.TemporaryDirectory() as directory,
            ):
                source = Path(directory) / (
                    "EntryExamples.lagda.md" if literate else "EntryExamples.agda"
                )
                text = "# Test\n\n```agda\n" + SOURCE + "```\n" if literate else SOURCE
                source.write_text(text)
                original = source.read_bytes()
                rows = inspect_entries(source, text, BridgeBudget.for_run(10))
                self.assertEqual([r.name for r in rows], ["flip", "keep", "first"])
                self.assertEqual(len(rows[0].parts), 2)
                candidate, _ = virtual_entry(text, rows[0], literate=literate)
                self.assertNotIn("flip off = on", candidate)
                self.assertNotIn("flip on = off", candidate)
                self.assertIn("keep x = x", candidate)
                events = []
                result = default_application.test_entries(
                    TaskSpec(source, timeout_seconds=15),
                    publish=lambda event, data, events=events: events.append(
                        (event, data)
                    ),
                )
                self.assertEqual(result.payload["status"], "completed", result.payload)
                self.assertEqual(result.payload["solved"], 3)
                self.assertTrue(
                    all(
                        data["validation"]["fresh_process"]
                        for event, data in events
                        if event == "entry-result"
                    )
                )
                self.assertEqual(source.read_bytes(), original)

    def test_editor_api_emits_progress_lines_and_one_terminal_response(self):
        from agdaprover.cli import main
        from agdaprover.editor_api import EDITOR_REQUEST_SCHEMA, source_sha256

        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "EntryExamples.agda"
            source.write_text(SOURCE)
            request = {
                "schema_version": EDITOR_REQUEST_SCHEMA,
                "request_id": "test:entries",
                "operation": "test-entries",
                "source_file": str(source),
                "source_sha256": source_sha256(source),
                "goal_position": 1,
                "timeout_seconds": 15,
            }
            output = io.StringIO()
            with (
                patch("sys.stdin", io.StringIO(json.dumps(request))),
                patch("sys.stdout", output),
            ):
                status = main(["editor-api"])
            self.assertEqual(status, 0, output.getvalue())
            rows = [json.loads(line) for line in output.getvalue().splitlines()]
            self.assertEqual(rows[0]["event"], "started")
            self.assertEqual(rows[-1]["result"]["status"], "completed")
            self.assertTrue(all(r["request_id"] == "test:entries" for r in rows))
            self.assertEqual(source.read_text(), SOURCE)
