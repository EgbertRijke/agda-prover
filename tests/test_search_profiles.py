import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from agdaprover.cli import build_parser, task_from_arguments
from agdaprover.editor_api import EDITOR_REQUEST_SCHEMA, EditorRequest, source_sha256
from agdaprover.search_profiles import search_profile


class SearchProfileTests(unittest.TestCase):
    def task(self, *options, operation="prove-prefix"):
        arguments = build_parser().parse_args([operation, "Example.agda", *options])
        return task_from_arguments(arguments, Path("Example.agda"), "symbolic", None)

    def test_deep_only_changes_default_effort_in_every_search_entry_point(self):
        for operation in ("prove", "prove-prefix", "step", "interactive"):
            with self.subTest(operation=operation):
                standard = self.task(operation=operation)
                deep = self.task("--deep", operation=operation)
                self.assertEqual(standard.max_candidates, 500)
                self.assertEqual(deep, replace(standard, max_candidates=8000))
                self.assertEqual(
                    deep, self.task("--search-profile", "deep", operation=operation)
                )
                self.assertIsNone(deep.max_depth)
                self.assertIsNone(deep.timeout_seconds)
                self.assertIsNone(deep.max_verifier_calls)

    def test_explicit_caps_are_preserved_in_both_argument_orders(self):
        for options in (
            ("--deep", "--max-candidates", "17"),
            ("--max-candidates", "17", "--deep"),
        ):
            task = self.task(
                *options,
                "--timeout",
                "2",
                "--max-verifier-calls",
                "9",
                "--max-depth",
                "3",
                "--cpu-seconds",
                "1",
            )
            self.assertEqual(task.max_candidates, 17)
            self.assertEqual(task.max_verifier_calls, 9)
            self.assertEqual(task.timeout_seconds, 2)
            self.assertEqual(task.max_depth, 3)
            self.assertEqual(task.resources.cpu_seconds, 1)

    def test_editor_resolves_same_defaults_and_preserves_explicit_allowance(self):
        with tempfile.TemporaryDirectory() as d:
            source = Path(d) / "Example.agda"
            source.write_text("module Example where\n")
            value = dict(
                schema_version=EDITOR_REQUEST_SCHEMA,
                request_id="test:1",
                operation="prove-prefix",
                source_file=str(source),
                source_sha256=source_sha256(source),
                goal_position=1,
            )
            standard = EditorRequest.from_dict(value)
            deep = EditorRequest.from_dict({**value, "search_profile": "deep"})
            self.assertEqual(standard.max_candidates, 500)
            self.assertEqual(deep.max_candidates, 8000)
            self.assertEqual(deep.to_namespace_values()["max_candidates"], 8000)
            self.assertEqual(
                EditorRequest.from_dict(
                    {**value, "search_profile": "deep", "max_candidates": 11}
                ).max_candidates,
                11,
            )
            for invalid in (None, [], True, "unknown"):
                with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                    EditorRequest.from_dict({**value, "search_profile": invalid})
            with self.assertRaisesRegex(ValueError, "search-only"):
                EditorRequest.from_dict(
                    {**value, "operation": "inspect", "search_profile": "deep"}
                )

    def test_profile_lookup_rejects_unknown_names(self):
        with self.assertRaises(ValueError):
            search_profile("unlimited")
