import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from agdaprover.editor_api import (
    EDITOR_REQUEST_SCHEMA,
    EDITOR_RESPONSE_SCHEMA,
    EditorRequest,
    response_envelope,
)


class EditorAPIContractTests(unittest.TestCase):
    def _request(self, source: Path) -> dict[str, object]:
        return {
            "schema_version": EDITOR_REQUEST_SCHEMA,
            "request_id": "vscode:17",
            "operation": "prove-prefix",
            "source_file": str(source),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "goal_position": 11,
            "ranker": "symbolic",
            "model": None,
            "action_model": None,
            "max_candidates": 50,
            "max_term_size": 8,
            "max_depth": None,
            "timeout_seconds": 20,
        }

    def test_request_round_trip_is_editor_neutral(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.agda"
            source.write_text("module Tiny where\n\nid : Set\nid = {!!}\n")
            request = EditorRequest.from_dict(self._request(source))
            response = response_envelope(
                request,
                exit_code=2,
                result={"schema_version": "agdaprover.p0.v1", "status": "unsolved"},
            )
        self.assertEqual(response["schema_version"], EDITOR_RESPONSE_SCHEMA)
        self.assertEqual(response["request_id"], "vscode:17")
        self.assertEqual(response["operation"], "prove-prefix")
        self.assertEqual(response["result"]["status"], "unsolved")

    def test_request_rejects_stale_source_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.agda"
            source.write_text("module Tiny where\n")
            value = self._request(source)
            source.write_text("module Changed where\n")
            with self.assertRaisesRegex(ValueError, "changed before"):
                EditorRequest.from_dict(value)

    def test_request_rejects_unknown_fields(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.agda"
            source.write_text("module Tiny where\n")
            value = self._request(source)
            value["editor_specific_escape_hatch"] = True
            with self.assertRaisesRegex(ValueError, "unknown editor request fields"):
                EditorRequest.from_dict(value)

    def test_contract_is_json_serializable(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.lagda.md"
            source.write_text("```agda\nmodule Tiny where\n```\n")
            request = EditorRequest.from_dict(self._request(source))
            encoded = json.dumps(
                response_envelope(request, exit_code=0, result={"goals": []})
            )
        self.assertIn(EDITOR_RESPONSE_SCHEMA, encoded)

    def test_timeout_may_be_omitted_for_an_unbounded_interactive_run(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.agda"
            source.write_text("module Tiny where\n")
            value = self._request(source)
            value.pop("timeout_seconds")
            request = EditorRequest.from_dict(value)
        self.assertIsNone(request.timeout_seconds)
        self.assertIsNone(request.max_verifier_calls)

    def test_optional_verifier_budget_is_validated_and_forwarded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Tiny.agda"
            source.write_text("module Tiny where\n")
            value = self._request(source)
            value["max_verifier_calls"] = 17
            request = EditorRequest.from_dict(value)
            self.assertEqual(request.to_namespace_values()["max_verifier_calls"], 17)
            for invalid in (0, -1, True, 1.5, "17"):
                with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                    EditorRequest.from_dict({**value, "max_verifier_calls": invalid})
            with self.assertRaisesRegex(ValueError, "search-only"):
                EditorRequest.from_dict({**value, "operation": "inspect"})


if __name__ == "__main__":
    unittest.main()
