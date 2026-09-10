"""Defaults, role isolation and opt-out without development artifacts."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import PropertyMock, patch

from agdaprover.cli import build_parser
from agdaprover.contracts import TaskSpec
from agdaprover.editor_api import EDITOR_REQUEST_SCHEMA, EditorRequest
from agdaprover.ranking.bundled import (
    FOCUSED_MODEL,
    OR_MODEL,
    STEP_MODEL,
    BundledModel,
)
from agdaprover.ranking.runtime import (
    configured_model_ids,
    load_proof_models,
    load_step_model,
)


class BundledModelTests(unittest.TestCase):
    def setUp(self) -> None:
        self.task = TaskSpec(Path("Example.agda"))

    def test_all_search_entry_points_default_to_nnue(self) -> None:
        self.assertEqual(self.task.ranker, "nnue")
        for command in ("prove", "prove-prefix", "step", "interactive"):
            with self.subTest(command=command):
                args = build_parser().parse_args([command, "Example.agda"])
                self.assertEqual(args.ranker, "nnue")
                self.assertIsNone(args.model)
                self.assertIsNone(args.action_model)
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.agda"
            source.write_text("module Example where\n")
            request = EditorRequest.from_dict(
                {
                    "schema_version": EDITOR_REQUEST_SCHEMA,
                    "request_id": "default",
                    "operation": "prove-prefix",
                    "goal_position": 1,
                    "source_file": str(source),
                    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                }
            )
            self.assertEqual(request.ranker, "nnue")
            self.assertEqual(request.to_namespace_values()["ranker"], "nnue")

    def test_defaults_load_exact_role_compatible_artifacts(self) -> None:
        for command in ("prove", "prove-prefix"):
            models = load_proof_models(self.task, command=command, deadline=None)
            self.assertIsNone(models.term)
            self.assertIsNotNone(models.focused)
            self.assertIsNotNone(models.refinement)
            self.assertEqual(models.primary_id, FOCUSED_MODEL.sha256)
            self.assertEqual(models.refinement_id, OR_MODEL.sha256)
            self.assertEqual(
                configured_model_ids(self.task, deadline=None),
                {
                    "primary": models.primary_id,
                    "refinement": models.refinement_id,
                },
            )
        step = load_step_model(self.task, deadline=None)
        self.assertIsNotNone(step)
        self.assertEqual(step.model_id, STEP_MODEL.sha256)
        self.assertEqual(
            configured_model_ids(self.task, deadline=None, command="step"),
            {"step": step.model_id},
        )

    def test_symbolic_opt_out_never_accesses_bundled_artifacts(self) -> None:
        task = replace(self.task, ranker="symbolic", model_path=Path("missing"))
        with patch.object(
            BundledModel,
            "path",
            new_callable=PropertyMock,
            side_effect=AssertionError("unexpected model access"),
        ):
            models = load_proof_models(task, command="prove", deadline=None)
            self.assertIsNone(models.primary_id)
            self.assertIsNone(models.refinement_id)
            self.assertIsNone(load_step_model(task, deadline=None))
            self.assertEqual(
                configured_model_ids(task, deadline=None),
                {"primary": None, "refinement": None},
            )

    def test_explicit_model_override_does_not_load_its_default(self) -> None:
        task = replace(
            self.task, model_path=FOCUSED_MODEL.path, action_model_path=OR_MODEL.path
        )
        step_task = replace(task, model_path=STEP_MODEL.path)
        with patch.object(BundledModel, "load", side_effect=AssertionError("default")):
            self.assertEqual(
                load_proof_models(task, command="prove", deadline=None).primary_id,
                FOCUSED_MODEL.sha256,
            )
            self.assertEqual(
                load_step_model(step_task, deadline=None).model_id, STEP_MODEL.sha256
            )

    def test_custom_roles_are_never_reinterpreted(self) -> None:
        with self.assertRaisesRegex(ValueError, "proof terms or focused branches"):
            load_proof_models(
                replace(self.task, model_path=STEP_MODEL.path),
                command="prove",
                deadline=None,
            )
        with self.assertRaisesRegex(ValueError, "role mismatch"):
            load_proof_models(
                replace(self.task, action_model_path=STEP_MODEL.path),
                command="prove-prefix",
                deadline=None,
            )
        with self.assertRaisesRegex(ValueError, "role mismatch"):
            load_step_model(
                replace(self.task, model_path=FOCUSED_MODEL.path), deadline=None
            )

    def test_custom_missing_artifact_is_not_silently_replaced(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            task = replace(self.task, model_path=Path(directory) / "missing.apnnue")
            with self.assertRaises(FileNotFoundError):
                load_proof_models(task, command="prove", deadline=None)
            with self.assertRaises(FileNotFoundError):
                load_step_model(task, deadline=None)

    def test_checksum_and_deadline_are_enforced(self) -> None:
        with self.assertRaisesRegex(ValueError, "checksum mismatch"):
            replace(FOCUSED_MODEL, sha256="0" * 64).load(deadline=None)
        with self.assertRaises(TimeoutError):
            STEP_MODEL.load(deadline=0.0)

    def test_explicit_hybrid_policy_remains_supported(self) -> None:
        task = replace(self.task, ranker="symbolic", action_model_path=OR_MODEL.path)
        models = load_proof_models(task, command="prove", deadline=None)
        self.assertIsNone(models.primary_id)
        self.assertEqual(models.refinement_id, OR_MODEL.sha256)

    def test_library_policy_does_not_claim_untrained_families(self) -> None:
        model = OR_MODEL.load(deadline=None)
        self.assertEqual(
            model.policy_families, ("constructor-choice", "visible-premise")
        )
        self.assertFalse(model.supports_policy_family("evidence-application-v1"))
        self.assertFalse(model.supports_policy_family("recursive-call"))


if __name__ == "__main__":
    unittest.main()
