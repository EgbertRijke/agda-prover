"""Small product contracts; no dependency on the development repository."""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from agdaprover.application import default_application
from agdaprover.bridge.version_matrix import load_version_matrix
from agdaprover.cli import build_parser
from agdaprover.contracts import TaskSpec
from agdaprover.native import NativeBackend, default_native_library
from agdaprover.nnue import NNUEModel
from agdaprover.offline import offline_audit


class RuntimeContracts(unittest.TestCase):
    def test_cli_has_no_training_or_evaluation_commands(self) -> None:
        parser = build_parser()
        help_text = parser.format_help()
        for command in (
            "inspect",
            "prove",
            "prove-prefix",
            "interactive",
            "step",
            "editor-api",
            "doctor",
        ):
            self.assertIn(command, help_text)
        for command in ("train-nnue", "collect", "benchmark"):
            self.assertNotIn(command, help_text)

    def test_model_is_inference_only(self) -> None:
        self.assertFalse(hasattr(NNUEModel, "train_pair"))
        self.assertFalse(hasattr(NNUEModel, "save"))
        self.assertFalse(hasattr(NNUEModel, "initialize"))
        model = NNUEModel(
            "proof-term-ranking", 2, 1, [0.25], [0.1, -0.1], [0.5], 0.0, 1
        )
        self.assertAlmostEqual(
            model.score_accumulator(model.accumulator({0: 1.0})), 0.175
        )

    def test_optional_native_inference_matches_python(self) -> None:
        library = Path(
            os.environ.get("AGDAPROVER_NATIVE_LIBRARY", default_native_library())
        )
        if not library.is_file():
            self.skipTest("optional native inference library is not built")
        backend = NativeBackend(library)
        model = NNUEModel(
            "proof-term-ranking", 2, 1, [0.25], [0.1, -0.1], [0.5], 0.0, 1
        )
        base = model.accumulator({0: 1.0})
        batches = ({1: 2.0}, {}, {0: -1.0, 1: 1.0})
        expected = [
            model.score_accumulator(model.update_accumulator(base, add=batch))
            for batch in batches
        ]
        observed = backend.nnue_score_batch(
            base,
            model.embeddings,
            model.input_size,
            model.hidden_size,
            model.output_weights,
            model.output_bias,
            batches,
        )
        for left, right in zip(expected, observed, strict=True):
            self.assertAlmostEqual(left, right, places=6)
        self.assertFalse(hasattr(backend, "nnue_train_pair"))

    def test_development_modules_are_not_in_the_runtime_package(self) -> None:
        for name in (
            "training",
            "stage0",
            "stage1",
            "stage2",
            "fixture_gate",
            "application.training",
            "application.benchmarking",
        ):
            self.assertIsNone(importlib.util.find_spec("agdaprover." + name))

    def test_packaged_toolchain_matrix(self) -> None:
        self.assertIn("2.8.0", load_version_matrix())

    def test_offline_audit(self) -> None:
        self.assertTrue(offline_audit()["offline_capable"])
        self.assertEqual(offline_audit()["network_imports"], [])

    @unittest.skipUnless(shutil.which("agda"), "Agda is required")
    def test_fresh_proof_in_unrelated_temporary_directory(self) -> None:
        if (
            subprocess.check_output(["agda", "--numeric-version"], text=True).strip()
            != "2.8.0"
        ):
            self.skipTest("Agda 2.8.0 is required")
        with tempfile.TemporaryDirectory(prefix="agda-prover-smoke-") as directory:
            source = Path(directory) / "Identity.agda"
            body = "{-# OPTIONS --without-K --exact-split #-}\nmodule Identity where\nidentity : {A : Set} → A → A\nidentity = {!!}\n"
            source.write_text(body)
            result = default_application.prove(TaskSpec(source))
            self.assertEqual(result.status, "verified", json.dumps(result.to_dict()))
            self.assertIsNotNone(result.validation)
            self.assertEqual(source.read_text(), body)


if __name__ == "__main__":
    unittest.main()
