"""The user-facing example remains open and loads without external libraries."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path

from agdaprover.application import inspect_source

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/EckmannHilton.agda"


class ExampleTests(unittest.TestCase):
    def test_open_example_is_packaged(self) -> None:
        source = EXAMPLE.read_text(encoding="utf-8")
        self.assertEqual(source.count("{!!}"), 12)
        self.assertIn("--without-K --exact-split", source)
        self.assertNotIn("postulate", source)
        self.assertNotIn("import", source)
        config = tomllib.loads((ROOT / "pyproject.toml").read_text())
        self.assertIn(
            "examples/EckmannHilton.agda",
            config["tool"]["setuptools"]["data-files"]["share/agda-prover/examples"],
        )

    @unittest.skipUnless(shutil.which("agda"), "Agda is required")
    def test_example_loads_with_all_twelve_goals_outside_checkout(self) -> None:
        if (
            subprocess.check_output(["agda", "--numeric-version"], text=True).strip()
            != "2.8.0"
        ):
            self.skipTest("Agda 2.8.0 is required")
        with tempfile.TemporaryDirectory(prefix="agda-prover-example-") as directory:
            source = Path(directory) / EXAMPLE.name
            shutil.copyfile(EXAMPLE, source)
            result = inspect_source(source, timeout_seconds=30)
            self.assertEqual(result.exit_code, 0, result.payload)
            self.assertEqual(len(result.payload["goals"]), 12)
            self.assertEqual(source.read_bytes(), EXAMPLE.read_bytes())


if __name__ == "__main__":
    unittest.main()
