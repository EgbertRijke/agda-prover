"""Keep product licenses and independently packaged editor notices intact."""

from __future__ import annotations

import hashlib
import json
import tomllib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LICENSE = "GPL-3.0-or-later"
# Unmodified texts retrieved from GNU and Agda's pinned v2.8.0 release.
GPL_SHA256 = "3972dc9744f6499f0f9b2dbf76696f2ae7ad8af9b23dde66d6af86c9dfb36986"
AGDA_SHA256 = "a07da943d7a2a735b2c9ad6cd3a7bdb8d4908e4160d43787c7365f871e30b7d9"


class LicensingTests(unittest.TestCase):
    def test_package_license_expressions_agree(self) -> None:
        python = tomllib.loads((ROOT / "pyproject.toml").read_text())
        native = tomllib.loads((ROOT / "native/Cargo.toml").read_text())
        editor = json.loads((ROOT / "editor/vscode/package.json").read_text())
        self.assertEqual(python["project"]["license"], LICENSE)
        self.assertEqual(native["package"]["license"], LICENSE)
        self.assertEqual(editor["license"], LICENSE)

    def test_complete_gpl_is_preserved_in_both_distribution_roots(self) -> None:
        for relative in ("LICENSE", "editor/vscode/LICENSE"):
            with self.subTest(file=relative):
                content = (ROOT / relative).read_bytes().replace(b"\r\n", b"\n")
                self.assertEqual(hashlib.sha256(content).hexdigest(), GPL_SHA256)

    def test_upstream_agda_notice_is_not_replaced_by_our_license(self) -> None:
        content = (ROOT / "licenses/Agda-MIT.txt").read_bytes()
        self.assertEqual(
            hashlib.sha256(content.replace(b"\r\n", b"\n")).hexdigest(), AGDA_SHA256
        )
        notice = (ROOT / "THIRD_PARTY_NOTICES.md").read_text()
        self.assertIn("Agda-MIT.txt", notice)
        self.assertIn("v2.8.0", notice)
        bridge = (ROOT / "native/agda-bridge/Main.hs").read_text()
        self.assertIn("SPDX-License-Identifier: GPL-3.0-or-later AND MIT", bridge)

    def test_wheel_declares_all_notice_files(self) -> None:
        config = tomllib.loads((ROOT / "pyproject.toml").read_text())
        declared = {
            entry.relative_to(ROOT).as_posix()
            for pattern in config["project"]["license-files"]
            for entry in ROOT.glob(pattern)
        }
        self.assertEqual(
            declared,
            {
                "LICENSE",
                "AUTHORS.md",
                "THIRD_PARTY_NOTICES.md",
                "licenses/Agda-MIT.txt",
                "licenses/agda-stdlib-MIT.txt",
                "licenses/agda-unimath-MIT.txt",
            },
        )
        editor_files = config["tool"]["setuptools"]["data-files"][
            "share/agda-prover/editor/vscode"
        ]
        self.assertIn("editor/vscode/LICENSE", editor_files)


if __name__ == "__main__":
    unittest.main()
