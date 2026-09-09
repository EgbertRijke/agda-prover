"""Strict loader for the machine-readable Agda compatibility matrix."""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .contracts import (
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    DiagnosticPhase,
)


@dataclass(frozen=True)
class VersionRow:
    version: str
    adapter: str
    operations: tuple[str, ...]
    limitations: tuple[str, ...]
    manifest: Path


def _matrix_directory() -> Path:
    configured = os.environ.get("AGDAPROVER_TOOLCHAIN_MATRIX")
    if configured:
        return Path(configured).resolve()
    return Path(__file__).resolve().parents[1] / "data/toolchains"


def _error(code: str, message: str) -> BridgeError:
    return BridgeError(
        BridgeFailure.TOOLCHAIN_ERROR,
        BridgeDiagnostic(
            code=code,
            phase=DiagnosticPhase.TOOLCHAIN,
            severity="error",
            message=message,
        ),
    )


def load_version_matrix() -> dict[str, VersionRow]:
    directory = _matrix_directory()
    if not directory.is_dir():
        raise _error(
            "toolchain-matrix-missing",
            f"toolchain matrix directory does not exist: {directory}",
        )
    result: dict[str, VersionRow] = {}
    expected = {
        "schema_version",
        "supported",
        "agda_version",
        "adapter",
        "release",
        "license",
        "assets",
        "operations",
        "limitations",
        "ci_installer",
        "local_qualification",
    }
    for path in sorted(directory.glob("agda-*.json")):
        try:
            value: Any = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise _error(
                "toolchain-matrix-invalid", f"cannot read {path.name}: {error}"
            ) from error
        if not isinstance(value, dict) or set(value) != expected:
            raise _error(
                "toolchain-matrix-invalid",
                f"{path.name} does not have the exact version-1 matrix fields",
            )
        if value.get("schema_version") != "agdaprover.toolchain-matrix.v1":
            raise _error(
                "toolchain-matrix-version-unsupported",
                f"unsupported toolchain matrix schema in {path.name}",
            )
        if value.get("supported") is not True:
            continue
        version = value.get("agda_version")
        adapter = value.get("adapter")
        operations = value.get("operations")
        limitations = value.get("limitations")
        if (
            not isinstance(version, str)
            or not isinstance(adapter, str)
            or not isinstance(operations, list)
            or not all(isinstance(item, str) for item in operations)
            or not isinstance(limitations, list)
            or not all(isinstance(item, str) for item in limitations)
        ):
            raise _error(
                "toolchain-matrix-invalid",
                f"{path.name} contains invalid capability fields",
            )
        if version in result:
            raise _error(
                "toolchain-matrix-duplicate-version",
                f"multiple supported rows declare Agda {version}",
            )
        result[version] = VersionRow(
            version,
            adapter,
            tuple(sorted(set(operations))),
            tuple(limitations),
            path,
        )
    return result
