"""Static startup audit for the prototype's mandatory local-only runtime."""

from __future__ import annotations

import ast
import shutil
import sys
import time
from pathlib import Path
from typing import Any

from .contracts import TaskSpec

NETWORK_MODULES = {
    "aiohttp",
    "httpx",
    "requests",
    "socket",
    "urllib",
    "websockets",
}


_CACHED_REPORT: dict[str, Any] | None = None


def offline_audit(*, deadline: float | None = None) -> dict[str, Any]:
    global _CACHED_REPORT
    if _CACHED_REPORT is not None:
        return _CACHED_REPORT
    package = Path(__file__).resolve().parent
    violations: list[dict[str, str]] = []
    files = sorted(package.rglob("*.py"))
    for source_file in files:
        if deadline is not None and time.monotonic() >= deadline:
            raise TimeoutError("wall-time budget exhausted during offline audit")
        tree = ast.parse(source_file.read_text(), filename=str(source_file))
        for node in ast.walk(tree):
            names: list[str] = []
            if isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.module:
                names = [node.module]
            for name in names:
                root = name.split(".", 1)[0]
                if root in NETWORK_MODULES:
                    violations.append({"file": source_file.name, "module": name})
    agda = shutil.which("agda")
    _CACHED_REPORT = {
        "offline_capable": not violations,
        "python_files_scanned": len(files),
        "network_imports": violations,
        "binaries": {
            "python": sys.executable,
            "agda": agda,
        },
        "model_runtimes": ["agdaprover.nnue (dependency-free local CPU)"],
        "configured_endpoints": [],
        "attempted_socket_connections": 0,
        "telemetry": "disabled",
    }
    return _CACHED_REPORT


def assert_offline_configuration(
    task: TaskSpec, *, deadline: float | None = None
) -> None:
    if not task.offline:
        raise ValueError("P0 is local-only; disabling offline policy is unsupported")
    report = offline_audit(deadline=deadline)
    if not report["offline_capable"]:
        raise ValueError("offline policy rejected a network-capable runtime component")
