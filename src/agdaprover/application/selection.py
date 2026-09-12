"""Pre-search engine selection, separate from mathematical tasks and search.

Automatic native promotion is deliberately disabled until migration
qualification succeeds. An explicit native request never retries in Python.
No compiler, package manager or network access is used for executable discovery.
"""

from __future__ import annotations

import argparse
import os
import shutil
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, cast

from .service import ProverApplication, default_application

EngineName = Literal["auto", "haskell", "python"]


class EngineConfigurationError(ValueError):
    """A launch configuration could not select a usable requested engine."""


def add_engine_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--engine",
        choices=("auto", "haskell", "python"),
        help="search implementation (default: AGDAPROVER_ENGINE or auto; currently Python)",
    )
    parser.add_argument(
        "--symbolic-core",
        type=Path,
        help="native engine executable (or AGDAPROVER_SYMBOLIC_CORE); never built automatically",
    )


@dataclass(frozen=True)
class EngineSelection:
    requested: EngineName
    actual: Literal["haskell", "python"]
    executable: Path | None = None
    reason: str | None = None

    def application(self) -> ProverApplication:
        if self.actual == "python":
            return default_application
        from .native import NativeAgendaEngine

        if self.executable is None:
            raise EngineConfigurationError(
                "native engine selection lacks an executable"
            )
        return ProverApplication(engine=NativeAgendaEngine(self.executable))

    def report(self) -> dict[str, object]:
        # Results already record the exact native executable and model digests.
        # Do not publish workstation-specific installation paths here.
        return {
            "schema_version": "agdaprover.engine-selection.v1",
            "requested": self.requested,
            "actual": self.actual,
            "reason": self.reason,
        }

    def worker_arguments(self) -> list[str]:
        arguments = ["--engine", self.requested]
        if self.executable is not None:
            arguments += ["--symbolic-core", str(self.executable)]
        return arguments


def select_engine(
    requested: str | None = None,
    executable: Path | None = None,
    *,
    environment: Mapping[str, str] | None = None,
) -> EngineSelection:
    environment = os.environ if environment is None else environment
    choice = (
        requested
        if requested is not None
        else environment.get("AGDAPROVER_ENGINE", "auto")
    )
    if choice not in {"auto", "haskell", "python"}:
        raise EngineConfigurationError("engine must be auto, haskell or python")
    name = cast(EngineName, choice)
    if name == "auto":
        return EngineSelection(name, "python", reason="native-engine-not-qualified")
    if name == "python":
        return EngineSelection(name, "python")
    configured = (
        str(executable)
        if executable is not None
        else environment.get("AGDAPROVER_SYMBOLIC_CORE")
    )
    command = os.path.expanduser(configured) if configured else "agdaprover-symbolic"
    resolved = shutil.which(command, path=environment.get("PATH", os.defpath))
    if resolved is None or not Path(resolved).is_file():
        raise EngineConfigurationError(
            "requested Haskell engine is unavailable; set --symbolic-core or "
            "AGDAPROVER_SYMBOLIC_CORE to an installed executable, or choose --engine python"
        )
    return EngineSelection(name, "haskell", Path(resolved).resolve())
