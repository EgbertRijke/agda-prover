"""Typed application service over proof-search implementations.

Frontends depend on this service, never on individual search controllers. The
legacy module-level entry points remain supported while the prototype evolves.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from ..contracts import ProverResult, StepResult, TaskSpec
from ..joint import prove_joint_prefix
from ..kernel.p0 import default_session_factory
from ..kernel.protocol import KernelSessionFactory
from ..principal_variation import PrincipalVariationObserver
from ..search import prove
from ..step import propose_step
from .engine import SymbolicEngine
from .entry_testing import test_entries
from .evidence import NativeEvidenceEngine
from .inspection import CommandResult


@dataclass(frozen=True)
class ProverApplication:
    """Composition root for proof, prefix, step, and independent entry tests."""

    session_factory: KernelSessionFactory = default_session_factory
    engine: SymbolicEngine | None = None

    def prove(self, task: TaskSpec, *, include_attempts: bool = True) -> ProverResult:
        if self.engine is not None:
            return self.engine.prove(task, session_factory=self.session_factory)
        return prove(
            task,
            include_attempts=include_attempts,
            session_factory=self.session_factory,
        )

    def prove_prefix(
        self,
        task: TaskSpec,
        *,
        progress_observer: PrincipalVariationObserver | None = None,
    ) -> ProverResult:
        if self.engine is not None:
            if progress_observer is not None:
                raise ValueError(
                    "selected engine has not qualified principal-variation publication"
                )
            return self.engine.prove_prefix(task, session_factory=self.session_factory)
        return prove_joint_prefix(
            task,
            session_factory=self.session_factory,
            progress_observer=progress_observer,
        )

    def prove_evidence(
        self, task: TaskSpec, *, engine: NativeEvidenceEngine
    ) -> ProverResult:
        """Explicit native first slice; production engine selection is unchanged."""
        return engine.prove(task, session_factory=self.session_factory)

    def step(self, task: TaskSpec, *, collect_all: bool = False) -> StepResult:
        if self.engine is not None:
            raise ValueError("selected engine has not qualified one-step operations")
        return propose_step(
            task,
            collect_all=collect_all,
            session_factory=self.session_factory,
        )

    def test_entries(
        self, task: TaskSpec, *, publish: Callable[[str, dict[str, Any]], None]
    ) -> CommandResult:
        return test_entries(task, solve=self.prove, publish=publish)


default_application = ProverApplication()
