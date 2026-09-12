"""Coarse proof-operation boundary; no per-candidate frontend decisions."""

from __future__ import annotations

from typing import Protocol

from ..contracts import ProverResult, TaskSpec
from ..kernel.protocol import KernelSessionFactory
from ..principal_variation import PrincipalVariationObserver


class SymbolicEngine(Protocol):
    """Coarse proof and provisional observation surface; never a checker callback."""

    def prove(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
    ) -> ProverResult: ...

    def prove_prefix(
        self,
        task: TaskSpec,
        *,
        session_factory: KernelSessionFactory,
        progress_observer: PrincipalVariationObserver | None = None,
    ) -> ProverResult: ...
