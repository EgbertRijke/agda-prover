"""Coarse proof-operation boundary; no per-candidate frontend decisions."""

from __future__ import annotations

from typing import Protocol

from ..contracts import ProverResult, TaskSpec
from ..kernel.protocol import KernelSessionFactory


class SymbolicEngine(Protocol):
    """Initial proof surface; step/PV qualification is still separate."""

    def prove(
        self, task: TaskSpec, *, session_factory: KernelSessionFactory
    ) -> ProverResult: ...

    def prove_prefix(
        self, task: TaskSpec, *, session_factory: KernelSessionFactory
    ) -> ProverResult: ...
