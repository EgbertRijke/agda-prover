"""Pinned, offline inference artifacts shipped with the product.

Only role-compatible defaults live here; training and model promotion remain
development responsibilities. An explicit path always selects the user's model.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from ..nnue import NNUEModel
from .protocol import ModelRole


@dataclass(frozen=True)
class BundledModel:
    filename: str
    role: ModelRole
    sha256: str

    @property
    def path(self) -> Path:
        return Path(__file__).resolve().parents[1] / "data" / "models" / self.filename

    def load(self, *, deadline: float | None) -> NNUEModel:
        model = NNUEModel.load(self.path, expected_role=self.role, deadline=deadline)
        if model.model_id != self.sha256:
            raise ValueError(
                f"bundled NNUE checksum mismatch: {self.filename}; "
                "reinstall AgdaProver or use --ranker symbolic"
            )
        return model


FOCUSED_MODEL = BundledModel(
    "focused.apnnue",
    "focused-search-branch-policy",
    "2e0e202bf12012d0805fbca1ceea0f7c341070efd1a2fdeb043035a92dc37499",
)
STEP_MODEL = BundledModel(
    "step.apnnue",
    "one-step-refinement-ranking",
    "8a30df44ab425c2f86f0ea8739e681761cf3a01fec316994e9eb21ef7e1761d7",
)
OR_MODEL = BundledModel(
    "or-policy.apnnue",
    "or-decision-ranking",
    "a2072fd6c874db7ea8542cb1223400a537a07d0c2e7ba90754909ed7301c439f",
)
