"""A tiny dependency-free, incrementally updatable action ranker."""

from __future__ import annotations

import hashlib
import json
import math
import struct
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from itertools import chain
from pathlib import Path

from .actions import RefinementCandidate
from .contracts import GoalInfo
from .native import native_backend
from .ranking.features import (
    action_feature_tokens,
    hash_features,
    refinement_action_feature_tokens,
    state_feature_tokens,
)
from .ranking.features import merge_sparse as merge_sparse
from .ranking.focused_policy import FocusedPolicy
from .ranking.protocol import ModelRole
from .terms import Term

FocusedNNUEPolicy = FocusedPolicy

MODEL_SCHEMA_VERSION = "agdaprover.nnue.p0.v2"
LEGACY_MODEL_SCHEMA_VERSION = "agdaprover.nnue.p0.v1"
FEATURE_SCHEMA_VERSION = "agdaprover.features.p0.v2"
MAGIC = b"APNNUE2\0"
LEGACY_MAGIC = b"APNNUE1\0"

MODEL_FEATURE_FAMILIES: dict[ModelRole, str] = {
    "proof-term-ranking": "proof-term-v2",
    "one-step-refinement-ranking": "one-step-refinement-v2",
    "focused-search-branch-policy": "focused-branch-v2",
    "or-decision-ranking": "or-decision-v4",
}
MAX_INPUT_SIZE = 1_048_576
MAX_HIDDEN_SIZE = 4_096
MAX_PARAMETER_BYTES = 16 * 1024 * 1024
MAX_HEADER_BYTES = 64 * 1024
MAX_MODEL_FILE_BYTES = (
    max(len(MAGIC), len(LEGACY_MAGIC)) + 4 + MAX_HEADER_BYTES + MAX_PARAMETER_BYTES
)


def _validate_dimensions(input_size: int, hidden_size: int) -> None:
    if not isinstance(input_size, int) or not isinstance(hidden_size, int):
        raise ValueError("NNUE dimensions must be integers")
    if not 1 <= input_size <= MAX_INPUT_SIZE:
        raise ValueError(f"NNUE input size must be in [1, {MAX_INPUT_SIZE}]")
    if not 1 <= hidden_size <= MAX_HIDDEN_SIZE:
        raise ValueError(f"NNUE hidden size must be in [1, {MAX_HIDDEN_SIZE}]")
    parameter_count = hidden_size + input_size * hidden_size + hidden_size + 1
    if parameter_count * 4 > MAX_PARAMETER_BYTES:
        raise ValueError(
            f"NNUE payload exceeds the {MAX_PARAMETER_BYTES}-byte safety cap"
        )


def _role_from_header_or_legacy_manifest(
    path: Path, header: Mapping[str, object]
) -> ModelRole:
    role = header.get("role")
    if role is None and header.get("schema_version") == LEGACY_MODEL_SCHEMA_VERSION:
        manifest_path = path.with_name(path.name + ".json")
        try:
            manifest = json.loads(manifest_path.read_text())
            role = manifest.get("training", {}).get("role")
        except (OSError, AttributeError, json.JSONDecodeError, UnicodeDecodeError):
            role = None
    if role not in MODEL_FEATURE_FAMILIES:
        raise ValueError(
            "NNUE model has no supported role; retrain it with a role-specific command"
        )
    return role


@dataclass
class NNUEModel:
    role: ModelRole
    input_size: int
    hidden_size: int
    hidden_bias: list[float]
    embeddings: list[float]
    output_weights: list[float]
    output_bias: float
    seed: int
    model_id: str = "unpersisted"

    def __post_init__(self) -> None:
        _validate_dimensions(self.input_size, self.hidden_size)
        expected_embeddings = self.input_size * self.hidden_size
        if len(self.hidden_bias) != self.hidden_size:
            raise ValueError("NNUE hidden-bias length does not match header")
        if len(self.embeddings) != expected_embeddings:
            raise ValueError("NNUE embedding length does not match header")
        if len(self.output_weights) != self.hidden_size:
            raise ValueError("NNUE output-weight length does not match header")
        if self.role not in MODEL_FEATURE_FAMILIES:
            raise ValueError(f"unsupported NNUE model role: {self.role!r}")
        values = chain(
            self.hidden_bias,
            self.embeddings,
            self.output_weights,
            (self.output_bias,),
        )
        if not all(math.isfinite(value) for value in values):
            raise ValueError("NNUE parameters contain a non-finite weight")

    def accumulator(self, features: Mapping[int, float]) -> list[float]:
        accumulator = self.hidden_bias.copy()
        return self.update_accumulator(accumulator, add=features)

    def update_accumulator(
        self,
        accumulator: list[float],
        *,
        add: Mapping[int, float] | None = None,
        remove: Mapping[int, float] | None = None,
    ) -> list[float]:
        result = accumulator.copy()
        for feature_set, direction in ((remove or {}, -1.0), (add or {}, 1.0)):
            for index, value in feature_set.items():
                if not 0 <= index < self.input_size:
                    raise ValueError(f"feature index out of range: {index}")
                offset = index * self.hidden_size
                scale = direction * value
                for hidden in range(self.hidden_size):
                    result[hidden] += scale * self.embeddings[offset + hidden]
        return result

    @staticmethod
    def _activate(value: float) -> float:
        return min(1.0, max(0.0, value))

    def score_accumulator(self, accumulator: list[float]) -> float:
        if len(accumulator) != self.hidden_size:
            raise ValueError("NNUE accumulator length does not match hidden size")
        return self.output_bias + sum(
            self.output_weights[index] * self._activate(value)
            for index, value in enumerate(accumulator)
        )

    def score_feature_batches(
        self,
        base_accumulator: list[float],
        feature_batches: Sequence[Mapping[int, float]],
    ) -> list[float]:
        """Score one OR batch natively when available, with exact fallback."""

        backend = native_backend()
        if backend is not None and len(feature_batches) > 1:
            try:
                scores = backend.nnue_score_batch(
                    base_accumulator,
                    self.embeddings,
                    self.input_size,
                    self.hidden_size,
                    self.output_weights,
                    self.output_bias,
                    feature_batches,
                )
                if all(math.isfinite(score) for score in scores):
                    return scores
            except (ArithmeticError, RuntimeError, ValueError):
                pass
        return [
            self.score_accumulator(
                self.update_accumulator(base_accumulator, add=features)
            )
            for features in feature_batches
        ]

    def score(self, goal: GoalInfo, term: Term) -> float:
        return self.score_terms(goal, (term,))[0]

    def score_terms(self, goal: GoalInfo, terms: Sequence[Term]) -> list[float]:
        """Score actions by reusing the state accumulator across every candidate."""

        self.require_role("proof-term-ranking")

        state = hash_features(state_feature_tokens(goal), self.input_size)
        state_accumulator = self.accumulator(state)
        return self.score_feature_batches(
            state_accumulator,
            tuple(
                hash_features(action_feature_tokens(goal, term), self.input_size)
                for term in terms
            ),
        )

    def score_refinement_actions(
        self, goal: GoalInfo, candidates: Sequence[RefinementCandidate]
    ) -> list[float]:
        """Score next-step actions while reusing the proof-state accumulator."""

        self.require_role("one-step-refinement-ranking")

        state = hash_features(state_feature_tokens(goal), self.input_size)
        state_accumulator = self.accumulator(state)
        return self.score_feature_batches(
            state_accumulator,
            tuple(
                hash_features(
                    refinement_action_feature_tokens(goal, candidate),
                    self.input_size,
                )
                for candidate in candidates
            ),
        )

    @property
    def feature_family(self) -> str:
        return MODEL_FEATURE_FAMILIES[self.role]

    def require_role(self, expected: ModelRole) -> None:
        if self.role != expected:
            raise ValueError(
                f"NNUE role mismatch: expected {expected!r}, found {self.role!r}"
            )

    @classmethod
    def load(
        cls,
        path: Path,
        *,
        expected_role: ModelRole | None = None,
        deadline: float | None = None,
    ) -> NNUEModel:
        if path.stat().st_size > MAX_MODEL_FILE_BYTES:
            raise ValueError("NNUE model file exceeds safety cap")
        chunks: list[bytes] = []
        total = 0
        with path.open("rb") as stream:
            while block := stream.read(1024 * 1024):
                if deadline is not None and time.monotonic() >= deadline:
                    raise TimeoutError("wall-time budget exhausted loading NNUE model")
                total += len(block)
                if total > MAX_MODEL_FILE_BYTES:
                    raise ValueError("NNUE model file exceeds safety cap")
                chunks.append(block)
        contents = b"".join(chunks)
        magic = MAGIC if contents.startswith(MAGIC) else LEGACY_MAGIC
        if not contents.startswith(magic):
            raise ValueError("invalid NNUE model magic")
        if len(contents) < len(magic) + 4:
            raise ValueError("truncated NNUE model header")
        header_size = struct.unpack("<I", contents[len(magic) : len(magic) + 4])[0]
        if header_size > MAX_HEADER_BYTES:
            raise ValueError("NNUE model header exceeds safety cap")
        header_start = len(magic) + 4
        header_end = header_start + header_size
        if len(contents) < header_end:
            raise ValueError("truncated NNUE model header")
        try:
            header = json.loads(contents[header_start:header_end])
        except (json.JSONDecodeError, UnicodeDecodeError) as error:
            raise ValueError("invalid NNUE model header") from error
        schema = header.get("schema_version")
        if schema not in {MODEL_SCHEMA_VERSION, LEGACY_MODEL_SCHEMA_VERSION}:
            raise ValueError("unsupported NNUE model schema")
        if header.get("feature_schema_version") != FEATURE_SCHEMA_VERSION:
            raise ValueError("unsupported NNUE feature schema")
        try:
            input_size = int(header["input_size"])
            hidden_size = int(header["hidden_size"])
            seed = int(header["seed"])
        except (KeyError, TypeError, ValueError, OverflowError) as error:
            raise ValueError("invalid NNUE dimension or seed header") from error
        _validate_dimensions(input_size, hidden_size)
        role = _role_from_header_or_legacy_manifest(path, header)
        if expected_role is not None and role != expected_role:
            raise ValueError(
                f"NNUE role mismatch: expected {expected_role!r}, found {role!r}"
            )
        if schema == MODEL_SCHEMA_VERSION:
            expected_family = MODEL_FEATURE_FAMILIES[role]
            if header.get("feature_family") != expected_family:
                raise ValueError("NNUE feature family does not match its model role")
        count = hidden_size + input_size * hidden_size + hidden_size + 1
        expected_bytes = count * 4
        payload = contents[header_end:]
        if len(payload) != expected_bytes:
            raise ValueError("truncated or oversized NNUE payload")
        values = list(struct.unpack(f"<{count}f", payload))
        if not all(math.isfinite(value) for value in values):
            raise ValueError("NNUE payload contains a non-finite weight")
        cursor = 0
        hidden_bias = values[cursor : cursor + hidden_size]
        cursor += hidden_size
        embeddings = values[cursor : cursor + input_size * hidden_size]
        cursor += input_size * hidden_size
        output_weights = values[cursor : cursor + hidden_size]
        cursor += hidden_size
        output_bias = values[cursor]
        return cls(
            role=role,
            input_size=input_size,
            hidden_size=hidden_size,
            hidden_bias=hidden_bias,
            embeddings=embeddings,
            output_weights=output_weights,
            output_bias=output_bias,
            seed=seed,
            model_id=hashlib.sha256(contents).hexdigest(),
        )
