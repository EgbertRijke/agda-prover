"""Optional local native acceleration behind a versioned, proof-neutral ABI.

The module never builds or downloads code at runtime.  A release or developer
may build ``native/`` explicitly; otherwise every operation uses the exact
deterministic Python implementation.  Native results only schedule or compose
proposals and therefore confer no verification authority.
"""

from __future__ import annotations

import ctypes
import math
import os
import platform
from array import array
from collections.abc import Mapping, Sequence
from pathlib import Path

NATIVE_ABI_VERSION = 3


def _library_name() -> str:
    system = platform.system()
    if system == "Darwin":
        return "libagdaprover_native.dylib"
    if system == "Windows":
        return "agdaprover_native.dll"
    return "libagdaprover_native.so"


def default_native_library() -> Path:
    return (
        Path(__file__).resolve().parents[2] / "native/target/release" / _library_name()
    )


class NativeBackend:
    """Validated ctypes binding; construction is all-or-nothing."""

    def __init__(self, path: Path) -> None:
        self.path = path.resolve()
        self._library = ctypes.CDLL(str(self.path))
        self._library.agdaprover_native_abi_version.argtypes = []
        self._library.agdaprover_native_abi_version.restype = ctypes.c_uint32
        if self._library.agdaprover_native_abi_version() != NATIVE_ABI_VERSION:
            raise ValueError("unsupported AgdaProver native ABI")
        self._bind()

    def _bind(self) -> None:
        library = self._library
        library.agdaprover_nnue_score_batch.argtypes = [
            ctypes.POINTER(ctypes.c_float),
            ctypes.POINTER(ctypes.c_float),
            ctypes.c_size_t,
            ctypes.c_size_t,
            ctypes.POINTER(ctypes.c_float),
            ctypes.c_float,
            ctypes.POINTER(ctypes.c_size_t),
            ctypes.POINTER(ctypes.c_uint32),
            ctypes.POINTER(ctypes.c_float),
            ctypes.c_size_t,
            ctypes.c_size_t,
            ctypes.POINTER(ctypes.c_float),
        ]
        library.agdaprover_nnue_score_batch.restype = ctypes.c_int32

    @staticmethod
    def _pointer(values: array, ctype: type[ctypes._SimpleCData]) -> object:
        return (ctype * len(values)).from_buffer(values)

    @staticmethod
    def _validate_model_shape(
        base: Sequence[float],
        embeddings: Sequence[float],
        input_size: int,
        hidden_size: int,
        weights: Sequence[float],
    ) -> None:
        if input_size <= 0 or hidden_size <= 0:
            raise ValueError("native NNUE dimensions must be positive")
        if (
            len(base) != hidden_size
            or len(embeddings) != input_size * hidden_size
            or len(weights) != hidden_size
        ):
            raise ValueError("native NNUE buffers do not match their dimensions")

    def nnue_score_batch(
        self,
        base_accumulator: Sequence[float],
        embeddings: Sequence[float],
        input_size: int,
        hidden_size: int,
        output_weights: Sequence[float],
        output_bias: float,
        feature_batches: Sequence[Mapping[int, float]],
    ) -> list[float]:
        base = array("f", base_accumulator)
        embedding_values = array("f", embeddings)
        weights = array("f", output_weights)
        self._validate_model_shape(
            base, embedding_values, input_size, hidden_size, weights
        )
        if not all(
            math.isfinite(value)
            for values_to_check in (base, embedding_values, weights)
            for value in values_to_check
        ):
            raise ValueError("NNUE values exceed the native float32 domain")
        offsets = array("Q", [0])
        indices = array("I")
        values = array("f")
        if not math.isfinite(output_bias):
            raise ValueError("NNUE values exceed the native float32 domain")
        for features in feature_batches:
            for index, value in sorted(features.items()):
                if not 0 <= index < input_size or not math.isfinite(value):
                    raise ValueError("invalid sparse NNUE feature")
                indices.append(index)
                values.append(value)
            offsets.append(len(indices))
        output = array("f", [0.0]) * len(feature_batches)
        status = self._library.agdaprover_nnue_score_batch(
            self._pointer(base, ctypes.c_float),
            self._pointer(embedding_values, ctypes.c_float),
            input_size,
            hidden_size,
            self._pointer(weights, ctypes.c_float),
            output_bias,
            self._pointer(offsets, ctypes.c_size_t),
            self._pointer(indices, ctypes.c_uint32),
            self._pointer(values, ctypes.c_float),
            len(feature_batches),
            len(indices),
            self._pointer(output, ctypes.c_float),
        )
        if status != 0:
            raise RuntimeError(f"native NNUE scoring failed: {status}")
        return list(output)


_BACKEND: NativeBackend | None | bool = False


def native_backend() -> NativeBackend | None:
    global _BACKEND
    if os.environ.get("AGDAPROVER_DISABLE_NATIVE") == "1":
        return None
    if _BACKEND is False:
        configured = os.environ.get("AGDAPROVER_NATIVE_LIBRARY")
        path = Path(configured) if configured else default_native_library()
        try:
            _BACKEND = NativeBackend(path) if path.is_file() else None
        except (OSError, ValueError):
            _BACKEND = None
    return _BACKEND if isinstance(_BACKEND, NativeBackend) else None


def reset_native_backend() -> None:
    """Forget the optional artifact, primarily for fallback tests."""

    global _BACKEND
    _BACKEND = False


__all__ = [
    "NATIVE_ABI_VERSION",
    "NativeBackend",
    "default_native_library",
    "native_backend",
    "reset_native_backend",
]
