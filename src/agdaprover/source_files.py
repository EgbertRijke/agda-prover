"""Shared recognition and discovery of Agda source-file formats."""

from __future__ import annotations

from collections.abc import Iterator
from pathlib import Path

# Longest first so compound suffixes remain one semantic file kind.
AGDA_SOURCE_SUFFIXES = (".lagda.md", ".agda", ".lagda")
PROVER_SOURCE_SUFFIXES = (".lagda.md", ".agda")


def agda_source_suffix(path: str | Path) -> str | None:
    """Return PATH's supported Agda suffix, including compound suffixes."""

    name = Path(path).name
    return next(
        (suffix for suffix in AGDA_SOURCE_SUFFIXES if name.endswith(suffix)), None
    )


def is_agda_source_path(path: str | Path) -> bool:
    """Whether PATH names one supported Agda source format."""

    return agda_source_suffix(path) is not None


def is_prover_source_path(path: str | Path) -> bool:
    """Whether PATH names a source format qualified for prover entry points."""

    name = Path(path).name
    return any(name.endswith(suffix) for suffix in PROVER_SOURCE_SUFFIXES)


def require_agda_source_file(path: Path) -> None:
    """Reject missing files and source formats unsupported by the prover."""

    if not path.is_file() or not is_prover_source_path(path):
        supported = ", ".join(PROVER_SOURCE_SUFFIXES)
        raise ValueError(f"source must be an existing Agda file ({supported})")


def iter_agda_source_files(directory: Path) -> Iterator[Path]:
    """Yield supported source files recursively in deterministic path order."""

    paths = {
        path
        for suffix in PROVER_SOURCE_SUFFIXES
        for path in directory.rglob(f"*{suffix}")
        if path.is_file()
    }
    yield from sorted(paths)


def agda_interface_path(source: Path) -> Path:
    """Return Agda's interface path for a recognized source filename."""

    suffix = agda_source_suffix(source)
    if suffix is None:
        raise ValueError(f"unsupported Agda source filename: {source.name}")
    return Path(f"{source!s}"[: -len(suffix)] + ".agdai")


__all__ = [
    "AGDA_SOURCE_SUFFIXES",
    "PROVER_SOURCE_SUFFIXES",
    "agda_interface_path",
    "agda_source_suffix",
    "is_agda_source_path",
    "is_prover_source_path",
    "iter_agda_source_files",
    "require_agda_source_file",
]
