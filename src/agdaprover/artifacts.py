"""Content identities for source and executable artifacts."""

from __future__ import annotations

import hashlib
import shutil
import time
from pathlib import Path


def file_sha256(path: Path, *, deadline: float | None = None) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            if deadline is not None and time.monotonic() >= deadline:
                raise TimeoutError("wall-time budget exhausted hashing artifact")
            digest.update(block)
    return digest.hexdigest()


def optional_file_sha256(
    path: Path | None, *, deadline: float | None = None
) -> str | None:
    return (
        file_sha256(path.resolve(), deadline=deadline)
        if path is not None and path.is_file()
        else None
    )


_EXECUTABLE_HASH_CACHE: dict[tuple[str, int, int, int, int, int], str] = {}


def executable_sha256(executable: str, *, deadline: float | None = None) -> str:
    """Hash an executable once per unchanged file, honoring a task deadline."""

    resolved = shutil.which(executable)
    if resolved is None:
        raise ValueError(f"executable not found: {executable}")
    path = Path(resolved).resolve()
    stat = path.stat()
    key = (
        str(path),
        stat.st_dev,
        stat.st_ino,
        stat.st_size,
        stat.st_mtime_ns,
        stat.st_ctime_ns,
    )
    cached = _EXECUTABLE_HASH_CACHE.get(key)
    if cached is not None:
        return cached

    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            if deadline is not None and time.monotonic() >= deadline:
                raise TimeoutError("wall-time budget exhausted hashing toolchain")
            digest.update(block)
    value = digest.hexdigest()
    _EXECUTABLE_HASH_CACHE[key] = value
    return value
