"""Materialize a pinned checking environment without changing module semantics.

Both speculative sessions and fresh validation use this boundary. Only the
resolved source closure and its library manifests are copied; no ambient
registrations, interfaces, user configuration or source rewrites are admitted.
"""

from __future__ import annotations

import hashlib
import time
from dataclasses import dataclass, replace
from pathlib import Path

from ..resource_budget import charge_io
from ..source_files import agda_source_suffix
from .contracts import (
    BridgeBudget,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    DiagnosticPhase,
    ModuleId,
)
from .project import ResolvedProject
from .resources import CancellationToken


@dataclass(frozen=True)
class ProjectOverlay:
    sources: tuple[tuple[ModuleId, Path], ...]
    artifacts: tuple[tuple[str, str], ...]
    total_bytes: int
    library_file: Path | None
    include_roots: tuple[Path, ...]
    configuration_paths: tuple[Path, ...] = ()

    def source_for(self, module: ModuleId) -> Path:
        return dict(self.sources)[module]


@dataclass(frozen=True)
class RootOverlayReuse:
    """Prepared root bytes; all other pinned overlay inputs are unchanged."""

    destination: Path
    content: bytes
    overlay: ProjectOverlay


def prepare_root_overlay_reuse(
    previous: ResolvedProject,
    old: ProjectOverlay,
    old_root: Path,
    project: ResolvedProject,
    new: ProjectOverlay,
    new_root: Path,
    budget: BridgeBudget,
    cancellation: CancellationToken,
) -> RootOverlayReuse | None:
    """Witness root-only reuse, never import arbitrary on-disk interfaces.

    The complete new snapshot has already been materialized independently.
    Absolute registry paths may relocate, but their routing, manifest contents,
    source ownership, module paths and every dependency byte must agree.
    A missing or modified old overlay is a miss, not permission to trust it.
    """
    if (
        previous.toolchain != project.toolchain
        or previous.root_module != project.root_module
        or previous.command_options != project.command_options
        or previous.options != project.options
        or [(s.module, s.library_name) for s in previous.sources]
        != [(s.module, s.library_name) for s in project.sources]
        or [(m, p.relative_to(old_root)) for m, p in old.sources]
        != [(m, p.relative_to(new_root)) for m, p in new.sources]
        or [p.relative_to(old_root) for p in old.include_roots]
        != [p.relative_to(new_root) for p in new.include_roots]
        or bool(old.library_file) != bool(new.library_file)
    ):
        return None
    old_artifacts, new_artifacts = dict(old.artifacts), dict(new.artifacts)
    if old_artifacts.keys() != new_artifacts.keys():
        return None
    root_relative = (
        old.source_for(previous.root_module).relative_to(old_root).as_posix()
    )
    registry_relative = (
        old.library_file.relative_to(old_root).as_posix() if old.library_file else None
    )
    old_content: dict[str, bytes] = {}
    new_content: dict[str, bytes] = {}
    for relative, expected in old.artifacts:
        cancellation.raise_if_cancelled()
        if time.monotonic() >= budget.deadline:
            raise _error(
                "root-overlay-reuse-timeout",
                "overlay comparison deadline exhausted",
                BridgeFailure.TIMEOUT,
            )
        old_path, new_path = old_root / relative, new_root / relative
        try:
            if any(
                path.is_symlink()
                for path in (old_path, *old_path.parents)
                if path == old_root or old_root in path.parents
            ):
                return None
            before = old_path.read_bytes()
        except OSError:
            return None
        # Staging belongs to this transaction. Losing it is an error, not a
        # cache miss that may fall back to adopting an incomplete snapshot.
        after = new_path.read_bytes()
        charge_io(len(before) + len(after))
        if hashlib.sha256(before).hexdigest() != expected:
            return None
        if hashlib.sha256(after).hexdigest() != new_artifacts[relative]:
            raise _error(
                "root-overlay-staging-changed",
                "staged overlay changed during comparison",
                BridgeFailure.STALE_TOKEN,
            )
        if relative == registry_relative:
            try:
                before_routes = [
                    Path(line).relative_to(old_root.resolve())
                    for line in before.decode().splitlines()
                ]
                after_routes = [
                    Path(line).relative_to(new_root.resolve())
                    for line in after.decode().splitlines()
                ]
            except (ValueError, UnicodeError):
                return None
            if before_routes != after_routes:
                return None
        elif relative != root_relative and before != after:
            return None
        if relative == root_relative:
            old_content[relative], new_content[relative] = before, after
    content = new_content[root_relative]
    artifacts = dict(old.artifacts)
    artifacts[root_relative] = new_artifacts[root_relative]
    return RootOverlayReuse(
        old_root / root_relative,
        content,
        replace(
            old,
            artifacts=tuple(sorted(artifacts.items())),
            total_bytes=old.total_bytes
            - len(old_content[root_relative])
            + len(content),
        ),
    )


def _error(code: str, message: str, failure: BridgeFailure) -> BridgeError:
    return BridgeError(
        failure,
        BridgeDiagnostic(
            code=code,
            phase=DiagnosticPhase.RESOLUTION,
            severity="error",
            message=message,
        ),
    )


def _relocated_manifest(content: bytes, includes: tuple[str, ...]) -> bytes:
    """Retain Agda's own grammar, warnings and flag pragma boundaries.

    Only path routing changes. In particular we must not accidentally repair
    an invalid duplicate/unknown field while constructing a checking overlay.
    """
    rendered = " ".join(
        path.replace("\\", "\\\\").replace(" ", "\\ ") for path in includes
    )
    lines: list[str] = []
    field: str | None = None
    replaced = False
    for line in content.decode().splitlines():
        if line and not line[0].isspace() and ":" in line and not line.startswith("--"):
            field = line.split(":", 1)[0].strip()
            if field == "include":
                lines.append("include: " + rendered)
                replaced = True
                continue
        if field != "include" or not line.strip() or line.lstrip().startswith("--"):
            lines.append(line)
    if not replaced:
        lines.append("include: " + rendered)
    return ("\n".join(lines) + "\n").encode()


def materialize_project(
    project: ResolvedProject,
    root: Path,
    budget: BridgeBudget,
    cancellation: CancellationToken,
    *,
    replacement: tuple[ModuleId, str] | None = None,
) -> ProjectOverlay:
    try:
        return _materialize_project(
            project, root, budget, cancellation, replacement=replacement
        )
    except OSError as error:
        raise _error(
            "project-overlay-io-failure",
            f"could not materialize the isolated checking environment: {error}",
            BridgeFailure.RESOURCE_EXHAUSTED,
        ) from error


def _materialize_project(
    project: ResolvedProject,
    root: Path,
    budget: BridgeBudget,
    cancellation: CancellationToken,
    *,
    replacement: tuple[ModuleId, str] | None,
) -> ProjectOverlay:
    libraries = {library.name: library for library in project.libraries}
    destinations = {
        library.name: root / "projects" / str(index)
        for index, library in enumerate(project.libraries)
    }
    artifacts: list[tuple[str, str]] = []
    written_paths: set[str] = set()
    sources: list[tuple[ModuleId, Path]] = []
    total_bytes = 0

    def write(destination: Path, content: bytes, expected: str | None = None) -> None:
        nonlocal total_bytes
        cancellation.raise_if_cancelled()
        if time.monotonic() >= budget.deadline:
            raise _error(
                "project-overlay-timeout",
                "overlay deadline exhausted",
                BridgeFailure.TIMEOUT,
            )
        if len(artifacts) >= budget.artifact_count:
            raise _error(
                "project-overlay-artifact-exhausted",
                "overlay artifact count exhausted",
                BridgeFailure.RESOURCE_EXHAUSTED,
            )
        digest = hashlib.sha256(content).hexdigest()
        if expected is not None and digest != expected:
            raise _error(
                "project-overlay-snapshot-changed",
                "an input changed during materialization",
                BridgeFailure.STALE_TOKEN,
            )
        total_bytes += len(content)
        if total_bytes > budget.temporary_bytes:
            raise _error(
                "project-overlay-storage-exhausted",
                "overlay storage budget exhausted",
                BridgeFailure.RESOURCE_EXHAUSTED,
            )
        relative = destination.relative_to(root).as_posix()
        if relative in written_paths:
            raise _error(
                "project-overlay-path-conflict",
                "two inputs map to the same overlay path",
                BridgeFailure.INVALID_REQUEST,
            )
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
        charge_io(len(content))
        artifacts.append((relative, digest))
        written_paths.add(relative)

    for source in project.sources:
        if source.library_name is not None:
            library = libraries[source.library_name]
            destination = destinations[library.name] / source.path.relative_to(
                library.manifest_path.parent
            )
        else:
            suffix = agda_source_suffix(source.path)
            if suffix is None:
                raise _error(
                    "project-overlay-source-kind",
                    "expected an Agda source",
                    BridgeFailure.INTERNAL_INVARIANT,
                )
            destination = root / Path(
                str(Path(*source.module.name.split("."))) + suffix
            )
        if replacement is not None and source.module == replacement[0]:
            content = replacement[1].encode()
            expected = None
        else:
            content = source.path.read_bytes()
            charge_io(len(content))
            expected = source.sha256
        write(destination, content, expected)
        sources.append((source.module, destination))

    manifests = []
    for library in project.libraries:
        destination = destinations[library.name] / library.manifest_path.name
        content = library.manifest_path.read_bytes()
        charge_io(len(content))
        if hashlib.sha256(content).hexdigest() != library.manifest_sha256:
            raise _error(
                "project-overlay-snapshot-changed",
                "a library manifest changed during materialization",
                BridgeFailure.STALE_TOKEN,
            )
        # Canonical relative include paths also handle absolute paths and
        # in-root symlink aliases in the original manifest. Never leave an
        # overlay manifest pointing back into the user's original tree.
        includes = tuple(
            include.relative_to(library.manifest_path.parent).as_posix()
            for include in library.include_roots
        )
        write(destination, _relocated_manifest(content, includes))
        # Empty include roots still belong to the registered library.
        for include in library.include_roots:
            (
                destinations[library.name]
                / include.relative_to(library.manifest_path.parent)
            ).mkdir(parents=True, exist_ok=True)
        manifests.append(str(destination.resolve()))
    registry = root / "libraries" if manifests else None
    if registry is not None:
        write(registry, ("\n".join(manifests) + "\n").encode())
    include_roots = tuple(
        dict.fromkeys(
            (
                root,
                *(
                    destinations[library.name]
                    / include.relative_to(library.manifest_path.parent)
                    for library in project.libraries
                    for include in library.include_roots
                ),
            )
        )
    )
    return ProjectOverlay(
        tuple(sources),
        tuple(sorted(artifacts)),
        total_bytes,
        registry,
        include_roots,
        tuple(Path(path) for path in manifests) + ((registry,) if registry else ()),
    )


def library_arguments(library_file: Path | None) -> tuple[str, ...]:
    """Never consult the user's library database or default libraries."""
    if library_file is None:
        return ("--no-libraries",)
    return ("--no-default-libraries", f"--library-file={library_file.resolve()}")
