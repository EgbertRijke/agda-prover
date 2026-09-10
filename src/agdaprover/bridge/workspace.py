"""Provisional source projects with explicitly rebound library configuration."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, replace
from pathlib import Path

from ..artifacts import executable_sha256, file_sha256
from ..project_configuration import ProjectConfiguration
from ..resource_budget import charge_io
from .configuration import project_request
from .contracts import BridgeBudget
from .overlay import _relocated_manifest, materialize_project
from .project import (
    ResolvedProject,
    _nearest_project_manifest,
    resolve_project,
    write_source_overlay,
)
from .resources import CancellationToken


@dataclass(frozen=True)
class ProjectInputs:
    """The original checking inputs, distinct from mutable branch overlays."""

    files: tuple[tuple[Path, str], ...]
    executable: Path
    executable_hash: str
    library_bound: bool

    @property
    def identity(self) -> str:
        content = {
            "files": [(str(path), digest) for path, digest in self.files],
            "executable": self.executable_hash,
        }
        return hashlib.sha256(
            json.dumps(content, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()

    def assert_current(self, *, deadline: float | None = None) -> None:
        for path, digest in self.files:
            if path.is_file():
                charge_io(path.stat().st_size)
            if not path.is_file() or file_sha256(path, deadline=deadline) != digest:
                raise ValueError(f"checking input changed during search: {path}")
        if (
            executable_sha256(str(self.executable), deadline=deadline)
            != self.executable_hash
        ):
            raise ValueError("Agda executable changed during search")


def project_inputs(project: ResolvedProject) -> ProjectInputs:
    return ProjectInputs(
        tuple((source.path, source.sha256) for source in project.sources)
        + project.configuration_files,
        project.toolchain.executable,
        project.toolchain.executable_sha256,
        bool(project.libraries),
    )


@dataclass(frozen=True)
class SourceWorkspace:
    source_file: Path
    files: tuple[tuple[Path, Path], ...]
    configuration: ProjectConfiguration | None
    total_bytes: int
    inputs: ProjectInputs | None = None


def checking_environment(project: ResolvedProject) -> dict[str, object]:
    """Compare prefix checks across relocation without ignoring library meaning.

    Registry bytes contain temporary absolute paths and cannot be compared as
    content identities across two workspaces. Bind the registered manifests,
    include topology, source ownership and options instead, not only filenames.
    """
    libraries = []
    for library in project.libraries:
        raw = library.manifest_path.read_bytes()
        charge_io(len(raw))
        if hashlib.sha256(raw).hexdigest() != library.manifest_sha256:
            raise OSError("library manifest changed during validation")
        includes = tuple(
            path.relative_to(library.manifest_path.parent).as_posix()
            for path in library.include_roots
        )
        libraries.append(
            {
                "name": library.name,
                "includes": list(includes),
                "manifest_sha256": hashlib.sha256(
                    _relocated_manifest(raw, includes)
                ).hexdigest(),
            }
        )
    return {
        "schema_version": "agdaprover.checking-environment.v1",
        "root_module": project.root_module.name,
        "command_options": list(project.command_options),
        "libraries": libraries,
        "sources": {
            source.module.name: {
                "sha256": source.sha256,
                "library": source.library_name,
            }
            for source in project.sources
            if source.module != project.root_module
        },
    }


def prepare_source_workspace(
    source_file: Path,
    candidate: str,
    root: Path,
    *,
    configuration: ProjectConfiguration | None = None,
    timeout_seconds: float = float("inf"),
) -> SourceWorkspace:
    manifest, _ = _nearest_project_manifest(source_file.resolve())
    if configuration is None and manifest is None:
        path, files = write_source_overlay(source_file, candidate, root)
        return SourceWorkspace(
            path, files, None, sum(path.stat().st_size for _, path in files)
        )
    effective = configuration or ProjectConfiguration()
    budget = BridgeBudget.for_run(timeout_seconds)
    project, _ = resolve_project(project_request(source_file, effective), budget)
    overlay = materialize_project(
        project,
        root,
        budget,
        CancellationToken(),
        replacement=(project.root_module, candidate),
    )
    return SourceWorkspace(
        overlay.source_for(project.root_module),
        tuple(
            (source.path, overlay.source_for(source.module))
            for source in project.sources
        ),
        replace(
            effective,
            executable=str(project.toolchain.executable),
            library_file=overlay.library_file,
        ),
        overlay.total_bytes,
        project_inputs(project),
    )
