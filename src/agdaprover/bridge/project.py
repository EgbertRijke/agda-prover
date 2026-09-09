"""Resolve one immutable Agda project before a kernel process is started."""

from __future__ import annotations

import hashlib
import math
import os
import platform
import re
import shlex
import shutil
import subprocess
import time
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path

from ..artifacts import executable_sha256, file_sha256
from ..resource_budget import charge_io, checkpoint
from ..source_files import (
    AGDA_SOURCE_SUFFIXES,
    agda_interface_path,
    agda_source_suffix,
    is_agda_source_path,
)
from .contracts import (
    BridgeBudget,
    BridgeCost,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    CapabilityManifest,
    DiagnosticPhase,
    EnvironmentId,
    ModuleId,
    ProjectHandle,
    SourceRevision,
    stable_hash,
)
from .operations import OpenProjectRequest, OpenProjectResult
from .source_text import mask_agda_source
from .versions import adapter_for_version

_MODULE = re.compile(
    r"(?m)^\s*module\s+([A-Za-z_][\w'.]*(?:\.[A-Za-z_][\w']*)*)\s+where\b"
)
_IMPORT = re.compile(
    r"(?m)^\s*(?:open\s+)?import\s+([A-Za-z_][\w'.]*(?:\.[A-Za-z_][\w']*)*)\b"
)
_OPTIONS = re.compile(r"\{-#\s*OPTIONS\s+(.+?)#-\}", re.DOTALL)

_TOOLCHAIN_MODULES = frozenset({"Agda.Primitive"})


def _is_toolchain_module(name: str) -> bool:
    """Return whether Agda supplies ``name`` independently of source roots."""

    return name in _TOOLCHAIN_MODULES or name.startswith("Agda.Builtin.")


@dataclass(frozen=True)
class ToolchainIdentity:
    executable: Path
    version: str
    executable_sha256: str
    size: int

    def semantic_dict(self) -> dict[str, str | int]:
        return {
            "version": self.version,
            "executable_sha256": self.executable_sha256,
            "size": self.size,
        }


_TOOLCHAIN_CACHE: dict[tuple[str, int, int, int, int, int], ToolchainIdentity] = {}


@dataclass(frozen=True)
class LibraryIdentity:
    name: str
    manifest_path: Path
    manifest_sha256: str
    include_roots: tuple[Path, ...]
    dependencies: tuple[str, ...]

    def semantic_dict(self, project_root: Path) -> dict[str, object]:
        return {
            "name": self.name,
            "manifest_sha256": self.manifest_sha256,
            "include_roots": [
                _portable_path(root, project_root) for root in self.include_roots
            ],
            "dependencies": list(self.dependencies),
        }


@dataclass(frozen=True)
class SourceIdentity:
    module: ModuleId
    path: Path
    sha256: str
    imports: tuple[str, ...]
    interface_sha256: str | None

    def semantic_dict(self) -> dict[str, object]:
        return {
            "module": self.module.to_dict(),
            "sha256": self.sha256,
            "imports": list(self.imports),
            "interface_sha256": self.interface_sha256,
        }


@dataclass(frozen=True)
class ResolvedProject:
    project_root: Path
    source_roots: tuple[Path, ...]
    root_module: ModuleId
    root_source: Path
    toolchain: ToolchainIdentity
    options: tuple[str, ...]
    libraries: tuple[LibraryIdentity, ...]
    sources: tuple[SourceIdentity, ...]
    environment_id: EnvironmentId
    source_revision: SourceRevision
    capabilities: CapabilityManifest
    handle: ProjectHandle

    def source_for(self, module: ModuleId) -> Path:
        matches = [source.path for source in self.sources if source.module == module]
        if len(matches) != 1:
            raise KeyError(f"module is not uniquely resolved: {module.name}")
        return matches[0]

    @property
    def module_graph(self) -> tuple[tuple[str, tuple[str, ...]], ...]:
        return tuple((source.module.name, source.imports) for source in self.sources)


def _portable_path(path: Path, project_root: Path) -> str:
    try:
        return path.relative_to(project_root).as_posix()
    except ValueError:
        return f"external:{path.name}"


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


def detect_toolchain(executable: str, budget: BridgeBudget) -> ToolchainIdentity:
    resolved = shutil.which(executable)
    if resolved is None:
        raise _error(
            "agda-not-found",
            f"Agda executable not found: {executable}; install the pinned 2.8.0 toolchain",
            BridgeFailure.TOOLCHAIN_ERROR,
        )
    path = Path(resolved).resolve()
    try:
        remaining = budget.remaining_seconds()
        stat = path.stat()
        cache_key = (
            str(path),
            stat.st_dev,
            stat.st_ino,
            stat.st_size,
            stat.st_mtime_ns,
            stat.st_ctime_ns,
        )
        cached = _TOOLCHAIN_CACHE.get(cache_key)
        if cached is not None:
            return cached
        completed = subprocess.run(
            [str(path), "--numeric-version"],
            check=False,
            capture_output=True,
            text=True,
            timeout=remaining if math.isfinite(remaining) else None,
            env=_tool_environment(),
        )
    except (OSError, TimeoutError, subprocess.TimeoutExpired) as error:
        failure = (
            BridgeFailure.TIMEOUT
            if isinstance(error, (TimeoutError, subprocess.TimeoutExpired))
            else BridgeFailure.TOOLCHAIN_ERROR
        )
        raise _error(
            "agda-version-query-failed",
            f"could not query Agda version: {error}",
            failure,
        ) from error
    version = completed.stdout.strip()
    if completed.returncode != 0 or not version:
        raise _error(
            "agda-version-query-failed",
            (
                completed.stderr or completed.stdout or "Agda returned no version"
            ).strip(),
            BridgeFailure.TOOLCHAIN_ERROR,
        )
    # Selecting the adapter here deliberately fails before source loading.
    adapter_for_version(version)
    try:
        executable_digest = executable_sha256(str(path), deadline=budget.deadline)
    except (OSError, TimeoutError, ValueError) as error:
        failure = (
            BridgeFailure.TIMEOUT
            if isinstance(error, TimeoutError)
            else BridgeFailure.TOOLCHAIN_ERROR
        )
        raise _error(
            "agda-executable-hash-failed",
            f"could not hash the Agda executable: {error}",
            failure,
        ) from error
    identity = ToolchainIdentity(path, version, executable_digest, stat.st_size)
    _TOOLCHAIN_CACHE[cache_key] = identity
    return identity


def _tool_environment() -> dict[str, str]:
    allowed = ("PATH", "LANG", "LC_ALL", "TMPDIR", "SYSTEMROOT")
    return {name: os.environ[name] for name in allowed if name in os.environ}


def _parse_agda_lib(path: Path, budget: BridgeBudget) -> LibraryIdentity:
    fields: dict[str, list[str]] = {}
    current: str | None = None
    for raw_line in path.read_text().splitlines():
        if time.monotonic() >= budget.deadline:
            raise _error(
                "project-resolution-timeout",
                "project resolution exceeded its wall-time budget",
                BridgeFailure.TIMEOUT,
            )
        line = raw_line.split("--", 1)[0].rstrip()
        if not line:
            continue
        if not line[0].isspace() and ":" in line:
            name, value = line.split(":", 1)
            current = name.strip().lower()
            fields.setdefault(current, []).append(value.strip())
        elif current is not None:
            fields[current].append(line.strip())
        else:
            raise _error(
                "malformed-library-file",
                f"malformed .agda-lib entry in {path.name}: {raw_line!r}",
                BridgeFailure.INVALID_REQUEST,
            )
    name = " ".join(fields.get("name", [])).strip() or path.stem
    includes = " ".join(fields.get("include", [])).split() or ["."]
    roots: list[Path] = []
    manifest_root = path.parent.resolve()
    for include in includes:
        root = (path.parent / include).resolve()
        if not root.is_dir() or not _within(root, manifest_root):
            raise _error(
                "library-include-escape",
                f"library include is missing or escapes its manifest root: {include}",
                BridgeFailure.INVALID_REQUEST,
            )
        roots.append(root)
    dependencies = tuple(
        sorted(filter(None, " ".join(fields.get("depend", [])).split()))
    )
    return LibraryIdentity(
        name=name,
        manifest_path=path.resolve(),
        manifest_sha256=file_sha256(path.resolve(), deadline=budget.deadline),
        include_roots=tuple(roots),
        dependencies=dependencies,
    )


def _library_database(path: Path | None, budget: BridgeBudget) -> dict[str, Path]:
    if path is None:
        return {}
    if not path.is_file():
        raise _error(
            "library-database-missing",
            f"Agda library database does not exist: {path}",
            BridgeFailure.INVALID_REQUEST,
        )
    result: dict[str, Path] = {}
    for line in path.read_text().splitlines():
        entry = line.split("--", 1)[0].strip()
        if not entry:
            continue
        manifest = Path(os.path.expandvars(os.path.expanduser(entry))).resolve()
        if not manifest.is_file():
            raise _error(
                "library-manifest-missing",
                f"registered Agda library does not exist: {manifest}",
                BridgeFailure.INVALID_REQUEST,
            )
        library = _parse_agda_lib(manifest, budget)
        if library.name in result:
            raise _error(
                "duplicate-library-name",
                f"multiple registered libraries are named {library.name!r}",
                BridgeFailure.INVALID_REQUEST,
            )
        result[library.name] = manifest
    return result


def _resolve_libraries(
    project_manifest: Path | None,
    library_file: Path | None,
    budget: BridgeBudget,
) -> tuple[LibraryIdentity, ...]:
    if project_manifest is None:
        return ()
    root_library = _parse_agda_lib(project_manifest, budget)
    database = _library_database(library_file, budget)
    resolved: dict[str, LibraryIdentity] = {root_library.name: root_library}
    queue = list(root_library.dependencies)
    while queue:
        dependency = queue.pop()
        if dependency in resolved:
            continue
        manifest = database.get(dependency)
        if manifest is None:
            raise _error(
                "library-dependency-missing",
                f"Agda library dependency is not registered: {dependency}",
                BridgeFailure.INVALID_REQUEST,
            )
        library = _parse_agda_lib(manifest, budget)
        resolved[dependency] = library
        queue.extend(library.dependencies)
    return tuple(sorted(resolved.values(), key=lambda item: item.name))


def _within(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def _nearest_project_manifest(source: Path) -> tuple[Path | None, Path]:
    for parent in (source.parent, *source.parents):
        manifests = sorted(parent.glob("*.agda-lib"))
        if len(manifests) > 1:
            raise _error(
                "multiple-project-libraries",
                f"multiple .agda-lib files found in {parent}",
                BridgeFailure.INVALID_REQUEST,
            )
        if manifests:
            return manifests[0].resolve(), parent.resolve()
        if (parent / ".git").exists():
            return None, parent.resolve()
    return None, source.parent.resolve()


def _module_name(source: Path, text: str) -> str:
    match = _MODULE.search(mask_agda_source(text, source))
    if match is None:
        raise _error(
            "module-declaration-missing",
            f"source does not contain a top-level module declaration: {source}",
            BridgeFailure.INVALID_REQUEST,
        )
    return match.group(1)


def _declared_source_root(source: Path, module_name: str) -> Path:
    parts = module_name.split(".")
    if len(source.parents) < len(parts):
        return source.parent.resolve()
    root = source.parents[len(parts) - 1].resolve()
    expected = root.joinpath(*parts)
    candidates = tuple(
        Path(str(expected) + suffix).resolve() for suffix in AGDA_SOURCE_SUFFIXES
    )
    return root if source.resolve() in candidates else source.parent.resolve()


def _resolve_module(name: str, roots: tuple[Path, ...]) -> Path | None:
    matches: list[Path] = []
    for root in roots:
        for suffix in AGDA_SOURCE_SUFFIXES:
            candidate = root.joinpath(*name.split("."))
            if suffix == ".agda":
                candidate = candidate.with_suffix(".agda")
            else:
                candidate = Path(str(candidate) + suffix)
            if candidate.is_file():
                resolved = candidate.resolve()
                if not _within(resolved, root.resolve()):
                    raise _error(
                        "module-path-escape",
                        f"module {name!r} resolves outside its source root",
                        BridgeFailure.INVALID_REQUEST,
                    )
                matches.append(resolved)
    unique = tuple(dict.fromkeys(matches))
    if len(unique) > 1:
        raise _error(
            "ambiguous-module",
            f"module {name!r} resolves to multiple source files",
            BridgeFailure.INVALID_REQUEST,
        )
    return unique[0] if unique else None


def _interface_hash(source: Path, budget: BridgeBudget) -> str | None:
    interface = agda_interface_path(source)
    return (
        file_sha256(interface, deadline=budget.deadline)
        if interface.is_file()
        else None
    )


def _resolve_sources(
    root_source: Path,
    roots: tuple[Path, ...],
    budget: BridgeBudget,
) -> tuple[SourceIdentity, ...]:
    queue = [root_source]
    found: dict[Path, SourceIdentity] = {}
    names: dict[str, Path] = {}
    while queue:
        if time.monotonic() >= budget.deadline:
            raise _error(
                "project-resolution-timeout",
                "source graph resolution exceeded its wall-time budget",
                BridgeFailure.TIMEOUT,
            )
        path = queue.pop().resolve()
        if path in found:
            continue
        if len(found) >= budget.artifact_count:
            raise _error(
                "project-artifact-count-exhausted",
                "resolved source graph exceeded its artifact-count budget",
                BridgeFailure.RESOURCE_EXHAUSTED,
            )
        text = path.read_text()
        code = mask_agda_source(text, path)
        name = _module_name(path, text)
        previous = names.get(name)
        if previous is not None and previous != path:
            raise _error(
                "conflicting-module-declaration",
                f"module {name!r} is declared by both {previous} and {path}",
                BridgeFailure.INVALID_REQUEST,
            )
        names[name] = path
        source_root = next((root for root in roots if _within(path, root)), None)
        if source_root is None:
            raise _error(
                "source-root-escape",
                f"source file is outside every resolved source root: {path}",
                BridgeFailure.INVALID_REQUEST,
            )
        relative = path.relative_to(source_root).as_posix()
        imports = tuple(sorted(set(_IMPORT.findall(code))))
        found[path] = SourceIdentity(
            module=ModuleId(name, relative),
            path=path,
            sha256=file_sha256(path, deadline=budget.deadline),
            imports=imports,
            interface_sha256=_interface_hash(path, budget),
        )
        for imported in imports:
            imported_source = _resolve_module(imported, roots)
            if imported_source is not None:
                queue.append(imported_source)
            elif not _is_toolchain_module(imported):
                raise _error(
                    "import-not-resolved",
                    f"could not resolve imported module {imported!r}",
                    BridgeFailure.INVALID_REQUEST,
                )
    return tuple(sorted(found.values(), key=lambda item: item.module.name))


def _module_options(text: str, source: Path) -> tuple[str, ...]:
    options: list[str] = []
    for body in _OPTIONS.findall(mask_agda_source(text, source)):
        try:
            options.extend(shlex.split(body))
        except ValueError as error:
            raise _error(
                "malformed-options-pragma",
                f"cannot parse OPTIONS pragma: {error}",
                BridgeFailure.INVALID_REQUEST,
            ) from error
    return tuple(options)


def _validate_options(options: Iterable[str]) -> tuple[str, ...]:
    result = tuple(options)
    for option in result:
        if (
            not option.startswith("-")
            or "\x00" in option
            or len(option.encode()) > 4096
        ):
            raise _error(
                "invalid-agda-option",
                f"invalid Agda option in resolved project: {option!r}",
                BridgeFailure.INVALID_REQUEST,
            )
        if option.startswith(("--include-path", "-i", "--library-file")):
            raise _error(
                "path-option-not-resolved",
                f"path-bearing option must be represented by project resolution: {option}",
                BridgeFailure.INVALID_REQUEST,
            )
    return result


def _resolve_project(
    request: OpenProjectRequest, budget: BridgeBudget
) -> tuple[ResolvedProject, OpenProjectResult]:
    source = request.source_file.resolve()
    if not source.is_file() or not is_agda_source_path(source):
        raise _error(
            "source-file-missing",
            f"source must be an existing Agda file: {source}",
            BridgeFailure.INVALID_REQUEST,
        )
    manifest, discovered_root = _nearest_project_manifest(source)
    project_root = (
        request.project_root.resolve() if request.project_root else discovered_root
    )
    if not project_root.is_dir() or not _within(source, project_root):
        raise _error(
            "project-root-mismatch",
            "source file must be contained in the resolved project root",
            BridgeFailure.INVALID_REQUEST,
        )
    if manifest is not None and not _within(manifest, project_root):
        raise _error(
            "library-manifest-escape",
            "project library manifest is outside the selected project root",
            BridgeFailure.INVALID_REQUEST,
        )
    toolchain = detect_toolchain(request.executable, budget)
    adapter = adapter_for_version(toolchain.version)
    libraries = _resolve_libraries(manifest, request.library_file, budget)
    root_name = _module_name(source, source.read_text())
    declared_root = _declared_source_root(source, root_name)
    local_roots = tuple(dict.fromkeys((declared_root, project_root)))
    library_roots = tuple(
        root for library in libraries for root in library.include_roots
    )
    source_roots = tuple(dict.fromkeys((*local_roots, *library_roots)))
    sources = _resolve_sources(source, source_roots, budget)
    root_matches = tuple(item for item in sources if item.path == source)
    if len(root_matches) != 1:
        raise _error(
            "root-source-resolution-invariant",
            "resolved project must contain its root source exactly once",
            BridgeFailure.INTERNAL_INVARIANT,
        )
    root_identity = root_matches[0]
    if root_identity.module.name != root_name:
        raise _error(
            "root-module-resolution-invariant",
            "root module identity changed during project resolution",
            BridgeFailure.INTERNAL_INVARIANT,
        )
    options = _validate_options(
        dict.fromkeys((*request.options, *_module_options(source.read_text(), source)))
    )
    source_payload = {
        "sources": [item.semantic_dict() for item in sources],
        "options": list(options),
    }
    revision = SourceRevision(stable_hash(source_payload))
    environment_payload = {
        "toolchain": toolchain.semantic_dict(),
        "options": list(options),
        "libraries": [item.semantic_dict(project_root) for item in libraries],
        "source_revision": revision.value,
        "platform_semantics": {
            "system": platform.system(),
            "machine": platform.machine(),
            "path_case_sensitive": os.path.normcase("A") != os.path.normcase("a"),
        },
        "adapter": adapter.name,
        "interface_policy": "identity-recorded-ignore-for-speculation",
    }
    environment_id = EnvironmentId(stable_hash(environment_payload))
    nonce = hashlib.sha256(
        f"{environment_id.value}:{time.monotonic_ns()}".encode()
    ).hexdigest()[:32]
    handle = ProjectHandle(environment_id, nonce)
    capabilities = adapter.capabilities()
    resolved = ResolvedProject(
        project_root=project_root,
        source_roots=source_roots,
        root_module=root_identity.module,
        root_source=source,
        toolchain=toolchain,
        options=options,
        libraries=libraries,
        sources=sources,
        environment_id=environment_id,
        source_revision=revision,
        capabilities=capabilities,
        handle=handle,
    )
    result = OpenProjectResult(
        project=handle,
        environment_id=environment_id,
        source_revision=revision,
        root_module=root_identity.module,
        capabilities=capabilities,
        source_count=len(sources),
        module_graph=resolved.module_graph,
        diagnostics=(),
        cost=BridgeCost(),
    )
    return resolved, result


def resolve_project(
    request: OpenProjectRequest, budget: BridgeBudget
) -> tuple[ResolvedProject, OpenProjectResult]:
    """Resolve a project while keeping filesystem failures inside the algebra."""

    try:
        return _resolve_project(request, budget)
    except BridgeError:
        raise
    except TimeoutError as error:
        raise _error(
            "project-resolution-timeout",
            str(error),
            BridgeFailure.TIMEOUT,
        ) from error
    except (OSError, UnicodeError) as error:
        raise _error(
            "project-source-read-failed",
            f"could not read the resolved project: {error}",
            BridgeFailure.INVALID_REQUEST,
        ) from error


def write_source_overlay(
    source_file: Path, candidate: str, overlay_root: Path
) -> tuple[Path, tuple[tuple[Path, Path], ...]]:
    """Compatibility materializer for provisional P0 source-state search.

    Final acceptance uses :mod:`agdaprover.bridge.validator`; this helper only
    creates an isolated source/import closure for speculative interaction loads.
    """

    source = source_file.resolve()
    module_name = _module_name(source, candidate)
    root = _declared_source_root(source, module_name)
    roots = (root,)
    queue: list[tuple[Path, str | None]] = [(source, candidate)]
    found: dict[Path, tuple[str, str]] = {}
    while queue:
        checkpoint()
        path, override = queue.pop()
        resolved = path.resolve()
        if resolved in found:
            continue
        text = override if override is not None else resolved.read_text()
        if override is None:
            charge_io(len(text.encode()))
        name = _module_name(resolved, text)
        found[resolved] = (name, text)
        for imported in sorted(set(_IMPORT.findall(mask_agda_source(text, resolved)))):
            imported_path = _resolve_module(imported, roots)
            if imported_path is not None:
                queue.append((imported_path, None))
            elif not _is_toolchain_module(imported):
                raise ValueError(f"project overlay cannot resolve module {imported!r}")
    written: list[tuple[Path, Path]] = []
    candidate_path: Path | None = None
    for original, (name, text) in sorted(found.items(), key=lambda item: str(item[0])):
        suffix = agda_source_suffix(original)
        if suffix is None:
            raise RuntimeError("project overlay contains a non-Agda source")
        destination = overlay_root / Path(str(Path(*name.split("."))) + suffix)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text)
        charge_io(len(text.encode()))
        checkpoint()
        written.append((original, destination))
        if original == source:
            candidate_path = destination
    if candidate_path is None:
        raise RuntimeError("project overlay omitted its root source")
    return candidate_path, tuple(written)
