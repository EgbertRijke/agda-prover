"""Coarse native evidence operation; no Python per-candidate semantic calls.

Project resolution, immutable overlays and resource supervision are shared with
the existing bridge. This transport is explicitly selected until H11; it never
silently falls back to another engine on rejection or exhaustion.
"""

from __future__ import annotations

import json
import os
import queue
import subprocess
import tempfile
import threading
from collections.abc import Callable
from pathlib import Path
from typing import Any

from ..resource_budget import ResourceLimitError, charge_io
from ..verifier_budget import charge_verifier_request
from .contracts import BridgeBudget
from .overlay import materialize_project
from .project import ResolvedProject
from .resources import (
    CancellationToken,
    OwnedProcess,
    ResourceSupervisor,
    isolated_process_environment,
    temporary_storage,
)


class SymbolicProtocolError(RuntimeError):
    """Native failure or malformed response, never an unsolved mathematical fact."""


def search_evidence(
    executable: Path,
    project: ResolvedProject,
    goal_id: int,
    *,
    budget: BridgeBudget,
    work_units: int | None,
    ranker: str,
    model_path: Path | None,
    native_path: Path | None,
    cancellation: CancellationToken,
    publish: Callable[[dict[str, Any]], None],
) -> dict[str, Any]:
    if project.libraries:
        raise ValueError("native evidence library-manifest routing is pending H8")
    if work_units is not None and (type(work_units) is not int or work_units <= 0):
        raise ValueError("work_units must be positive or None")
    if ranker not in {"nnue", "symbolic"}:
        raise ValueError("unknown native ranker")
    with tempfile.TemporaryDirectory(prefix="agdaprover-evidence-") as directory:
        root = Path(directory)
        overlay = materialize_project(project, root, budget, cancellation)
        lease = temporary_storage(root)
        try:
            lease.sample(force=True)
            arguments = [
                str(executable.resolve()),
                "session",
                str(overlay.source_for(project.root_module)),
                *map(str, overlay.include_roots),
                "--",
                *project.command_options,
            ]
            request = {
                "schema_version": "agdaprover.symbolic-session-request.v1",
                "request_id": 0,
                "operation": "solve-evidence",
                "goal_id": goal_id,
                "limits": {"work_units": work_units},
                "ranker": ranker,
                "model_path": str(model_path.resolve()) if model_path else None,
                "native_path": str(native_path.resolve()) if native_path else None,
                "exclude_names": [],
            }
            return _exchange(arguments, root, request, budget, cancellation, publish)
        finally:
            lease.close()


def _exchange(
    arguments: list[str],
    root: Path,
    request: dict[str, Any],
    budget: BridgeBudget,
    cancellation: CancellationToken,
    publish: Callable[[dict[str, Any]], None],
) -> dict[str, Any]:
    supervisor = ResourceSupervisor(budget, cancellation)
    charge_verifier_request("interaction")  # Resident checker startup/load.
    process = OwnedProcess(
        arguments,
        cwd=root,
        env=isolated_process_environment(root),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        bufsize=0,
        start_new_session=True,
    )
    assert (
        process.stdin is not None
        and process.stdout is not None
        and process.stderr is not None
    )
    chunks: queue.Queue[tuple[str, bytes]] = queue.Queue(maxsize=16)
    stop = threading.Event()

    def read_stream(label: str, descriptor: int) -> None:
        while not stop.is_set():
            try:
                data = os.read(descriptor, 65536)
            except OSError:
                data = b""
            while not stop.is_set():
                try:
                    chunks.put((label, data), timeout=0.1)
                    break
                except queue.Full:
                    pass
            if not data:
                return

    readers = [
        threading.Thread(target=read_stream, args=(label, pipe.fileno()), daemon=True)
        for label, pipe in (("out", process.stdout), ("err", process.stderr))
    ]
    for reader in readers:
        reader.start()
    buffer = bytearray()
    diagnostics = bytearray()
    total = 0
    dispatched = False
    try:
        while True:
            supervisor.check(process, command_id=None)
            try:
                label, data = chunks.get(timeout=0.05)
            except queue.Empty:
                continue
            if not data:
                if label == "out":
                    raise SymbolicProtocolError(
                        "native session ended without result: "
                        + diagnostics.decode(errors="replace")
                    )
                continue
            total += len(data)
            charge_io(len(data))
            if total > budget.output_bytes:
                raise ResourceLimitError("native session output allowance exhausted")
            if label == "err":
                diagnostics.extend(data)
                del diagnostics[:-8192]
                continue
            buffer.extend(data)
            while b"\n" in buffer:
                line, _, remainder = buffer.partition(b"\n")
                buffer = bytearray(remainder)
                value = json.loads(line)
                if (
                    not isinstance(value, dict)
                    or value.get("schema_version")
                    != "agdaprover.symbolic-session-event.v1"
                ):
                    raise SymbolicProtocolError("invalid native session envelope")
                event = value.get("event")
                if event == "session-start" and not dispatched:
                    request["state"] = value["state"]
                    encoded = json.dumps(request).encode() + b"\n"
                    charge_io(len(encoded))
                    charge_verifier_request("interaction")  # One coarse request.
                    process.stdin.write(encoded)
                    process.stdin.flush()
                    dispatched = True
                elif (
                    event in {"search-policy", "operation-start", "operation-result"}
                    and dispatched
                    and value.get("request_id") == 0
                ):
                    publish(value)
                    if event == "operation-result":
                        return value
                else:
                    raise SymbolicProtocolError(
                        f"unexpected native session event: {value}"
                    )
    finally:
        stop.set()
        try:
            supervisor.terminate_process_tree(process)
        finally:
            for reader in readers:
                reader.join(timeout=1)
            process.stdout.close()
            process.stderr.close()
            supervisor.release(process)
