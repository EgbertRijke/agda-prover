"""Supervised resident native operations; no Python symbolic decisions.

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
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from pathlib import Path
from typing import Any

from ..resource_budget import ResourceLimitError, charge_io
from ..verifier_budget import charge_verifier_request
from .contracts import BridgeBudget
from .overlay import materialize_project
from .process_io import write_process_input
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
    focused_model_path: Path | None = None,
    focused_search: bool = True,
    native_path: Path | None,
    cancellation: CancellationToken,
    publish: Callable[[dict[str, Any]], None],
) -> dict[str, Any]:
    if work_units is not None and (type(work_units) is not int or work_units <= 0):
        raise ValueError("work_units must be positive or None")
    if ranker not in {"nnue", "symbolic"}:
        raise ValueError("unknown native ranker")
    if type(focused_search) is not bool:
        raise ValueError("focused_search must be a boolean")
    with resident_session(executable, project, budget, cancellation) as connection:
        reply = connection.request(
            "solve-evidence",
            {
                "state": connection.root_state,
                "goal_id": goal_id,
                "limits": {"work_units": work_units},
                "ranker": ranker,
                "model_path": str(model_path.resolve()) if model_path else None,
                "focused_model_path": str(focused_model_path.resolve())
                if focused_model_path
                else None,
                "focused_search": focused_search,
                "native_path": str(native_path.resolve()) if native_path else None,
                "exclude_names": [],
            },
            publish,
        )
        outcome = reply["outcome"]
        if outcome.get("status") == "candidate" and outcome.get("candidate"):
            exported = connection.request(
                "export-goals",
                {
                    "state": connection.root_state,
                    "goal_ids": [goal_id],
                    "descendant": outcome["candidate"]["state"],
                },
                publish,
            )
            reply = {
                **reply,
                "source_export": exported["outcome"],
                "cost": exported["cost"],
            }
        return reply


@contextmanager
def resident_session(
    executable: Path,
    project: ResolvedProject,
    budget: BridgeBudget,
    cancellation: CancellationToken,
) -> Iterator[SymbolicConnection]:
    """One immutable overlay and physical supervisor for all run slices.

    This is transport, not a search policy or verification authority. Multiple
    requests never restart the wall/output/resource envelope.
    """
    if project.libraries:
        raise ValueError("native library-manifest routing is pending H8")
    with tempfile.TemporaryDirectory(prefix="agdaprover-symbolic-") as directory:
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
            with SymbolicConnection(
                arguments, root, budget, cancellation
            ) as connection:
                yield connection
        finally:
            lease.close()


class SymbolicConnection:
    """Single-request-at-a-time framed connection to one supervised owner."""

    def __init__(
        self,
        arguments: list[str],
        root: Path,
        budget: BridgeBudget,
        cancellation: CancellationToken,
    ) -> None:
        self.budget = budget
        self.supervisor = ResourceSupervisor(budget, cancellation)
        charge_verifier_request("interaction")  # Resident checker startup/load.
        self.process = OwnedProcess(
            arguments,
            cwd=root,
            env=isolated_process_environment(root),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            start_new_session=True,
        )
        assert self.process.stdin and self.process.stdout and self.process.stderr
        self.chunks: queue.Queue[tuple[str, bytes]] = queue.Queue(maxsize=16)
        self.stop = threading.Event()
        self.buffer = bytearray()
        self.diagnostics = bytearray()
        self.total = 0
        self.serial = 0
        self.root_state: dict[str, Any] = {}
        self.lock = threading.Lock()
        self.closed = False
        self.readers = [
            threading.Thread(
                target=self._read_stream, args=(label, pipe.fileno()), daemon=True
            )
            for label, pipe in (
                ("out", self.process.stdout),
                ("err", self.process.stderr),
            )
        ]
        for reader in self.readers:
            reader.start()

    def __enter__(self) -> SymbolicConnection:
        try:
            event = self._receive()
            if event.get("event") != "session-start" or not isinstance(
                event.get("state"), dict
            ):
                raise SymbolicProtocolError("native owner did not supply a root state")
            self.root_state = event["state"]
            return self
        except BaseException:
            self.close()
            raise

    def __exit__(self, *_exc: object) -> None:
        self.close()

    def _read_stream(self, label: str, descriptor: int) -> None:
        while not self.stop.is_set():
            try:
                data = os.read(descriptor, 65536)
            except OSError:
                data = b""
            while not self.stop.is_set():
                try:
                    self.chunks.put((label, data), timeout=0.1)
                    break
                except queue.Full:
                    pass
            if not data:
                return

    def _receive(self) -> dict[str, Any]:
        while True:
            self.supervisor.check(self.process, command_id=None)
            if b"\n" in self.buffer:
                line, _, remainder = self.buffer.partition(b"\n")
                self.buffer = bytearray(remainder)
                try:
                    value = json.loads(line)
                except (ValueError, UnicodeError) as error:
                    raise SymbolicProtocolError(
                        "malformed native session JSON"
                    ) from error
                if (
                    not isinstance(value, dict)
                    or value.get("schema_version")
                    != "agdaprover.symbolic-session-event.v1"
                ):
                    raise SymbolicProtocolError("invalid native session envelope")
                return value
            try:
                label, data = self.chunks.get(timeout=0.05)
            except queue.Empty:
                continue
            if not data:
                if label == "out":
                    raise SymbolicProtocolError(
                        "native session ended without result: "
                        + self.diagnostics.decode(errors="replace")
                    )
                continue
            self.total += len(data)
            charge_io(len(data))
            if self.total > self.budget.output_bytes:
                raise ResourceLimitError("native session output allowance exhausted")
            if label == "err":
                self.diagnostics.extend(data)
                del self.diagnostics[:-8192]
                continue
            self.buffer.extend(data)

    def request(
        self,
        operation: str,
        fields: dict[str, Any],
        publish: Callable[[dict[str, Any]], None],
    ) -> dict[str, Any]:
        if self.closed:
            raise SymbolicProtocolError("native connection is closed")
        if not self.lock.acquire(blocking=False):
            raise SymbolicProtocolError("another native request is active")
        try:
            if {"schema_version", "request_id", "operation"} & fields.keys():
                raise ValueError("native request fields override its envelope")
            number = self.serial
            self.serial += 1
            request = {
                **fields,
                "schema_version": "agdaprover.symbolic-session-request.v1",
                "request_id": number,
                "operation": operation,
            }
            encoded = json.dumps(request).encode() + b"\n"
            charge_verifier_request("interaction")
            write_process_input(self.process, encoded, self.supervisor)
            started = False
            while True:
                value = self._receive()
                event = value.get("event")
                if (
                    event
                    in {
                        "search-policy",
                        "search-progress",
                        "operation-start",
                        "operation-result",
                        "control-result",
                    }
                    and type(value.get("request_id")) is int
                    and value.get("request_id") == number
                ):
                    if event == "operation-start":
                        if started:
                            raise SymbolicProtocolError(
                                "duplicate native dispatch receipt"
                            )
                        started = True
                    elif event != "control-result" and not started:
                        raise SymbolicProtocolError(
                            "native work arrived before dispatch receipt"
                        )
                    if event in {
                        "operation-result",
                        "control-result",
                    } and not isinstance(value.get("outcome"), dict):
                        raise SymbolicProtocolError("invalid native operation result")
                    publish(value)
                    if event in {"operation-result", "control-result"}:
                        return value
                else:
                    raise SymbolicProtocolError(
                        f"unexpected native session event: {value}"
                    )
        except BaseException:
            # A partly sent/consumed frame cannot be reused as though this were
            # a clean request boundary. The caller retains published receipts.
            self.close()
            raise
        finally:
            self.lock.release()

    def close(self) -> None:
        if self.closed:
            return
        self.closed = True
        self.stop.set()
        try:
            self.supervisor.terminate_process_tree(self.process)
        finally:
            for reader in self.readers:
                reader.join(timeout=1)
            for pipe in (self.process.stdin, self.process.stdout, self.process.stderr):
                if pipe is not None:
                    pipe.close()
            self.supervisor.release(self.process)
