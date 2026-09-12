"""Single-owner, bounded byte transport for Agda interaction JSON."""

from __future__ import annotations

import os
import secrets
import select
import subprocess
import threading
import time
from pathlib import Path

from ..resource_budget import ResourceLimitError, charge_io
from ..verifier_budget import charge_verifier_request
from .contracts import (
    BridgeBudget,
    BridgeCost,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    BridgeResourceSummary,
    CommandId,
    DiagnosticPhase,
)
from .overlay import library_arguments
from .process_io import write_process_input
from .resources import (
    CancellationToken,
    OwnedProcess,
    ProcessUsage,
    ResourceSupervisor,
    isolated_process_environment,
)
from .versions.agda_2_8 import PROMPT, Agda28Adapter, DecodedResponse


class AgdaJsonTransport:
    def __init__(
        self,
        executable: Path,
        adapter: Agda28Adapter,
        budget: BridgeBudget,
        *,
        cancellation: CancellationToken | None = None,
        runtime_root: Path | None = None,
        transactional_commands: bool = False,
        library_file: Path | None = None,
    ) -> None:
        self.executable = executable
        self.adapter = adapter
        self.budget = budget
        self.cancellation = cancellation or CancellationToken()
        self.runtime_root = runtime_root
        self.transactional_commands = transactional_commands
        self.library_file = library_file
        self.supervisor = ResourceSupervisor(budget, self.cancellation)
        self.cost = BridgeCost()
        self.process_generation = 0
        self._process: subprocess.Popen[bytes] | None = None
        self._buffer = bytearray()
        self._lock = threading.Lock()
        self._session_nonce = secrets.token_hex(8)
        self._sequence = 0
        self._active_command: CommandId | None = None
        self._closed = False
        self._orphan_processes = 0

    @property
    def active_command(self) -> CommandId | None:
        return self._active_command

    @property
    def is_open(self) -> bool:
        return self._process is not None and self._process.poll() is None

    def current_usage(self) -> ProcessUsage:
        process = self._process
        if process is None or process.poll() is not None:
            return ProcessUsage(0, 0.0, 0)
        return self.supervisor.sample(process)

    def check_resources(self) -> None:
        """Enforce the same envelope for an observation without a kernel command."""
        process = self._process
        if process is None or process.poll() is not None:
            raise self._error(
                BridgeFailure.STALE_TOKEN,
                "cached-read-process-ended",
                "cannot reuse an observation after the Agda process has ended",
            )
        self.supervisor.check(process, command_id=None)
        self.cost.peak_rss_bytes = max(
            self.cost.peak_rss_bytes, self.supervisor.peak_rss_bytes
        )

    @property
    def buffered_bytes(self) -> int:
        return len(self._buffer)

    def open(self) -> None:
        if self._closed:
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "transport-closed",
                "cannot reopen a closed transport",
            )
        if self.is_open:
            return
        self.cancellation.raise_if_cancelled()
        try:
            process = OwnedProcess(
                [
                    str(self.executable),
                    *library_arguments(self.library_file),
                    "--ignore-interfaces",
                    "--interaction-json",
                ],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                bufsize=0,
                cwd=self.runtime_root,
                env=(
                    isolated_process_environment(self.runtime_root)
                    if self.runtime_root is not None
                    else None
                ),
                start_new_session=True,
            )
        except OSError as error:
            raise self._error(
                BridgeFailure.CHILD_PROCESS_FAILURE,
                "agda-process-start-failed",
                f"could not start Agda interaction process: {error}",
            ) from error
        self._process = process
        self.process_generation += 1
        self.cost.add(
            process_starts=1,
            process_restarts=int(self.process_generation > 1),
        )
        try:
            startup = self._read_until_prompt(None)
            # Startup output is not an operation response, but still consumes bytes.
            if startup.strip():
                self.adapter.decode(startup, event_limit=self.budget.event_count)
        except BaseException:
            self._poison()
            raise

    def command(
        self,
        source_file: Path,
        command: str,
        *,
        transactional: bool = False,
    ) -> tuple[CommandId, DecodedResponse]:
        if not self._lock.acquire(blocking=False):
            raise self._error(
                BridgeFailure.INVALID_REQUEST,
                "concurrent-command-rejected",
                "one bridge session accepts only one command in flight",
            )
        started = time.monotonic()
        try:
            self.open()
            process = self._process
            if process is None or process.stdin is None:
                raise self._error(
                    BridgeFailure.INTERNAL_INVARIANT,
                    "transport-process-missing",
                    "open transport has no writable child process",
                )
            self._sequence += 1
            command_id = CommandId(self._session_nonce, self._sequence)
            self._active_command = command_id
            if transactional and not self.transactional_commands:
                raise self._error(
                    BridgeFailure.UNSUPPORTED_CAPABILITY,
                    "transactional-command-unavailable",
                    "the selected Agda frontend does not support local transactions",
                )
            wire = self.adapter.command_wire(
                source_file,
                command,
                highlighting_method="Indirect" if transactional else "Direct",
            )
            if len(wire) > self.budget.output_bytes:
                raise self._error(
                    BridgeFailure.RESOURCE_EXHAUSTED,
                    "bridge-command-too-large",
                    "serialized Agda command exceeds the output-byte budget",
                    command_id,
                )
            self.cancellation.raise_if_cancelled(command_id)
            charge_verifier_request("interaction")
            try:
                written = self._write_all(process, wire, command_id)
            except BridgeError:
                self._poison()
                raise
            except (BrokenPipeError, OSError) as error:
                self._poison()
                raise self._error(
                    BridgeFailure.CHILD_PROCESS_FAILURE,
                    "agda-broken-pipe",
                    f"Agda interaction input failed: {error}",
                    command_id,
                ) from error
            if written != len(wire):
                self._poison()
                raise self._error(
                    BridgeFailure.INTERNAL_INVARIANT,
                    "partial-command-write-invariant",
                    "bounded transport returned after a partial command write",
                    command_id,
                )
            self.cost.add(commands=1)
            try:
                raw = self._read_until_prompt(command_id)
                response = self.adapter.decode(raw, event_limit=self.budget.event_count)
            except ValueError as error:
                self._poison()
                raise self._error(
                    BridgeFailure.PROTOCOL_FAILURE,
                    "malformed-agda-response",
                    str(error),
                    command_id,
                ) from error
            except BridgeError:
                self._poison()
                raise
            self.cost.add(events_decoded=len(response.events))
            # The read loop already samples at most every 100 ms.  Forcing a
            # second sample here would spawn one `ps` process per fast command
            # on platforms without /proc, dominating candidate-check latency.
            self.supervisor.check(process, command_id=command_id)
            self.cost.peak_rss_bytes = max(
                self.cost.peak_rss_bytes, self.supervisor.peak_rss_bytes
            )
            return command_id, response
        except ResourceLimitError:
            # A shared quota may interrupt a partial write, read or final
            # sample. The child's protocol state is no longer reusable.
            self._poison()
            raise
        finally:
            self.cost.add(elapsed_ms=(time.monotonic() - started) * 1000.0)
            self._active_command = None
            self._lock.release()

    def cancel(self, command_id: CommandId) -> bool:
        active = self._active_command
        if active is None or active != command_id:
            return False
        self.cancellation.cancel()
        self.cost.add(cancellations=1)
        return True

    def _write_all(
        self,
        process: subprocess.Popen[bytes],
        wire: bytes,
        command_id: CommandId,
    ) -> int:
        return write_process_input(
            process,
            wire,
            self.supervisor,
            command_id=command_id,
            wrote=lambda amount: self.cost.add(bytes_written=amount),
        )

    def _prompt_position(self) -> int:
        if self._buffer.startswith(PROMPT):
            return 0
        marker = self._buffer.find(b"\n" + PROMPT)
        return marker + 1 if marker >= 0 else -1

    def _read_until_prompt(self, command_id: CommandId | None) -> bytes:
        process = self._process
        if process is None or process.stdout is None:
            raise self._error(
                BridgeFailure.INTERNAL_INVARIANT,
                "transport-output-missing",
                "open transport has no readable child process",
                command_id,
            )
        while True:
            prompt_at = self._prompt_position()
            if prompt_at >= 0:
                response = bytes(self._buffer[:prompt_at])
                del self._buffer[: prompt_at + len(PROMPT)]
                return response
            try:
                self.supervisor.check(process, command_id=command_id)
            except BridgeError:
                raise
            remaining = self.budget.deadline - time.monotonic()
            if remaining <= 0:
                raise self._error(
                    BridgeFailure.TIMEOUT,
                    "agda-response-timeout",
                    "timed out waiting for the Agda interaction prompt",
                    command_id,
                )
            ready, _, _ = select.select(
                [process.stdout.fileno()], [], [], min(0.05, remaining)
            )
            if not ready:
                continue
            try:
                chunk = os.read(process.stdout.fileno(), 65_536)
            except OSError as error:
                raise self._error(
                    BridgeFailure.CHILD_PROCESS_FAILURE,
                    "agda-output-read-failed",
                    f"could not read Agda interaction output: {error}",
                    command_id,
                ) from error
            if not chunk:
                return_code = process.poll()
                raise self._error(
                    BridgeFailure.CHILD_PROCESS_FAILURE,
                    "agda-process-exited",
                    f"Agda interaction process exited before a prompt: {return_code}",
                    command_id,
                )
            self._buffer.extend(chunk)
            self.cost.add(bytes_read=len(chunk))
            charge_io(len(chunk))
            if len(self._buffer) > self.budget.output_bytes:
                raise self._error(
                    BridgeFailure.RESOURCE_EXHAUSTED,
                    "agda-response-too-large",
                    "Agda response exceeded the configured byte limit",
                    command_id,
                )

    def _poison(self) -> None:
        process = self._process
        self._process = None
        self._buffer.clear()
        if process is None:
            return
        self._orphan_processes += ResourceSupervisor.terminate_process_tree(process)
        if process.stdout is not None:
            process.stdout.close()
        self.supervisor.release(process)

    def set_library_file(self, library_file: Path | None) -> None:
        """A relocated environment must not reuse startup library state."""
        if self.library_file != library_file:
            self._poison()
            self.library_file = library_file

    def close(self) -> BridgeResourceSummary:
        started = time.monotonic()
        self._closed = True
        self._poison()
        return BridgeResourceSummary(
            process_generation=self.process_generation,
            commands=self.cost.commands,
            process_starts=self.cost.process_starts,
            process_restarts=self.cost.process_restarts,
            cancellations=self.cost.cancellations,
            bytes_read=self.cost.bytes_read,
            bytes_written=self.cost.bytes_written,
            peak_rss_bytes=max(
                self.cost.peak_rss_bytes, self.supervisor.peak_rss_bytes
            ),
            overlays_removed=0,
            orphan_processes=self._orphan_processes,
            close_elapsed_ms=(time.monotonic() - started) * 1000.0,
        )

    @staticmethod
    def _error(
        failure: BridgeFailure,
        code: str,
        message: str,
        command_id: CommandId | None = None,
    ) -> BridgeError:
        phase = (
            DiagnosticPhase.RESOURCE
            if failure
            in {
                BridgeFailure.TIMEOUT,
                BridgeFailure.CANCELLED,
                BridgeFailure.RESOURCE_EXHAUSTED,
            }
            else (
                DiagnosticPhase.INTERNAL
                if failure == BridgeFailure.INTERNAL_INVARIANT
                else DiagnosticPhase.PROTOCOL
            )
        )
        return BridgeError(
            failure,
            BridgeDiagnostic(
                code=code,
                phase=phase,
                severity="error",
                message=message,
                retryable=failure
                in {
                    BridgeFailure.TIMEOUT,
                    BridgeFailure.CANCELLED,
                    BridgeFailure.CHILD_PROCESS_FAILURE,
                },
            ),
            command_id=command_id,
        )
