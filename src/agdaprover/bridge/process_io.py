"""Shared cancellable pipe writes for supervised Agda processes."""

from __future__ import annotations

import os
import select
import subprocess
from collections.abc import Callable

from ..resource_budget import charge_io
from .contracts import CommandId
from .resources import ResourceSupervisor


def write_process_input(
    process: subprocess.Popen[bytes],
    wire: bytes,
    supervisor: ResourceSupervisor,
    *,
    command_id: CommandId | None = None,
    wrote: Callable[[int], None] | None = None,
) -> int:
    """Handle partial writes without hiding cancellation behind a full pipe."""
    if process.stdin is None:
        raise BrokenPipeError("Agda input pipe is closed")
    descriptor = process.stdin.fileno()
    previous = os.get_blocking(descriptor)
    os.set_blocking(descriptor, False)
    written = 0
    try:
        while written < len(wire):
            supervisor.check(process, command_id=command_id)
            _, ready, _ = select.select([], [descriptor], [], 0.05)
            if not ready:
                continue
            try:
                amount = os.write(descriptor, wire[written : written + 65_536])
            except BlockingIOError:
                continue
            if amount <= 0:
                raise BrokenPipeError("Agda input pipe accepted no bytes")
            written += amount
            if wrote is not None:
                wrote(amount)
            charge_io(amount)
    finally:
        # A concurrent owner shutdown may already have closed its pipe.
        if not process.stdin.closed:
            os.set_blocking(descriptor, previous)
    return written
