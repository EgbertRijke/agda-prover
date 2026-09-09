"""Cancellation and portable process-tree resource supervision."""

from __future__ import annotations

import ctypes
import functools
import os
import platform
import signal
import subprocess
import tempfile
import threading
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, cast
from weakref import WeakSet

from ..resource_budget import (
    ResourceExhausted,
    ResourceLimitError,
    StorageLease,
    checkpoint,
    current_ledgers,
)
from .contracts import (
    BridgeBudget,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    CommandId,
    DiagnosticPhase,
)


class CancellationToken:
    def __init__(self) -> None:
        self._event = threading.Event()

    def cancel(self) -> None:
        self._event.set()

    @property
    def cancelled(self) -> bool:
        return self._event.is_set()

    def raise_if_cancelled(self, command_id: CommandId | None = None) -> None:
        if self.cancelled:
            raise BridgeError(
                BridgeFailure.CANCELLED,
                BridgeDiagnostic(
                    code="command-cancelled",
                    phase=DiagnosticPhase.RESOURCE,
                    severity="error",
                    message="bridge command was cancelled",
                    retryable=True,
                ),
                command_id=command_id,
            )


@dataclass(frozen=True)
class ProcessUsage:
    rss_bytes: int
    cpu_seconds: float
    process_count: int


class OwnedProcess(subprocess.Popen[bytes]):
    """Retain final POSIX CPU usage, including children shorter than a sample.

    Popen still owns polling, waiting and return-code handling. Its POSIX wait
    hooks retain final usage on POSIX; other hosts retain sampled accounting.
    """

    final_cpu_seconds: float = 0.0

    def _internal_poll(
        self, _deadstate: int | None = None, **_kwargs: object
    ) -> int | None:
        if os.name != "posix":
            return cast(int | None, cast(Any, super())._internal_poll(_deadstate))
        # Popen.poll normally uses waitpid directly, bypassing _try_wait.
        # Both paths must reap through wait4 or short completed children would
        # disappear from accounting. The lock is Popen's own wait ownership.
        # The standard-library stubs deliberately omit these POSIX hooks.
        wait_state = cast(Any, self)
        if self.returncode is None and wait_state._waitpid_lock.acquire(False):
            try:
                if self.returncode is None:
                    pid, status = self._try_wait(os.WNOHANG)
                    if pid == self.pid:
                        wait_state._handle_exitstatus(status)
            finally:
                wait_state._waitpid_lock.release()
        return self.returncode

    def _try_wait(self, wait_flags: int) -> tuple[int, int]:
        try:
            pid, status, usage = os.wait4(self.pid, wait_flags)
        except ChildProcessError:
            return self.pid, 0
        if pid:
            self.final_cpu_seconds = usage.ru_utime + usage.ru_stime
        return pid, status


def current_process_rss() -> int:
    """Current host RSS, without including any unrelated process or child."""
    try:
        return _current_process_rss()
    except (OSError, ValueError, IndexError, RuntimeError) as error:
        raise ResourceLimitError(
            "current process resident-memory sampling unavailable"
        ) from error


def _current_process_rss() -> int:
    if Path("/proc/self/statm").exists():
        return int(Path("/proc/self/statm").read_text().split()[1]) * os.sysconf(
            "SC_PAGE_SIZE"
        )
    library = _darwin_libproc()
    if library is not None:
        task = _DarwinTaskInfo()
        if library.proc_pidinfo(
            os.getpid(), 4, 0, ctypes.byref(task), ctypes.sizeof(task)
        ) == ctypes.sizeof(task):
            return int(task.resident_size)
    raise RuntimeError("current process resident-memory sampling unavailable")


def isolated_process_environment(root: Path) -> dict[str, str]:
    """Create the minimal HOME/cache/temp environment used by Agda children."""

    environment: dict[str, str] = {}
    for name in ("PATH", "LANG", "LC_ALL", "SYSTEMROOT"):
        if name in os.environ:
            environment[name] = os.environ[name]
    home = root / ".home"
    cache = root / ".cache"
    temporary = root / ".tmp"
    agda_directory = home / ".agda"
    for directory in (home, cache, temporary, agda_directory):
        directory.mkdir(parents=True, exist_ok=True)
    environment.update(
        {
            "HOME": str(home),
            "XDG_CACHE_HOME": str(cache),
            "XDG_CONFIG_HOME": str(home / ".config"),
            "XDG_DATA_HOME": str(home / ".local/share"),
            "TMPDIR": str(temporary),
            "AGDA_DIR": str(agda_directory),
        }
    )
    return environment


def temporary_storage(root: Path) -> StorageLease:
    """Meter one exclusively owned temporary directory without following links."""

    def measure() -> int:
        total = 0
        pending = [root]
        while pending:
            directory = pending.pop()
            try:
                with os.scandir(directory) as entries:
                    for entry in entries:
                        try:
                            if entry.is_dir(follow_symlinks=False):
                                pending.append(Path(entry.path))
                            else:
                                total += entry.stat(follow_symlinks=False).st_size
                        except FileNotFoundError:
                            continue
            except FileNotFoundError:
                continue
        return total

    return StorageLease(measure)


@contextmanager
def temporary_workspace(*, prefix: str) -> Iterator[str]:
    """Own a scratch area and its shared-budget lease through exception cleanup."""
    with tempfile.TemporaryDirectory(prefix=prefix) as directory:
        with temporary_storage(Path(directory)):
            yield directory


def _parse_cpu_time(value: str) -> float:
    day_parts = value.strip().split("-")
    days = 0
    clock = day_parts[-1]
    if len(day_parts) == 2:
        days = int(day_parts[0])
    fields = [float(item) for item in clock.split(":")]
    if len(fields) == 3:
        hours, minutes, seconds = fields
    elif len(fields) == 2:
        hours, (minutes, seconds) = 0, fields
    else:
        hours, minutes, seconds = 0, 0, fields[0]
    return days * 86400 + hours * 3600 + minutes * 60 + seconds


def _linux_tree_usage(process_group: int) -> ProcessUsage | None:
    proc = Path("/proc")
    if not proc.is_dir():
        return None
    rss = 0
    cpu_ticks = 0
    count = 0
    ticks = os.sysconf("SC_CLK_TCK")
    page_size = os.sysconf("SC_PAGE_SIZE")
    for entry in proc.iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            # The parenthesized executable name can contain spaces or ')'.
            stat_fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            if int(stat_fields[2]) != process_group:
                continue
            cpu_ticks += sum(int(stat_fields[i]) for i in (11, 12, 13, 14))
            rss += int(stat_fields[21]) * page_size
            count += 1
        except (FileNotFoundError, PermissionError, IndexError, ValueError):
            continue
    return ProcessUsage(rss, cpu_ticks / ticks, count)


class _DarwinTaskInfo(ctypes.Structure):
    _fields_ = [
        ("virtual_size", ctypes.c_uint64),
        ("resident_size", ctypes.c_uint64),
        ("total_user", ctypes.c_uint64),
        ("total_system", ctypes.c_uint64),
        ("threads_user", ctypes.c_uint64),
        ("threads_system", ctypes.c_uint64),
        ("policy", ctypes.c_int32),
        ("faults", ctypes.c_int32),
        ("pageins", ctypes.c_int32),
        ("cow_faults", ctypes.c_int32),
        ("messages_sent", ctypes.c_int32),
        ("messages_received", ctypes.c_int32),
        ("syscalls_mach", ctypes.c_int32),
        ("syscalls_unix", ctypes.c_int32),
        ("context_switches", ctypes.c_int32),
        ("thread_count", ctypes.c_int32),
        ("running_thread_count", ctypes.c_int32),
        ("priority", ctypes.c_int32),
    ]


class _DarwinTimebaseInfo(ctypes.Structure):
    _fields_ = [("numer", ctypes.c_uint32), ("denom", ctypes.c_uint32)]


@functools.cache
def _darwin_seconds_per_tick() -> float | None:
    """libproc task CPU counters are Mach ticks, not necessarily nanoseconds.

    Apple uses ns_from_mach for PROC_PIDTASKINFO in XNU's
    tests/recount/recount_perf_tests.c. The ratio is not 1:1 on Apple Silicon.
    An unavailable timebase must fall back to another meter, not undercount.
    """
    if platform.system() != "Darwin":
        return None
    try:
        system = ctypes.CDLL("/usr/lib/libSystem.B.dylib")
        system.mach_timebase_info.argtypes = [ctypes.POINTER(_DarwinTimebaseInfo)]
        system.mach_timebase_info.restype = ctypes.c_int
        timebase = _DarwinTimebaseInfo()
        if system.mach_timebase_info(ctypes.byref(timebase)) != 0:
            return None
    except (OSError, AttributeError):
        return None
    if not timebase.numer or not timebase.denom:
        return None
    return timebase.numer / timebase.denom / 1_000_000_000


@functools.cache
def _darwin_libproc() -> ctypes.CDLL | None:
    if platform.system() != "Darwin":
        return None
    try:
        library = ctypes.CDLL("/usr/lib/libproc.dylib")
    except OSError:
        return None
    library.proc_listpids.argtypes = [
        ctypes.c_uint32,
        ctypes.c_uint32,
        ctypes.c_void_p,
        ctypes.c_int,
    ]
    library.proc_listpids.restype = ctypes.c_int
    library.proc_pidinfo.argtypes = [
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_uint64,
        ctypes.c_void_p,
        ctypes.c_int,
    ]
    library.proc_pidinfo.restype = ctypes.c_int
    return library


def _darwin_tree_usage(process_group: int) -> ProcessUsage | None:
    library = _darwin_libproc()
    seconds_per_tick = _darwin_seconds_per_tick()
    if library is None or seconds_per_tick is None:
        return None
    # PROC_PGRP_ONLY and PROC_PIDTASKINFO are stable public libproc selectors.
    pids = (ctypes.c_int * 4096)()
    byte_count = library.proc_listpids(2, process_group, pids, ctypes.sizeof(pids))
    if byte_count <= 0:
        return None
    rss = 0
    cpu_ticks = 0
    count = 0
    for pid in pids[: byte_count // ctypes.sizeof(ctypes.c_int)]:
        if pid <= 0:
            continue
        task = _DarwinTaskInfo()
        copied = library.proc_pidinfo(
            pid, 4, 0, ctypes.byref(task), ctypes.sizeof(task)
        )
        if copied != ctypes.sizeof(task):
            continue
        rss += task.resident_size
        cpu_ticks += task.total_user + task.total_system
        count += 1
    return ProcessUsage(rss, cpu_ticks * seconds_per_tick, count) if count else None


def _ps_tree_usage(process_group: int) -> ProcessUsage | None:
    try:
        completed = subprocess.run(
            ["ps", "-axo", "pgid=,rss=,time="],
            capture_output=True,
            text=True,
            check=False,
            timeout=0.25,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    rss_kib = 0
    cpu = 0.0
    count = 0
    for line in completed.stdout.splitlines():
        fields = line.split()
        if len(fields) != 3:
            continue
        try:
            if int(fields[0]) != process_group:
                continue
            rss_kib += int(fields[1])
            cpu += _parse_cpu_time(fields[2])
            count += 1
        except ValueError:
            continue
    return ProcessUsage(rss_kib * 1024, cpu, count) if count else None


def process_tree_usage(process_group: int) -> ProcessUsage | None:
    return (
        _linux_tree_usage(process_group)
        or _darwin_tree_usage(process_group)
        or _ps_tree_usage(process_group)
    )


class ResourceSupervisor:
    """Own resource checks and bounded process-tree termination."""

    def __init__(self, budget: BridgeBudget, cancellation: CancellationToken) -> None:
        self.budget = budget
        self.cancellation = cancellation
        self.peak_rss_bytes = 0
        self._last_sample = 0.0
        self._ledgers = current_ledgers()
        self._owners: dict[subprocess.Popen[bytes], object] = {}
        self._cpu: dict[subprocess.Popen[bytes], float] = {}
        self._retired: WeakSet[subprocess.Popen[bytes]] = WeakSet()
        self.cpu_seconds = 0.0

    def _account(self, process: subprocess.Popen[bytes], usage: ProcessUsage) -> None:
        if process in self._retired:
            return
        cpu = max(usage.cpu_seconds, getattr(process, "final_cpu_seconds", 0.0))
        previous = self._cpu.get(process, 0.0)
        self.cpu_seconds += max(0.0, cpu - previous)
        self._cpu[process] = max(previous, cpu)
        owner = self._owners.setdefault(process, object())
        # Publish to every parent even if a narrower child was exhausted.
        errors = []
        for ledger in self._ledgers:
            try:
                ledger.sample(owner, cpu_seconds=cpu, rss_bytes=usage.rss_bytes)
            except ResourceExhausted as error:
                errors.append(error)
        if errors:
            raise errors[0]

    def release(self, process: subprocess.Popen[bytes]) -> None:
        if process in self._retired:
            return
        try:
            self._account(process, ProcessUsage(0, 0.0, 0))
            self._check_cpu(None)
        finally:
            owner = self._owners.pop(process, None)
            for ledger in self._ledgers:
                if owner is not None:
                    ledger.release(owner)
            self._cpu.pop(process, None)
            self._retired.add(process)

    def _check_cpu(self, command_id: CommandId | None) -> None:
        if self.cpu_seconds > self.budget.cpu_seconds:
            raise self.error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "bridge-cpu-exhausted",
                f"Agda process tree exceeded {self.budget.cpu_seconds:g} CPU seconds",
                command_id,
            )

    def check(
        self,
        process: subprocess.Popen[bytes],
        *,
        command_id: CommandId | None,
        force_sample: bool = False,
    ) -> ProcessUsage | None:
        self.cancellation.raise_if_cancelled(command_id)
        checkpoint()
        if time.monotonic() >= self.budget.deadline:
            raise self.error(
                BridgeFailure.TIMEOUT,
                "bridge-deadline-exhausted",
                "bridge command exceeded its wall-time budget",
                command_id,
            )
        now = time.monotonic()
        if not force_sample and now - self._last_sample < 0.1:
            return None
        self._last_sample = now
        usage = process_tree_usage(process.pid)
        if usage is None:
            # A short-lived validator can exit after the caller's poll and
            # before the process-tree sample.  A completed child no longer
            # consumes resources; only a still-running unmeterable child must
            # fail closed.
            if process.poll() is not None:
                self._account(process, ProcessUsage(0, 0.0, 0))
                self._check_cpu(command_id)
                return ProcessUsage(0, 0.0, 0)
            raise self.error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "resource-sampling-unavailable",
                "could not measure the Agda process tree; resource limits fail closed",
                command_id,
            )
        self.peak_rss_bytes = max(self.peak_rss_bytes, usage.rss_bytes)
        self._account(process, usage)
        if usage.rss_bytes > self.budget.memory_bytes:
            raise self.error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "bridge-memory-exhausted",
                f"Agda process tree exceeded {self.budget.memory_bytes} bytes RSS",
                command_id,
            )
        self._check_cpu(command_id)
        if usage.process_count > self.budget.process_count:
            raise self.error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "bridge-process-count-exhausted",
                f"Agda process tree exceeded {self.budget.process_count} processes",
                command_id,
            )
        return usage

    def sample(self, process: subprocess.Popen[bytes]) -> ProcessUsage:
        """Return and account for one explicit process-tree usage sample."""

        usage = process_tree_usage(process.pid)
        if usage is None:
            if process.poll() is not None:
                self._account(process, ProcessUsage(0, 0.0, 0))
                return ProcessUsage(0, 0.0, 0)
            raise self.error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "resource-sampling-unavailable",
                "could not measure the Agda process tree; resource limits fail closed",
                None,
            )
        self.peak_rss_bytes = max(self.peak_rss_bytes, usage.rss_bytes)
        self._account(process, usage)
        return usage

    @staticmethod
    def error(
        failure: BridgeFailure,
        code: str,
        message: str,
        command_id: CommandId | None,
    ) -> BridgeError:
        return BridgeError(
            failure,
            BridgeDiagnostic(
                code=code,
                phase=DiagnosticPhase.RESOURCE,
                severity="error",
                message=message,
                retryable=failure in {BridgeFailure.TIMEOUT, BridgeFailure.CANCELLED},
            ),
            command_id=command_id,
        )

    @staticmethod
    def terminate_process_tree(
        process: subprocess.Popen[bytes],
        *,
        graceful_seconds: float = 0.15,
        terminate_seconds: float = 0.35,
    ) -> int:
        if process.poll() is not None:
            return 0
        started = time.monotonic()
        try:
            if process.stdin is not None:
                process.stdin.close()
        except OSError:
            pass
        try:
            process.wait(timeout=graceful_seconds)
            return 0
        except subprocess.TimeoutExpired:
            pass
        _signal_group(process, signal.SIGTERM)
        try:
            process.wait(timeout=terminate_seconds)
            return 0
        except subprocess.TimeoutExpired:
            pass
        _signal_group(process, signal.SIGKILL)
        try:
            process.wait(timeout=max(0.1, 1.8 - (time.monotonic() - started)))
        except subprocess.TimeoutExpired:
            return 1
        return 0


def _signal_group(
    process: subprocess.Popen[bytes], sent_signal: signal.Signals
) -> None:
    try:
        if os.name == "posix":
            os.killpg(process.pid, sent_signal)
        else:
            process.send_signal(sent_signal)
    except (ProcessLookupError, PermissionError):
        pass
