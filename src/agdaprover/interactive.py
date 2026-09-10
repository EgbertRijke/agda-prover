"""Editor-neutral control plane for one long-running local proof search."""

from __future__ import annotations

import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, TextIO

from .contracts import TaskSpec
from .principal_variation import load_principal_variation
from .project_configuration import ProjectConfiguration
from .verification import ValidationError, validate_reconstruction

INTERACTIVE_COMMAND_SCHEMA = "agdaprover.interactive.command.v1"
INTERACTIVE_EVENT_SCHEMA = "agdaprover.interactive.event.v1"
MAX_INTERACTIVE_COMMAND_BYTES = 1_048_576
RunState = Literal["running", "paused", "completed", "stopped", "failed"]


@dataclass(frozen=True)
class InteractivePolicy:
    """Small policy surface kept separate for rapid UX/latency iteration."""

    stop_grace_seconds: float = 2.0
    command_byte_limit: int = MAX_INTERACTIVE_COMMAND_BYTES


DEFAULT_INTERACTIVE_POLICY = InteractivePolicy()


@dataclass(frozen=True)
class InteractiveCommand:
    request_id: str
    command: Literal[
        "status",
        "principal-variation",
        "pause",
        "resume",
        "stop",
        "accept-goal",
    ]
    goal_id: int | None = None
    variation_id: str | None = None

    @classmethod
    def from_dict(cls, value: object) -> InteractiveCommand:
        if not isinstance(value, dict):
            raise ValueError("interactive command must be an object")
        allowed = {
            "schema_version",
            "request_id",
            "command",
            "goal_id",
            "variation_id",
        }
        unknown = set(value) - allowed
        if unknown:
            raise ValueError(f"unknown interactive command fields: {sorted(unknown)!r}")
        if value.get("schema_version") != INTERACTIVE_COMMAND_SCHEMA:
            raise ValueError("unsupported interactive command schema")
        request_id = value.get("request_id")
        if not isinstance(request_id, str) or not re.fullmatch(
            r"[A-Za-z0-9._:-]{1,128}", request_id
        ):
            raise ValueError("interactive request_id is malformed")
        command = value.get("command")
        commands = {
            "status",
            "principal-variation",
            "pause",
            "resume",
            "stop",
            "accept-goal",
        }
        if command not in commands:
            raise ValueError("unsupported interactive command")
        goal_id = value.get("goal_id")
        variation_id = value.get("variation_id")
        if command == "accept-goal":
            if type(goal_id) is not int or goal_id < 0:
                raise ValueError("accept-goal requires a nonnegative goal_id")
            if not isinstance(variation_id, str) or not re.fullmatch(
                r"[0-9a-f]{24}", variation_id
            ):
                raise ValueError("accept-goal requires a principal variation ID")
        elif goal_id is not None or variation_id is not None:
            raise ValueError("goal_id and variation_id are valid only for accept-goal")
        return cls(request_id, command, goal_id, variation_id)


def _descendant_process_groups(root_pid: int) -> tuple[int, ...]:
    """Return the root and all currently observable descendant process groups."""

    if os.name != "posix":
        return (root_pid,)
    try:
        completed = subprocess.run(
            ["ps", "-axo", "pid=,ppid=,pgid="],
            capture_output=True,
            text=True,
            check=False,
            timeout=0.5,
        )
    except (OSError, subprocess.TimeoutExpired):
        return (root_pid,)
    rows: list[tuple[int, int, int]] = []
    for line in completed.stdout.splitlines():
        fields = line.split()
        if len(fields) != 3:
            continue
        try:
            rows.append((int(fields[0]), int(fields[1]), int(fields[2])))
        except ValueError:
            continue
    descendants = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, parent_pid, _group_id in rows:
            if parent_pid in descendants and pid not in descendants:
                descendants.add(pid)
                changed = True
    groups = {
        group_id
        for pid, _parent_pid, group_id in rows
        if pid in descendants and group_id > 0
    }
    groups.add(root_pid)
    return (root_pid, *sorted(groups - {root_pid}))


def _source_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def event(
    event_name: str,
    *,
    run_id: str,
    request_id: str | None,
    state: RunState,
    payload: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema_version": INTERACTIVE_EVENT_SCHEMA,
        "event": event_name,
        "run_id": run_id,
        "request_id": request_id,
        "state": state,
        "payload": dict(payload or {}),
    }


class InteractiveRunController:
    """Own lifecycle and acceptance without depending on proof-search internals."""

    def __init__(
        self,
        *,
        run_id: str,
        process: subprocess.Popen[bytes],
        source_file: Path,
        source_sha256: str,
        variation_path: Path,
        result_path: Path,
        policy: InteractivePolicy = DEFAULT_INTERACTIVE_POLICY,
        project_configuration: ProjectConfiguration | None = None,
        signal_group: Callable[[int, int], None] = os.killpg,
        process_groups: Callable[[int], tuple[int, ...]] = (_descendant_process_groups),
        validator: Callable[..., tuple[dict[str, Any], dict[str, Any]]] = (
            validate_reconstruction
        ),
    ) -> None:
        self.run_id = run_id
        self.process = process
        self.source_file = source_file
        self.source_sha256 = source_sha256
        self.variation_path = variation_path
        self.result_path = result_path
        self.policy = policy
        self.project_configuration = project_configuration
        self._signal_group = signal_group
        self._process_groups = process_groups
        self._validator = validator
        self._state: RunState = "running"
        self._paused_groups: tuple[int, ...] = ()

    @property
    def state(self) -> RunState:
        if self._state in {"stopped", "failed"}:
            return self._state
        return_code = self.process.poll()
        if return_code is None:
            return self._state
        self._state = "completed" if self.result_path.is_file() else "failed"
        return self._state

    def _signal_groups(self, groups: tuple[int, ...], signal_number: int) -> None:
        if os.name != "posix":
            raise RuntimeError("interactive process-group control requires POSIX")
        for group_id in groups:
            try:
                self._signal_group(group_id, signal_number)
            except (PermissionError, ProcessLookupError):
                continue

    def _live_groups(self) -> tuple[int, ...]:
        groups = self._process_groups(self.process.pid)
        return tuple(dict.fromkeys((self.process.pid, *groups)))

    def pause(self) -> RunState:
        state = self.state
        if state == "paused":
            return state
        if state != "running":
            raise ValueError(f"cannot pause an interactive run in state {state}")
        # Freeze the worker first so it cannot launch another child while the
        # descendant groups are being enumerated.  Agda deliberately owns a
        # separate process group, so pause that group explicitly as well.
        self._signal_groups((self.process.pid,), signal.SIGSTOP)
        groups = self._live_groups()
        self._signal_groups(groups[1:], signal.SIGSTOP)
        self._paused_groups = groups
        self._state = "paused"
        return self._state

    def resume(self) -> RunState:
        state = self.state
        if state == "running":
            return state
        if state != "paused":
            raise ValueError(f"cannot resume an interactive run in state {state}")
        groups = tuple(dict.fromkeys((*self._paused_groups, *self._live_groups())))
        # Resume children before the worker that may immediately wait on them.
        self._signal_groups(tuple(reversed(groups)), signal.SIGCONT)
        self._paused_groups = ()
        self._state = "running"
        return self._state

    def stop(self) -> RunState:
        state = self.state
        if state in {"stopped", "completed", "failed"}:
            return state
        if state == "running":
            self.pause()
        groups = tuple(dict.fromkeys((*self._paused_groups, *self._live_groups())))
        self._signal_groups(tuple(reversed(groups)), signal.SIGTERM)
        self._signal_groups(tuple(reversed(groups)), signal.SIGCONT)
        try:
            self.process.wait(timeout=self.policy.stop_grace_seconds)
        except subprocess.TimeoutExpired:
            self._signal_groups(tuple(reversed(groups)), signal.SIGKILL)
            self.process.wait(timeout=self.policy.stop_grace_seconds)
        self._paused_groups = ()
        self._state = "stopped"
        return self._state

    def principal_variation(self) -> dict[str, Any] | None:
        return load_principal_variation(self.variation_path)

    def result(self) -> dict[str, Any] | None:
        if not self.result_path.is_file():
            return None
        if self.result_path.stat().st_size > 32 * 1024 * 1024:
            raise ValueError("interactive result exceeds its byte limit")
        value = json.loads(self.result_path.read_text())
        if not isinstance(value, dict):
            raise ValueError("interactive worker result is malformed")
        return value

    def accept_goal(self, goal_id: int, variation_id: str) -> dict[str, Any]:
        variation = self.principal_variation()
        if variation is None:
            raise ValueError("no principal variation is available yet")
        if variation["variation_id"] != variation_id:
            raise ValueError("principal variation changed before acceptance")
        if _source_sha256(self.source_file) != self.source_sha256:
            raise ValueError("source changed while the interactive run was active")
        options = [
            option
            for option in variation["acceptance_options"]
            if option["goal_id"] == goal_id
        ]
        if len(options) != 1:
            raise ValueError("goal is not individually completable on this variation")
        if self.state == "running":
            self.pause()
        patch = options[0]["patch"]
        checking_options: dict[str, Any] = {}
        if self.project_configuration is not None:
            checking_options["project_configuration"] = self.project_configuration
        try:
            validation, trust_report = self._validator(
                self.source_file,
                patch,
                timeout_seconds=float("inf"),
                **checking_options,
            )
        except (OSError, ValidationError) as error:
            raise ValueError(
                f"principal-variation validation failed: {error}"
            ) from error
        if not validation.get("checked"):
            raise ValueError(
                validation.get("diagnostic")
                or "fresh Agda rejected the principal-variation completion"
            )
        self.stop()
        return {
            "schema_version": "agdaprover.interactive-acceptance.v1",
            "status": "verified",
            "task_id": variation["task_id"],
            "source_file": str(self.source_file),
            "source_hash": self.source_sha256,
            "goal_id": goal_id,
            "proof_term": options[0].get("proof_term"),
            "patch": patch,
            "validation": validation,
            "trust_report": trust_report,
            "principal_variation_id": variation_id,
            "joint_completion": False,
        }

    def dispatch(self, command: InteractiveCommand) -> dict[str, Any]:
        if command.command == "status":
            payload: dict[str, Any] = {}
            if (result := self.result()) is not None:
                payload["result"] = result
            return event(
                "status",
                run_id=self.run_id,
                request_id=command.request_id,
                state=self.state,
                payload=payload,
            )
        if command.command == "principal-variation":
            variation = self.principal_variation()
            return event(
                "principal-variation",
                run_id=self.run_id,
                request_id=command.request_id,
                state=self.state,
                payload={"principal_variation": variation},
            )
        if command.command == "pause":
            state = self.pause()
            return event(
                "paused",
                run_id=self.run_id,
                request_id=command.request_id,
                state=state,
            )
        if command.command == "resume":
            state = self.resume()
            return event(
                "resumed",
                run_id=self.run_id,
                request_id=command.request_id,
                state=state,
            )
        if command.command == "stop":
            state = self.stop()
            return event(
                "stopped",
                run_id=self.run_id,
                request_id=command.request_id,
                state=state,
            )
        if command.goal_id is None or command.variation_id is None:
            raise ValueError("accept-goal command is incomplete")
        accepted = self.accept_goal(command.goal_id, command.variation_id)
        return event(
            "accepted-goal",
            run_id=self.run_id,
            request_id=command.request_id,
            state=self.state,
            payload={"result": accepted},
        )


def launch_interactive_run(
    task: TaskSpec,
    *,
    variation_path: Path,
    result_path: Path,
    policy: InteractivePolicy = DEFAULT_INTERACTIVE_POLICY,
) -> InteractiveRunController:
    source_file = task.source_file.resolve()
    source_hash = _source_sha256(source_file)
    run_id = hashlib.sha256(
        f"{source_hash}:{time.monotonic_ns()}".encode("ascii")
    ).hexdigest()[:20]
    argv = [
        sys.executable,
        "-m",
        "agdaprover.interactive_worker",
        str(source_file),
        "--variation-file",
        str(variation_path),
        "--result-file",
        str(result_path),
        "--max-candidates",
        str(task.max_candidates),
        "--max-term-size",
        str(task.max_term_size),
        "--ranker",
        task.ranker,
    ]
    if task.goal_id is not None:
        argv.extend(("--goal", str(task.goal_id)))
    if task.goal_position is not None:
        argv.extend(("--goal-position", str(task.goal_position)))
    if task.max_depth is not None:
        argv.extend(("--max-depth", str(task.max_depth)))
    if task.max_verifier_calls is not None:
        argv.extend(("--max-verifier-calls", str(task.max_verifier_calls)))
    if task.timeout_seconds is not None:
        argv.extend(("--timeout", str(task.timeout_seconds)))
    if task.resources.cpu_seconds is not None:
        argv.extend(("--cpu-seconds", str(task.resources.cpu_seconds)))
    for name in ("memory_bytes", "io_bytes", "temporary_bytes"):
        argv.extend(("--" + name.replace("_", "-"), str(getattr(task.resources, name))))
    if task.model_path is not None:
        argv.extend(("--model", str(task.model_path)))
    if task.action_model_path is not None:
        argv.extend(("--action-model", str(task.action_model_path)))
    if task.project_configuration is not None:
        argv.extend(
            (
                "--project-configuration",
                json.dumps(task.project_configuration.to_dict()),
            )
        )
    process = subprocess.Popen(
        argv,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    return InteractiveRunController(
        run_id=run_id,
        process=process,
        source_file=source_file,
        source_sha256=source_hash,
        variation_path=variation_path,
        result_path=result_path,
        policy=policy,
        project_configuration=task.project_configuration,
    )


def serve_interactive(
    controller: InteractiveRunController,
    input_stream: TextIO,
    output_stream: TextIO,
) -> int:
    exit_code = 0

    def emit(value: Mapping[str, Any]) -> None:
        output_stream.write(
            json.dumps(value, sort_keys=True, ensure_ascii=False) + "\n"
        )
        output_stream.flush()

    emit(
        event(
            "started",
            run_id=controller.run_id,
            request_id=None,
            state="running",
            payload={
                "commands": [
                    "status",
                    "principal-variation",
                    "pause",
                    "resume",
                    "stop",
                    "accept-goal",
                ]
            },
        )
    )
    try:
        for line in input_stream:
            if len(line.encode("utf-8")) > controller.policy.command_byte_limit:
                emit(
                    event(
                        "error",
                        run_id=controller.run_id,
                        request_id=None,
                        state=controller.state,
                        payload={
                            "diagnostic": "interactive command exceeds byte limit"
                        },
                    )
                )
                continue
            request_id: str | None = None
            try:
                decoded = json.loads(line)
                if isinstance(decoded, dict) and isinstance(
                    decoded.get("request_id"), str
                ):
                    request_id = decoded["request_id"]
                command = InteractiveCommand.from_dict(decoded)
                emit(controller.dispatch(command))
            except (json.JSONDecodeError, OSError, RuntimeError, ValueError) as error:
                emit(
                    event(
                        "error",
                        run_id=controller.run_id,
                        request_id=request_id,
                        state=controller.state,
                        payload={"diagnostic": str(error)},
                    )
                )
    except KeyboardInterrupt:
        if controller.state in {"running", "paused"}:
            controller.stop()
        emit(
            event(
                "interrupted",
                run_id=controller.run_id,
                request_id=None,
                state=controller.state,
            )
        )
        exit_code = 130
    finally:
        if controller.state in {"running", "paused"}:
            controller.stop()
    return exit_code
