"""Fresh-process, structurally authorized validation for Stage 1."""

from __future__ import annotations

import hashlib
import os
import select
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from ..policy import inspect_patch
from ..resource_budget import charge_io
from ..source_files import agda_source_suffix
from ..verifier_budget import charge_verifier_request
from .contracts import (
    BridgeBudget,
    BridgeCost,
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    DiagnosticPhase,
)
from .diagnostics import diagnostics_from_checker_output
from .operations import (
    CheckOutcome,
    PolicyProfile,
    SourcePatch,
    TrustReport,
    ValidatePatchResult,
)
from .project import ResolvedProject
from .resources import (
    CancellationToken,
    OwnedProcess,
    ResourceSupervisor,
    isolated_process_environment,
    temporary_storage,
)


@dataclass(frozen=True)
class _CheckerRun:
    exit_status: int | None
    output: str
    output_bytes: int
    output_sha256: str
    elapsed_ms: float
    peak_rss_bytes: int
    timed_out: bool


def _validation_error(failure: BridgeFailure, code: str, message: str) -> BridgeError:
    phase = (
        DiagnosticPhase.RESOURCE
        if failure in {BridgeFailure.TIMEOUT, BridgeFailure.RESOURCE_EXHAUSTED}
        else DiagnosticPhase.VALIDATION
    )
    return BridgeError(
        failure,
        BridgeDiagnostic(
            code=code,
            phase=phase,
            severity="error",
            message=message,
            retryable=failure == BridgeFailure.TIMEOUT,
        ),
    )


def _materialize(
    project: ResolvedProject,
    candidate: str,
    patch: SourcePatch,
    overlay: Path,
    budget: BridgeBudget,
    cancellation: CancellationToken,
) -> tuple[Path, tuple[tuple[str, str], ...], int]:
    artifacts: list[tuple[str, str]] = []
    total_bytes = 0
    for index, source in enumerate(project.sources, 1):
        cancellation.raise_if_cancelled()
        if time.monotonic() >= budget.deadline:
            raise _validation_error(
                BridgeFailure.TIMEOUT,
                "validator-materialization-timeout",
                "validation deadline exhausted while copying sources",
            )
        if index > budget.artifact_count:
            raise _validation_error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "validator-artifact-count-exhausted",
                "validation artifact-count budget exhausted",
            )
        suffix = agda_source_suffix(source.path)
        if suffix is None:
            raise _validation_error(
                BridgeFailure.INTERNAL_INVARIANT,
                "validator-source-kind-invalid",
                "resolved project contains a non-Agda source",
            )
        relative = Path(*source.module.name.split("."))
        destination = overlay / Path(str(relative) + suffix)
        destination.parent.mkdir(parents=True, exist_ok=True)
        text = (
            candidate if source.module == patch.module_id else source.path.read_text()
        )
        encoded = text.encode()
        if source.module != patch.module_id:
            charge_io(len(encoded))
        total_bytes += len(encoded)
        if total_bytes > budget.temporary_bytes:
            raise _validation_error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "validator-storage-exhausted",
                "validation temporary-storage budget exhausted",
            )
        try:
            destination.write_bytes(encoded)
            charge_io(len(encoded))
        except OSError as error:
            raise _validation_error(
                BridgeFailure.RESOURCE_EXHAUSTED,
                "validator-overlay-write-failed",
                f"could not materialize validation overlay: {error}",
            ) from error
        digest = hashlib.sha256(encoded).hexdigest()
        artifacts.append((destination.relative_to(overlay).as_posix(), digest))
    root_suffix = agda_source_suffix(project.source_for(patch.module_id))
    if root_suffix is None:
        raise _validation_error(
            BridgeFailure.INTERNAL_INVARIANT,
            "validator-root-source-kind-invalid",
            "patch module resolves to a non-Agda source",
        )
    candidate_path = overlay / Path(
        str(Path(*patch.module_id.name.split("."))) + root_suffix
    )
    return candidate_path, tuple(sorted(artifacts)), total_bytes


def _run_checker(
    command: tuple[str, ...],
    *,
    overlay: Path,
    budget: BridgeBudget,
    cancellation: CancellationToken,
) -> _CheckerRun:
    started = time.monotonic()
    cancellation.raise_if_cancelled()
    charge_verifier_request("fresh-validation")
    try:
        process = OwnedProcess(
            command,
            cwd=overlay,
            env=isolated_process_environment(overlay),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    except OSError as error:
        raise BridgeError(
            BridgeFailure.CHILD_PROCESS_FAILURE,
            BridgeDiagnostic(
                code="validator-process-start-failed",
                phase=DiagnosticPhase.VALIDATION,
                severity="error",
                message=f"could not start fresh Agda validator: {error}",
            ),
        ) from error
    supervisor = ResourceSupervisor(budget, cancellation)
    output = bytearray()
    timed_out = False

    def append_output(chunk: bytes) -> None:
        charge_io(len(chunk))
        if len(chunk) > budget.output_bytes - len(output):
            raise BridgeError(
                BridgeFailure.RESOURCE_EXHAUSTED,
                BridgeDiagnostic(
                    code="validator-output-exhausted",
                    phase=DiagnosticPhase.RESOURCE,
                    severity="error",
                    message="fresh validator exceeded its output-byte budget",
                ),
            )
        output.extend(chunk)

    try:
        if process.stdout is None:
            raise BridgeError(
                BridgeFailure.INTERNAL_INVARIANT,
                BridgeDiagnostic(
                    code="validator-output-pipe-missing",
                    phase=DiagnosticPhase.INTERNAL,
                    severity="error",
                    message="fresh validator process has no output pipe",
                ),
            )
        while True:
            try:
                supervisor.check(process, command_id=None)
            except BridgeError as error:
                timed_out = error.failure == BridgeFailure.TIMEOUT
                raise
            ready, _, _ = select.select([process.stdout.fileno()], [], [], 0.05)
            if ready:
                chunk = os.read(process.stdout.fileno(), 65_536)
                if chunk:
                    append_output(chunk)
                elif process.poll() is not None:
                    break
            if process.poll() is not None and not ready:
                # The child has closed its writer, so bounded reads cannot
                # block. Never call ``read()`` here: a malicious or broken
                # checker may have produced arbitrarily more than the cap.
                while remainder := os.read(process.stdout.fileno(), 65_536):
                    append_output(remainder)
                break
        status = process.wait(timeout=0.1)
    except OSError as error:
        ResourceSupervisor.terminate_process_tree(process)
        raise BridgeError(
            BridgeFailure.CHILD_PROCESS_FAILURE,
            BridgeDiagnostic(
                code="validator-output-read-failed",
                phase=DiagnosticPhase.VALIDATION,
                severity="error",
                message=f"could not read fresh validator output: {error}",
            ),
        ) from error
    except BridgeError:
        ResourceSupervisor.terminate_process_tree(process)
        raise
    finally:
        if process.poll() is None:
            ResourceSupervisor.terminate_process_tree(process)
        if process.stdout is not None:
            process.stdout.close()
        supervisor.release(process)
    raw = bytes(output)
    return _CheckerRun(
        exit_status=status,
        output=raw.decode("utf-8", errors="replace"),
        output_bytes=len(raw),
        output_sha256=hashlib.sha256(raw).hexdigest(),
        elapsed_ms=(time.monotonic() - started) * 1000.0,
        peak_rss_bytes=supervisor.peak_rss_bytes,
        timed_out=timed_out,
    )


def _checks(
    successful: bool, diagnostics: tuple[BridgeDiagnostic, ...]
) -> tuple[CheckOutcome, ...]:
    phases = {
        "parse": {DiagnosticPhase.PARSING},
        "scope": {DiagnosticPhase.SCOPE},
        "type": {
            DiagnosticPhase.ELABORATION,
            DiagnosticPhase.UNIFICATION,
            DiagnosticPhase.INSTANCE_SEARCH,
        },
        "coverage": {DiagnosticPhase.COVERAGE},
        "positivity": {DiagnosticPhase.POSITIVITY},
        "termination": {DiagnosticPhase.TERMINATION},
        "metas": {DiagnosticPhase.ELABORATION},
    }
    outcomes: list[CheckOutcome] = []
    for name, relevant in phases.items():
        selected = tuple(item for item in diagnostics if item.phase in relevant)
        # Agda runs these checks as one pipeline.  A failed earlier phase means
        # later phases were not successfully completed; the Boolean schema must
        # never misreport an unexecuted check as passing.
        passed = successful
        outcomes.append(
            CheckOutcome(
                check=name,  # type: ignore[arg-type]
                passed=passed,
                diagnostics=selected,
            )
        )
    return tuple(outcomes)


def validate_patch(
    project: ResolvedProject,
    patch: SourcePatch,
    profile: PolicyProfile,
    budget: BridgeBudget,
    *,
    cancellation: CancellationToken | None = None,
) -> ValidatePatchResult:
    token = cancellation or CancellationToken()
    token.raise_if_cancelled()
    started = time.monotonic()
    policy = inspect_patch(project, patch, profile)
    if not policy.accepted or policy.candidate is None:
        policy_checks: tuple[CheckOutcome, ...] = (
            CheckOutcome("parse", False, policy.diagnostics),
            CheckOutcome("scope", False, policy.diagnostics),
            CheckOutcome("type", False, policy.diagnostics),
            CheckOutcome("coverage", False, policy.diagnostics),
            CheckOutcome("positivity", False, policy.diagnostics),
            CheckOutcome("termination", False, policy.diagnostics),
            CheckOutcome("metas", False, policy.diagnostics),
        )
        return ValidatePatchResult(
            project=project.handle,
            patch_id=patch.identity,
            verified=False,
            checks=policy_checks,
            diagnostics=policy.diagnostics,
            trust_report=None,
            cost=BridgeCost(elapsed_ms=(time.monotonic() - started) * 1000.0),
        )

    with (
        tempfile.TemporaryDirectory(prefix="agdaprover-stage1-validator-") as temporary,
        temporary_storage(Path(temporary)) as storage,
    ):
        overlay = Path(temporary)
        candidate_path, artifacts, temporary_bytes = _materialize(
            project, policy.candidate, patch, overlay, budget, token
        )
        storage.sample(force=True)
        relative_candidate = candidate_path.relative_to(overlay).as_posix()
        options = tuple(project.options)
        command_parts = [
            str(project.toolchain.executable),
            "--no-libraries",
            "--ignore-interfaces",
            "-i",
            ".",
        ]
        if profile.require_safe and "--safe" not in options:
            command_parts.append("--safe")
        command_parts.extend(options)
        command_parts.append(relative_candidate)
        command = tuple(command_parts)
        run = _run_checker(command, overlay=overlay, budget=budget, cancellation=token)
        storage.sample(force=True)
        successful = run.exit_status == 0 and not run.timed_out
        diagnostics = (
            diagnostics_from_checker_output(run.output, project_root=overlay)
            if not successful or "warning:" in run.output or "error:" in run.output
            else ()
        )
        checks = _checks(successful, diagnostics)
        verified = successful and all(item.passed for item in checks)
        effective_options = tuple(command_parts[1:-1])
        trust = TrustReport(
            agda_version=project.toolchain.version,
            agda_binary_sha256=project.toolchain.executable_sha256,
            environment_id=project.environment_id,
            source_revision=project.source_revision,
            patch_id=patch.identity,
            options=effective_options,
            imported_artifacts=artifacts,
            admitted_assumptions=policy.admitted_assumptions,
            policy_profile=profile.name,
            sandbox_profile=(
                "isolated-overlay-sanitized-home-no-libraries-process-group-v1"
            ),
            command=("agda", *command[1:]),
            exit_status=run.exit_status,
            output_sha256=run.output_sha256,
            fresh_process=True,
            offline=True,
        )
        return ValidatePatchResult(
            project=project.handle,
            patch_id=patch.identity,
            verified=verified,
            checks=checks,
            diagnostics=diagnostics,
            trust_report=trust,
            cost=BridgeCost(
                process_starts=1,
                bytes_read=run.output_bytes,
                peak_rss_bytes=run.peak_rss_bytes,
                temporary_bytes=temporary_bytes,
                elapsed_ms=(time.monotonic() - started) * 1000.0,
            ),
        )
