"""P0 validation facade over the Stage 1 structural validation boundary."""

from __future__ import annotations

import re
import time
from pathlib import Path
from typing import Any

from .artifacts import executable_sha256, file_sha256
from .bridge.configuration import project_request
from .bridge.contracts import BridgeBudget, BridgeError, BridgeFailure, SourceRange
from .bridge.operations import (
    PolicyProfile,
    SourceEdit,
    SourcePatch,
    ValidatePatchResult,
)
from .bridge.project import ResolvedProject, write_source_overlay
from .bridge.resources import temporary_workspace
from .bridge.session import ConformingKernelSession
from .bridge.source_prefix import independent_prefix, inspect_prefix
from .bridge.workspace import (
    ProjectInputs,
    SourceWorkspace,
    checking_environment,
    prepare_source_workspace,
)
from .contracts import GoalInfo
from .kernel.p0 import AgdaBridgeError, AgdaLoadError, AgdaSession
from .presentation import apply_source_edit
from .project_configuration import ProjectConfiguration
from .resource_budget import ResourceLimitError, charge_io
from .source_files import agda_source_suffix

FORBIDDEN_CANDIDATE_FRAGMENTS = (
    "postulate",
    "{-#",
    "FOREIGN",
    "COMPILE",
    "TERMINATING",
    "NON_TERMINATING",
)


class ValidationError(RuntimeError):
    pass


def _remaining(deadline: float, operation: str) -> float:
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise TimeoutError(f"validation deadline exhausted before {operation}")
    return remaining


def replace_goal(source: str, goal: GoalInfo, proof_term: str) -> str:
    if any(fragment in proof_term for fragment in FORBIDDEN_CANDIDATE_FRAGMENTS):
        raise ValidationError("candidate contains a forbidden source fragment")
    start, end = goal.source_range
    if start <= 0 or end <= start:
        raise ValidationError("Agda returned an invalid goal source range")
    selected = source[start - 1 : end - 1]
    if not ((selected.startswith("{!") and selected.endswith("!}")) or selected == "?"):
        raise ValidationError(f"goal range does not select a hole: {selected!r}")
    return source[: start - 1] + proof_term + source[end - 1 :]


def _run_patch(
    source_file: Path,
    edit: SourceEdit,
    *,
    agda_executable: str,
    timeout_seconds: float,
    policy_profile: str,
    project_configuration: ProjectConfiguration | None = None,
) -> tuple[ValidatePatchResult, ConformingKernelSession]:
    budget = BridgeBudget.for_run(timeout_seconds)
    session = ConformingKernelSession()
    try:
        opened = session.open_project(
            project_request(
                source_file, project_configuration, executable=agda_executable
            ),
            budget,
        )
        patch = SourcePatch(
            opened.environment_id,
            opened.source_revision,
            opened.root_module,
            (edit,),
        )
        result = session.validate_patch(
            opened.project,
            patch,
            PolicyProfile(policy_profile),
            budget,
        )
    except BridgeError as error:
        session.close()
        if error.failure == BridgeFailure.TOOLCHAIN_ERROR:
            raise AgdaBridgeError(str(error)) from error
        if error.failure == BridgeFailure.RESOURCE_EXHAUSTED:
            raise ResourceLimitError(str(error)) from error
        if error.failure == BridgeFailure.TIMEOUT:
            raise TimeoutError(str(error)) from error
        raise ValidationError(str(error)) from error
    except (OSError, ValueError) as error:
        session.close()
        raise ValidationError(str(error)) from error
    except BaseException:
        # Budget exhaustion and interruption must retain their exact status,
        # while still releasing both session and runtime overlays.
        session.close()
        raise
    return result, session


def _p0_result(
    result: ValidatePatchResult,
    project: ResolvedProject | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    trust = result.trust_report
    diagnostic = "\n".join(item.message for item in result.diagnostics)
    validation = {
        "fresh_process": bool(trust and trust.fresh_process),
        "checked": result.verified,
        "timed_out": any(item.code.endswith("timeout") for item in result.diagnostics),
        "exit_status": trust.exit_status if trust else None,
        "checker_output_sha256": trust.output_sha256 if trust else None,
        "diagnostic": diagnostic,
        "elapsed_ms": result.cost.elapsed_ms,
        "checks": [item.to_dict() for item in result.checks],
        "bridge_schema_version": "agdaprover.bridge.v1",
        "patch_id": result.patch_id,
        "fresh_validation_runs": result.cost.process_starts,
    }
    trust_report: dict[str, Any] = {
        "agda_binary_hash": trust.agda_binary_sha256 if trust else None,
        "agda_version": trust.agda_version if trust else None,
        "options": list(trust.options) if trust else [],
        "imported_project_hashes": [
            {
                "module_file": path,
                "overlay_path": path,
                "sha256": digest,
            }
            for path, digest in (trust.imported_artifacts if trust else ())
        ],
        "admitted_axioms_and_primitives": (
            list(trust.admitted_assumptions) if trust else []
        ),
        "policy_profile": trust.policy_profile if trust else None,
        "sandbox_profile": trust.sandbox_profile if trust else None,
        "checker_command": list(trust.command) if trust else [],
        "checker_exit_status": trust.exit_status if trust else None,
        "checker_output_hash": trust.output_sha256 if trust else None,
        "environment_id": trust.environment_id.value if trust else None,
        "source_revision": trust.source_revision.value if trust else None,
        "patch_id": trust.patch_id if trust else result.patch_id,
        "fresh_process": bool(trust and trust.fresh_process),
        "offline": bool(trust and trust.offline),
    }
    if project is not None and project.libraries:
        trust_report["checking_environment"] = checking_environment(project)
    return validation, trust_report


def validate_standalone_module(
    source: str,
    *,
    filename: str,
    agda_executable: str = "agda",
    agda_version: str | None = None,
    timeout_seconds: float = 2.0,
    policy_profile: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    del agda_version
    source_suffix = agda_source_suffix(filename)
    module_stem = filename[: -len(source_suffix)] if source_suffix else ""
    if source_suffix is None or not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", module_stem):
        raise ValidationError("invalid standalone Agda module filename")
    if timeout_seconds <= 0:
        raise ValidationError("standalone validation timeout must be positive")
    with temporary_workspace(prefix="agdaprover-standalone-") as temporary:
        source_file = Path(temporary) / filename
        source_file.write_text(source)
        charge_io(len(source.encode()))
        edit = SourceEdit(SourceRange(1, len(source) + 1), source, source)
        result, session = _run_patch(
            source_file,
            edit,
            agda_executable=agda_executable,
            timeout_seconds=timeout_seconds,
            policy_profile=policy_profile,
        )
        try:
            return _p0_result(result, session.project)
        finally:
            session.close()


def validate_candidate(
    source_file: Path,
    goal: GoalInfo,
    proof_term: str,
    *,
    agda_executable: str = "agda",
    timeout_seconds: float = 10.0,
    project_configuration: ProjectConfiguration | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    source = source_file.read_text()
    replace_goal(source, goal, proof_term)
    start, end = goal.source_range
    result, session = _run_patch(
        source_file,
        SourceEdit(SourceRange(start, end), source[start - 1 : end - 1], proof_term),
        agda_executable=agda_executable,
        timeout_seconds=timeout_seconds,
        policy_profile="p0-restricted-term-ir",
        project_configuration=project_configuration,
    )
    try:
        return _p0_result(result, session.project)
    finally:
        session.close()


def validate_reconstruction(
    source_file: Path,
    edit: dict[str, Any],
    *,
    agda_executable: str = "agda",
    agda_version: str | None = None,
    timeout_seconds: float = 10.0,
    project_configuration: ProjectConfiguration | None = None,
    expected_inputs: ProjectInputs | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    del agda_version
    replacement = edit.get("replacement", "")
    if not isinstance(replacement, str):
        raise ValidationError("reconstruction replacement must be text")
    source = source_file.read_text()
    try:
        candidate = apply_source_edit(source, edit)
    except ValueError as error:
        raise ValidationError(str(error)) from error
    source_range = edit.get("source_range")
    if not (
        isinstance(source_range, list)
        and len(source_range) == 2
        and all(isinstance(value, int) for value in source_range)
    ):
        raise ValidationError("invalid reconstruction source range")
    start, end = source_range
    started = time.monotonic()
    deadline = started + timeout_seconds
    if expected_inputs is not None:
        expected_inputs.assert_current(deadline=deadline)
    result, session = _run_patch(
        source_file,
        SourceEdit(
            SourceRange(start, end),
            source[start - 1 : end - 1],
            replacement,
        ),
        agda_executable=agda_executable,
        timeout_seconds=_remaining(deadline, "fresh structural validation"),
        project_configuration=project_configuration,
        policy_profile=(
            "p0-restricted-joint-prefix-reconstruction"
            if edit.get("style") == "joint-clauses"
            else "p0-restricted-clause-reconstruction"
        ),
    )
    try:
        validation, trust_report = _p0_result(result, session.project)
    finally:
        session.close()
    if (
        not validation["checked"]
        and not validation["timed_out"]
        and _only_unsolved_metas(validation["diagnostic"])
    ):
        remaining_goals = _validate_preexisting_holes(
            source_file,
            candidate,
            edit,
            agda_executable=agda_executable,
            timeout_seconds=_remaining(deadline, "open-goal differential check"),
            deadline=deadline,
            project_configuration=project_configuration,
        )
        if remaining_goals is not None:
            prefix = _validate_completed_prefix(
                source_file,
                candidate,
                start - 1 + len(replacement),
                edit_start=start - 1,
                remaining_ranges=tuple(goal.source_range for goal in remaining_goals),
                agda_executable=agda_executable,
                deadline=deadline,
                project_configuration=project_configuration,
            )
            validation["prefix_validation"] = prefix
            validation["fresh_validation_runs"] += prefix.get("validation", {}).get(
                "fresh_validation_runs", 0
            )
            validation["elapsed_ms"] = (time.monotonic() - started) * 1000
            if prefix["status"] != "verified":
                validation["diagnostic"] += "\nprefix validation: " + prefix.get(
                    "reason", prefix["status"]
                )
                return validation, trust_report
            if not _same_prefix_environment(trust_report, prefix["trust_report"]):
                prefix["status"] = "incomplete"
                prefix["reason"] = "prefix-checking-environment-mismatch"
                validation["diagnostic"] += "\nprefix checking environment mismatch"
                return validation, trust_report
            joint = edit.get("style") == "joint-clauses"
            validation.update(
                {
                    "checked": True,
                    "batch_clean": False,
                    "validation_scope": "target-prefix"
                    if joint
                    else "target-definition",
                    "remaining_open_goals": [
                        goal.to_dict() for goal in remaining_goals
                    ],
                    "acceptance_basis": "fresh strict declaration-prefix check and unchanged remaining goal ranges",
                    "batch_diagnostic": validation["diagnostic"],
                    "diagnostic": "",
                }
            )
            trust_report.update(
                {
                    "validation_scope": "target-prefix"
                    if joint
                    else "target-definition",
                    "remaining_pre_existing_interaction_metas": len(remaining_goals),
                    "supplemental_checker_command": ["agda", "--interaction-json"],
                    "prefix_validation": prefix["trust_report"],
                }
            )
    if expected_inputs is not None:
        expected_inputs.assert_current(deadline=deadline)
    return validation, trust_report


def _same_prefix_environment(full: dict[str, Any], prefix: dict[str, Any]) -> bool:
    library_bound = "checking_environment" in full or "checking_environment" in prefix

    def options(report: dict[str, Any]) -> list[str]:
        return [
            "--library-file=<isolated-registry>"
            if library_bound and option.startswith("--library-file=")
            else option
            for option in report["options"]
        ]

    if any(
        full[key] != prefix[key] for key in ("agda_binary_hash", "agda_version")
    ) or options(full) != options(prefix):
        return False
    if library_bound:
        full_environment = full.get("checking_environment")
        prefix_environment = prefix.get("checking_environment")
        if not isinstance(full_environment, dict) or not isinstance(
            prefix_environment, dict
        ):
            return False
        if any(
            full_environment.get(key) != prefix_environment.get(key)
            for key in ("schema_version", "root_module", "command_options", "libraries")
        ):
            return False
        full_sources = full_environment["sources"]
        return all(
            full_sources.get(name) == identity
            for name, identity in prefix_environment["sources"].items()
        )
    root = full["checker_command"][-1]
    if prefix["checker_command"][-1] != root:
        return False
    imports = {
        row["overlay_path"]: row["sha256"] for row in full["imported_project_hashes"]
    }
    return all(
        row["overlay_path"] == root or imports.get(row["overlay_path"]) == row["sha256"]
        for row in prefix["imported_project_hashes"]
    )


def _validate_completed_prefix(
    source_file: Path,
    candidate: str,
    end: int,
    *,
    edit_start: int,
    remaining_ranges: tuple[tuple[int, int], ...],
    agda_executable: str,
    deadline: float,
    project_configuration: ProjectConfiguration | None = None,
) -> dict[str, Any]:
    with temporary_workspace(prefix="agdaprover-prefix-validation-") as tmp:
        workspace = prepare_project_overlay(
            source_file,
            candidate,
            Path(tmp),
            project_configuration=project_configuration,
            timeout_seconds=_remaining(deadline, "prefix overlay"),
        )
        path, dependencies = workspace.source_file, workspace.files
        remaining = _remaining(deadline, "prefix declaration inspection")
        try:
            parsed = inspect_prefix(
                path,
                candidate,
                end,
                BridgeBudget.for_run(remaining),
            )
        except BridgeError as error:
            if error.failure == BridgeFailure.RESOURCE_EXHAUSTED:
                raise ResourceLimitError(str(error)) from error
            if error.failure == BridgeFailure.TIMEOUT:
                raise TimeoutError(str(error)) from error
            raise OSError(str(error)) from error
        if parsed["status"] != "parsed":
            return parsed
        allow_omissions = True
        for _, dependency in dependencies:
            _remaining(deadline, "prefix dependency reflection guard")
            # Imported macros can inspect names not mentioned by the caller.
            # This is an over-approximating veto, not lexical proof acceptance.
            if any(word in dependency.read_text() for word in ("macro", "unquote")):
                allow_omissions = False
                break
        prefix, omitted = independent_prefix(
            candidate,
            parsed,
            edit_start,
            remaining_ranges,
            allow_omissions=allow_omissions,
            deadline=deadline,
        )
        path.write_text(prefix)
        charge_io(len(prefix.encode()))
        result, session = _run_patch(
            path,
            SourceEdit(SourceRange(1, len(prefix) + 1), prefix, prefix),
            agda_executable=agda_executable,
            timeout_seconds=_remaining(deadline, "fresh strict prefix validation"),
            policy_profile="p0-restricted-joint-prefix-reconstruction",
            project_configuration=workspace.configuration,
        )
        try:
            checked, trust = _p0_result(result, session.project)
        finally:
            session.close()
        if checked["timed_out"]:
            raise TimeoutError("strict prefix validation deadline exhausted")
        return {
            "schema_version": "agdaprover.prefix-validation.v1",
            "status": "verified" if checked["checked"] else "incomplete",
            "parser": parsed,
            "omitted_declarations": omitted,
            "validation": checked,
            "trust_report": trust,
        }


def validate_partial_reconstruction(
    source_file: Path,
    edit: dict[str, Any],
    *,
    timeout_seconds: float = 10.0,
    project_configuration: ProjectConfiguration | None = None,
) -> dict[str, Any]:
    source = source_file.read_text()
    try:
        candidate = apply_source_edit(source, edit)
    except ValueError as error:
        raise ValidationError(str(error)) from error
    deadline = time.monotonic() + timeout_seconds
    with temporary_workspace(prefix="agdaprover-step-reconstruction-") as temporary:
        workspace = prepare_project_overlay(
            source_file,
            candidate,
            Path(temporary),
            project_configuration=project_configuration,
            timeout_seconds=_remaining(deadline, "partial reconstruction overlay"),
        )
        try:
            with AgdaSession(
                timeout_seconds=_remaining(deadline, "partial reconstruction load"),
                deadline=deadline,
                project_configuration=workspace.configuration,
            ) as session:
                goals = session.load_module(workspace.source_file)
        except AgdaLoadError as error:
            raise ValidationError(
                f"Agda rejected clause-style refinement: {error}"
            ) from error
    return {
        "fresh_process": True,
        "loaded": True,
        "open_goals": [goal.to_dict() for goal in goals],
        "generated_goals": [
            goal.to_dict()
            for goal in goals
            if edit["source_range"][0] <= goal.source_range[0]
            and goal.source_range[1]
            <= edit["source_range"][0] + len(edit["replacement"])
        ],
        "complete_proof": False,
    }


def _only_unsolved_metas(diagnostic: str) -> bool:
    error_kinds = re.findall(r"error:\s*\[([^]]+)\]", diagnostic)
    return bool(error_kinds) and set(error_kinds) <= {
        "UnsolvedInteractionMetas",
        "UnsolvedMetaVariables",
        "UnsolvedConstraints",
    }


def _validate_preexisting_holes(
    source_file: Path,
    candidate: str,
    edit: dict[str, Any],
    *,
    agda_executable: str,
    timeout_seconds: float,
    deadline: float | None = None,
    project_configuration: ProjectConfiguration | None = None,
) -> tuple[GoalInfo, ...] | None:
    source_range = edit["source_range"]
    edit_start, edit_end = source_range
    delta = len(edit["replacement"]) - len(edit["original"])
    shared_deadline = deadline or time.monotonic() + timeout_seconds
    with temporary_workspace(prefix="agdaprover-target-validation-") as temporary:
        workspace = prepare_project_overlay(
            source_file,
            candidate,
            Path(temporary),
            project_configuration=project_configuration,
            timeout_seconds=_remaining(shared_deadline, "candidate overlay"),
        )
        try:
            with AgdaSession(
                executable=agda_executable,
                timeout_seconds=_remaining(shared_deadline, "original goal load"),
                deadline=shared_deadline,
                project_configuration=project_configuration,
            ) as original_session:
                original_goals = original_session.load_module(source_file)
            with AgdaSession(
                executable=agda_executable,
                timeout_seconds=_remaining(shared_deadline, "candidate goal load"),
                deadline=shared_deadline,
                project_configuration=workspace.configuration,
            ) as candidate_session:
                candidate_goals = candidate_session.load_module(workspace.source_file)
        except AgdaLoadError:
            return None
    expected: list[tuple[tuple[int, int], str]] = []
    removed = 0
    for goal in original_goals:
        start, end = goal.source_range
        if end <= edit_start:
            expected.append((goal.source_range, goal.target))
        elif start >= edit_end:
            expected.append(((start + delta, end + delta), goal.target))
        elif edit_start <= start and end <= edit_end:
            removed += 1
        else:
            return None
    expected_removed = edit.get("target_goal_count", 1)
    if edit.get("style") == "joint-clauses":
        goals_match = sorted(item[0] for item in expected) == sorted(
            goal.source_range for goal in candidate_goals
        )
    else:
        goals_match = sorted(expected) == sorted(
            (goal.source_range, goal.target) for goal in candidate_goals
        )
    if (
        not isinstance(expected_removed, int)
        or expected_removed <= 0
        or removed != expected_removed
        or not goals_match
    ):
        return None
    return candidate_goals


def prepare_project_overlay(
    source_file: Path,
    candidate: str,
    overlay_root: Path,
    *,
    project_configuration: ProjectConfiguration | None = None,
    timeout_seconds: float = float("inf"),
) -> SourceWorkspace:
    if timeout_seconds <= 0:
        raise TimeoutError("project overlay deadline exhausted")
    try:
        return prepare_source_workspace(
            source_file,
            candidate,
            overlay_root,
            configuration=project_configuration,
            timeout_seconds=timeout_seconds,
        )
    except BridgeError as error:
        if error.failure in {BridgeFailure.INVALID_REQUEST, BridgeFailure.STALE_TOKEN}:
            raise AgdaLoadError(error.diagnostic.message) from error
        if error.failure == BridgeFailure.TOOLCHAIN_ERROR:
            raise AgdaBridgeError(error.diagnostic.message) from error
        if error.failure == BridgeFailure.TIMEOUT:
            raise TimeoutError(error.diagnostic.message) from error
        if error.failure == BridgeFailure.RESOURCE_EXHAUSTED:
            raise ResourceLimitError(error.diagnostic.message) from error
        raise ValidationError(str(error)) from error


def write_project_overlay(
    source_file: Path, candidate: str, overlay_root: Path
) -> tuple[Path, tuple[tuple[Path, Path], ...]]:
    try:
        return write_source_overlay(source_file, candidate, overlay_root)
    except BridgeError as error:
        if error.failure == BridgeFailure.INVALID_REQUEST:
            # The P0 application translates load errors into an input result;
            # a Stage 1 routing error must not escape as a Python traceback.
            raise AgdaLoadError(error.diagnostic.message) from error
        raise


__all__ = [
    "FORBIDDEN_CANDIDATE_FRAGMENTS",
    "ValidationError",
    "executable_sha256",
    "file_sha256",
    "replace_goal",
    "prepare_project_overlay",
    "validate_candidate",
    "validate_partial_reconstruction",
    "validate_reconstruction",
    "validate_standalone_module",
    "write_project_overlay",
]
