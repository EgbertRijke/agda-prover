"""Standalone strict validation for the public P0 result envelopes.

The JSON Schema documents are the portable contract.  This dependency-free
validator enforces the same closed top-level shape and the semantic invariants
which JSON Schema alone cannot conveniently express (most importantly that a
``verified`` result carries fresh validation and a trust report).
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any, Literal

from .contracts import EXIT_CODES, CostMetrics
from .project_configuration import ProjectConfiguration
from .resource_budget import RESOURCE_SCHEMA, ResourceLimits
from .verifier_budget import LEGACY_VERIFIER_BUDGET_SCHEMA, VERIFIER_BUDGET_SCHEMA

PROVER_SCHEMA = "agdaprover.p0.v1"
STEP_SCHEMA = "agdaprover.step.p0.v1"

_COST_FIELDS = frozenset(CostMetrics.__dataclass_fields__)
_PROVER_FIELDS = frozenset(
    {
        "schema_version",
        "task_id",
        "status",
        "source_file",
        "source_hash",
        "ranker",
        "goal",
        "joint_goals",
        "proof_term",
        "patch",
        "candidates_generated",
        "verifier_calls",
        "verifier_budget",
        "resource_budget",
        "model_calls",
        "model_elapsed_ms",
        "elapsed_ms",
        "attempts",
        "validation",
        "trust_report",
        "model_id",
        "action_model_id",
        "toolchain_id",
        "policy_profile",
        "cost",
        "impossibility_certificate",
        "search_stats",
        "policy_trace",
        "engine_selection",
        "diagnostics",
    }
)
_STEP_FIELDS = frozenset(
    {
        "schema_version",
        "task_id",
        "status",
        "source_file",
        "source_hash",
        "ranker",
        "goal",
        "action",
        "candidates_generated",
        "verifier_calls",
        "verifier_budget",
        "resource_budget",
        "model_calls",
        "model_elapsed_ms",
        "elapsed_ms",
        "model_id",
        "toolchain_id",
        "policy_profile",
        "cost",
        "attempts",
        "diagnostics",
        "engine_selection",
        "action_model_id",
        "search_stats",
    }
)
_COMMON_REQUIRED = frozenset(
    {
        "schema_version",
        "task_id",
        "status",
        "source_file",
        "source_hash",
        "ranker",
        "goal",
        "candidates_generated",
        "verifier_calls",
        "model_calls",
        "model_elapsed_ms",
        "elapsed_ms",
        "model_id",
        "toolchain_id",
        "policy_profile",
        "cost",
        "diagnostics",
    }
)


def _mapping(value: object, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or any(not isinstance(key, str) for key in value):
        raise ValueError(f"{label} must be a JSON object with string keys")
    return value


def _closed(
    value: Mapping[str, Any], *, allowed: frozenset[str], required: frozenset[str]
) -> None:
    unknown = sorted(set(value) - allowed)
    missing = sorted(required - set(value))
    if unknown:
        raise ValueError(f"unknown result fields: {', '.join(unknown)}")
    if missing:
        raise ValueError(f"missing result fields: {', '.join(missing)}")


def _string(value: object, label: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value):
        raise ValueError(f"{label} must be a nonempty string")
    return value


def _optional_string(value: object, label: str) -> None:
    if value is not None:
        _string(value, label, allow_empty=True)


def _nonnegative_number(value: object, label: str, *, integer: bool) -> None:
    expected = int if integer else (int, float)
    if isinstance(value, bool) or not isinstance(value, expected):
        raise ValueError(
            f"{label} must be a nonnegative {'integer' if integer else 'number'}"
        )
    if value < 0 or not math.isfinite(float(value)):
        raise ValueError(f"{label} must be finite and nonnegative")


def _validate_cost(value: object) -> None:
    cost = _mapping(value, "cost")
    _closed(cost, allowed=_COST_FIELDS, required=_COST_FIELDS)
    for field, number in cost.items():
        _nonnegative_number(
            number,
            f"cost.{field}",
            integer=field != "kernel_load_elapsed_ms",
        )


def _validate_common(value: Mapping[str, Any], schema: str) -> None:
    if value["schema_version"] != schema:
        raise ValueError(f"unsupported result schema: {value['schema_version']!r}")
    for field in ("task_id", "source_file", "source_hash", "ranker", "policy_profile"):
        _string(value[field], field)
    for field in ("model_id", "toolchain_id"):
        _optional_string(value[field], field)
    for field in ("candidates_generated", "verifier_calls", "model_calls"):
        _nonnegative_number(value[field], field, integer=True)
    for field in ("model_elapsed_ms", "elapsed_ms"):
        _nonnegative_number(value[field], field, integer=False)
    if value["goal"] is not None:
        _mapping(value["goal"], "goal")
    if not isinstance(value["diagnostics"], list):
        raise ValueError("diagnostics must be a list")
    for diagnostic in value["diagnostics"]:
        item = _mapping(diagnostic, "diagnostic")
        if not all(isinstance(part, str) for part in item.values()):
            raise ValueError("diagnostic values must be strings")
    _validate_cost(value["cost"])
    if "verifier_budget" in value:
        _validate_verifier_budget(value["verifier_budget"], value["status"])
    if "resource_budget" in value:
        _validate_resource_budget(value["resource_budget"], value["status"])
    if "engine_selection" in value:
        selection = _mapping(value["engine_selection"], "engine selection")
        fields = frozenset({"schema_version", "requested", "actual", "reason"})
        _closed(selection, allowed=fields, required=fields)
        if (
            selection["schema_version"] != "agdaprover.engine-selection.v1"
            or selection["requested"] not in ("auto", "haskell", "python")
            or selection["actual"] not in ("haskell", "python")
        ):
            raise ValueError("unsupported engine selection")
        _optional_string(selection["reason"], "engine selection reason")


def _validate_resource_budget(value: object, status: object) -> None:
    budget = _mapping(value, "resource_budget")
    fields = frozenset(
        {
            "schema_version",
            "limits",
            "cpu_seconds",
            "io_bytes",
            "peak_sampled_rss_bytes",
            "peak_sampled_temporary_bytes",
            "exhausted_resource",
            "accounting",
        }
    )
    _closed(budget, allowed=fields, required=fields)
    if budget["schema_version"] != RESOURCE_SCHEMA:
        raise ValueError("unsupported resource budget schema")
    limits = ResourceLimits.from_dict(budget["limits"])
    if budget["accounting"] != "sampled-owned-processes-and-caller-thread-v1":
        raise ValueError("unsupported resource accounting")
    measurements = {
        "cpu-seconds": (budget["cpu_seconds"], limits.cpu_seconds),
        "resident-bytes": (budget["peak_sampled_rss_bytes"], limits.memory_bytes),
        "io-bytes": (budget["io_bytes"], limits.io_bytes),
        "temporary-bytes": (
            budget["peak_sampled_temporary_bytes"],
            limits.temporary_bytes,
        ),
    }
    exceeded = set()
    for resource, (used, limit) in measurements.items():
        _nonnegative_number(used, resource, integer=resource != "cpu-seconds")
        if limit is not None and used > limit:
            exceeded.add(resource)
    exhausted = budget["exhausted_resource"]
    if exhausted is not None:
        if not isinstance(exhausted, str) or exhausted not in exceeded:
            raise ValueError("resource exhaustion must name an exceeded allowance")
        if status != "resource-exhausted":
            raise ValueError("exhausted resource requires resource-exhausted status")
    elif exceeded:
        raise ValueError("exceeded resource allowance must be reported")


def _validate_verifier_budget(value: object, status: object) -> None:
    budget = _mapping(value, "verifier_budget")
    fields = frozenset(
        {
            "schema_version",
            "limit",
            "used",
            "interaction_commands",
            "fresh_validations",
            "denied_calls",
        }
    )
    _closed(budget, allowed=fields, required=fields)
    if budget["schema_version"] not in (
        LEGACY_VERIFIER_BUDGET_SCHEMA,
        VERIFIER_BUDGET_SCHEMA,
    ):
        raise ValueError("unsupported verifier budget schema")
    for field in fields - {"schema_version", "limit"}:
        _nonnegative_number(budget[field], f"verifier_budget.{field}", integer=True)
    limit = budget["limit"]
    if limit is not None or budget["schema_version"] == LEGACY_VERIFIER_BUDGET_SCHEMA:
        _nonnegative_number(limit, "verifier_budget.limit", integer=True)
        if limit < 1 or budget["used"] > limit:
            raise ValueError("verifier budget must be positive and cannot be overdrawn")
    if budget["used"] != budget["interaction_commands"] + budget["fresh_validations"]:
        raise ValueError("verifier budget totals disagree")
    if budget["denied_calls"] and status != "resource-exhausted":
        raise ValueError("denied verifier requests require resource-exhausted status")


def _validate_library_checking_options(trust: Mapping[str, Any]) -> None:
    """Validate the existing library witness, without reinterpreting its flags.

    This checks a reported envelope, not Agda acceptance or dataset admission.
    Library manifests/source hashes retain per-module options; global command
    options need not impose the historical standalone without-K profile.
    """
    environment = _mapping(trust.get("checking_environment"), "checking environment")
    if environment.get("schema_version") != "agdaprover.checking-environment.v1":
        raise ValueError("unsupported checking environment schema")
    if (
        not isinstance(environment.get("root_module"), str)
        or not environment["root_module"]
    ):
        raise ValueError("checking environment lacks its root module")
    command_options = environment.get("command_options")
    if not isinstance(command_options, list):
        raise ValueError("checking environment options must be an array")
    ProjectConfiguration(options=tuple(command_options))
    libraries = environment.get("libraries")
    if not isinstance(libraries, list) or not libraries:
        raise ValueError("checking environment lacks pinned libraries")
    names = set()
    for raw in libraries:
        library = _mapping(raw, "library")
        name, digest, includes = (
            library.get("name"),
            library.get("manifest_sha256"),
            library.get("includes"),
        )
        if (
            not isinstance(name, str)
            or not name
            or name in names
            or not isinstance(digest, str)
            or len(digest) != 64
            or any(c not in "0123456789abcdef" for c in digest)
            or not isinstance(includes, list)
            or not includes
            or not all(isinstance(item, str) and item for item in includes)
        ):
            raise ValueError("malformed pinned library witness")
        names.add(name)
    sources = _mapping(environment.get("sources"), "checking sources")
    for raw in sources.values():
        source = _mapping(raw, "checking source")
        digest = source.get("sha256")
        owner = source.get("library")
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or any(c not in "0123456789abcdef" for c in digest)
            or (
                owner is not None and (not isinstance(owner, str) or owner not in names)
            )
        ):
            raise ValueError("malformed checking source witness")
    options = trust["options"]
    command = trust.get("checker_command")
    if (
        trust.get("sandbox_profile")
        != "isolated-overlay-pinned-libraries-process-group-v1"
        or not isinstance(command, list)
        or len(command) < 3
        or not all(isinstance(item, str) and item for item in command)
        or command[1:-1] != options
        or (command_options and options[-len(command_options) :] != command_options)
    ):
        raise ValueError("checking environment disagrees with the checker command")
    transport = list(options[: -len(command_options)] if command_options else options)
    if transport and transport[-1] == "--safe":
        transport.pop()  # The validation policy may strengthen global options.
    if (
        len(transport) < 5
        or transport[0] != "--no-default-libraries"
        or not transport[1].startswith("--library-file=")
        or not transport[1].removeprefix("--library-file=")
        or transport[2] != "--ignore-interfaces"
        or len(transport[3:]) % 2
        or any(
            transport[i] != "-i" or not transport[i + 1]
            for i in range(3, len(transport), 2)
        )
    ):
        raise ValueError("unreported options in the library checker command")


def _validate_checked_evidence(result: Mapping[str, Any], label: str) -> None:
    validation = _mapping(result["validation"], "validation")
    trust = _mapping(result["trust_report"], "trust_report")
    if (
        validation.get("checked") is not True
        or validation.get("fresh_process") is not True
        or validation.get("timed_out") is not False
    ):
        raise ValueError(f"{label} result lacks successful fresh validation")
    options = trust.get("options")
    if (
        trust.get("fresh_process") is not True
        or trust.get("offline") is not True
        or not isinstance(options, list)
        or not all(isinstance(option, str) for option in options)
    ):
        raise ValueError(f"{label} result lacks a strict offline trust report")
    if "checking_environment" in trust:
        _validate_library_checking_options(trust)
    elif not {"--without-K", "--exact-split"}.issubset(options):
        raise ValueError(f"{label} result lacks a strict offline trust report")
    full_module = (
        type(validation.get("exit_status")) is int
        and type(trust.get("checker_exit_status")) is int
        and validation.get("exit_status") == 0
        and trust.get("checker_exit_status") == 0
    )
    supplemental = trust.get("supplemental_checker_command")
    scope = validation.get("validation_scope")
    prefix = validation.get("prefix_validation")
    strict_prefix = (
        isinstance(prefix, Mapping)
        and prefix.get("schema_version") == "agdaprover.prefix-validation.v1"
        and prefix.get("status") == "verified"
        and isinstance(prefix.get("parser"), Mapping)
        and prefix["parser"].get("status") == "parsed"
        and isinstance(prefix.get("omitted_declarations"), list)
        and isinstance(prefix.get("validation"), Mapping)
        and prefix["validation"].get("checked") is True
        and prefix["validation"].get("fresh_process") is True
        and prefix["validation"].get("timed_out") is False
        and type(prefix["validation"].get("exit_status")) is int
        and prefix["validation"].get("exit_status") == 0
        and isinstance(prefix.get("trust_report"), Mapping)
        and type(prefix["trust_report"].get("checker_exit_status")) is int
        and prefix["trust_report"].get("checker_exit_status") == 0
        and prefix["trust_report"].get("fresh_process") is True
        and prefix["trust_report"].get("offline") is True
        and prefix["trust_report"].get("options") == options
        and prefix["trust_report"] == trust.get("prefix_validation")
    )
    target_definition = bool(
        (
            (scope == "target-definition" and prefix is None)
            or (scope in {"target-definition", "target-prefix"} and strict_prefix)
        )
        and trust.get("validation_scope") == scope
        and validation.get("exit_status") == trust.get("checker_exit_status")
        and isinstance(validation.get("acceptance_basis"), str)
        and validation.get("acceptance_basis")
        and isinstance(validation.get("remaining_open_goals"), list)
        and isinstance(supplemental, list)
        and "--interaction-json" in supplemental
    )
    if not (full_module or target_definition):
        raise ValueError(f"{label} result lacks an accepted fresh validation scope")


def validate_prover_result(value: object) -> Mapping[str, Any]:
    result = _mapping(value, "prover result")
    required = _COMMON_REQUIRED | frozenset(
        {
            "joint_goals",
            "proof_term",
            "patch",
            "validation",
            "trust_report",
            "action_model_id",
            "impossibility_certificate",
            "search_stats",
        }
    )
    _closed(result, allowed=_PROVER_FIELDS, required=required)
    _validate_common(result, PROVER_SCHEMA)
    status = result["status"]
    if status not in EXIT_CODES:
        raise ValueError(f"unsupported prover status: {status!r}")
    if not isinstance(result["joint_goals"], list):
        raise ValueError("joint_goals must be a list")
    for goal in result["joint_goals"]:
        _mapping(goal, "joint goal")
    _optional_string(result["proof_term"], "proof_term")
    _optional_string(result["action_model_id"], "action_model_id")
    for field in ("attempts", "policy_trace"):
        if field not in result:
            continue
        if not isinstance(result[field], list):
            raise ValueError(f"{field} must be a list")
        for item in result[field]:
            _mapping(item, field[:-1] if field.endswith("s") else field)
    for field in (
        "patch",
        "validation",
        "trust_report",
        "impossibility_certificate",
        "search_stats",
    ):
        if result[field] is not None:
            _mapping(result[field], field)
    if status == "verified":
        if not result["proof_term"] or result["patch"] is None:
            raise ValueError("verified result lacks proof term or patch")
        _validate_checked_evidence(result, "verified")
    if status == "impossible":
        if result["impossibility_certificate"] is None:
            raise ValueError("impossible result lacks checked certificate evidence")
        _validate_checked_evidence(result, "impossible")
    return result


def validate_step_result(value: object) -> Mapping[str, Any]:
    result = _mapping(value, "step result")
    required = _COMMON_REQUIRED | frozenset({"action"})
    _closed(result, allowed=_STEP_FIELDS, required=required)
    _validate_common(result, STEP_SCHEMA)
    allowed = {
        "accepted-step",
        "unsolved",
        "resource-exhausted",
        "invalid-task",
        "toolchain-error",
        "internal-error",
    }
    if result["status"] not in allowed:
        raise ValueError(f"unsupported step status: {result['status']!r}")
    if result["action"] is not None:
        _mapping(result["action"], "action")
    _optional_string(result.get("action_model_id"), "action_model_id")
    if result.get("search_stats") is not None:
        _mapping(result["search_stats"], "search_stats")
    if "attempts" in result:
        if not isinstance(result["attempts"], list):
            raise ValueError("attempts must be a list")
        for attempt in result["attempts"]:
            _mapping(attempt, "attempt")
    if result["status"] == "accepted-step" and result["action"] is None:
        raise ValueError("accepted-step result lacks an action")
    return result


def validate_result(
    value: object, *, kind: Literal["auto", "prover", "step"] = "auto"
) -> Mapping[str, Any]:
    if kind == "prover":
        return validate_prover_result(value)
    if kind == "step":
        return validate_step_result(value)
    mapping = _mapping(value, "result")
    if mapping.get("schema_version") == PROVER_SCHEMA:
        return validate_prover_result(mapping)
    if mapping.get("schema_version") == STEP_SCHEMA:
        return validate_step_result(mapping)
    raise ValueError(f"unsupported result schema: {mapping.get('schema_version')!r}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, nargs="?", help="JSON file (default: stdin)")
    parser.add_argument("--kind", choices=("auto", "prover", "step"), default="auto")
    arguments = parser.parse_args(argv)
    try:
        raw = (
            arguments.path.read_text()
            if arguments.path is not None
            else sys.stdin.read()
        )
        validate_result(json.loads(raw), kind=arguments.kind)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
