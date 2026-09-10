"""Command-line interface for the AgdaProver P0 vertical slice."""

from __future__ import annotations

import argparse
import json
import signal
import sys
import tempfile
from argparse import Namespace
from pathlib import Path
from types import FrameType
from typing import Any, Literal, cast

from .application import (
    default_application,
    inspect_source,
)
from .contracts import EXIT_CODES, Status, TaskSpec
from .editor_api import EditorRequest, error_envelope, response_envelope
from .interactive import launch_interactive_run, serve_interactive
from .offline import offline_audit
from .project_configuration import ProjectConfiguration
from .resource_budget import ResourceLimits
from .search_profiles import search_profile


def add_project_options(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--agda", help="Agda executable (default: agda)")
    parser.add_argument(
        "--library-file",
        type=Path,
        help="explicit Agda library registry; ambient defaults are never used",
    )
    checking_options = parser.add_mutually_exclusive_group()
    checking_options.add_argument(
        "--agda-option",
        action="append",
        help="global checking option, repeat as --agda-option=--FLAG; replaces default global options",
    )
    checking_options.add_argument(
        "--no-default-agda-options",
        dest="agda_option",
        action="store_const",
        const=[],
        help="supply no global checking options; retain library and file options",
    )


def project_configuration_from_arguments(
    arguments: argparse.Namespace,
) -> ProjectConfiguration | None:
    supplied = getattr(arguments, "project_configuration", None)
    if supplied is not None:
        return supplied
    executable = getattr(arguments, "agda", None)
    library = getattr(arguments, "library_file", None)
    options = getattr(arguments, "agda_option", None)
    if executable is None and library is None and options is None:
        return None
    return ProjectConfiguration(
        executable or "agda",
        library,
        tuple(options) if options is not None else ProjectConfiguration().options,
    )


def add_search_options(
    parser: argparse.ArgumentParser,
    *,
    allow_model: bool = True,
    joint_selection: bool = False,
) -> None:
    add_project_options(parser)
    goal = parser.add_mutually_exclusive_group()
    goal.add_argument("--goal", type=int)
    goal.add_argument(
        "--goal-position",
        type=int,
        help=(
            "one-based cursor position; select through its containing goal, or "
            "all goals when it is outside every goal"
            if joint_selection
            else "one-based position contained in the target open goal"
        ),
    )
    profiles = parser.add_mutually_exclusive_group()
    profiles.add_argument(
        "--search-profile",
        choices=("standard", "deep"),
        default="standard",
        help="effort preset: standard (500 actions) or deep (8000 actions)",
    )
    profiles.add_argument(
        "--deep",
        dest="search_profile",
        action="store_const",
        const="deep",
        help="use the deep-search effort preset; explicit limits still take precedence",
    )
    parser.add_argument(
        "--max-candidates",
        type=int,
        help="explicit whole-run action allowance, overriding the search profile",
    )
    parser.add_argument(
        "--max-verifier-calls",
        type=int,
        help="optional total Agda-command/fresh-validation cap (no implicit cap)",
    )
    parser.add_argument("--max-term-size", type=int, default=8)
    parser.add_argument(
        "--cpu-seconds",
        type=float,
        help="aggregate CPU allowance; includes retries and validation",
    )
    for name in ("memory_bytes", "io_bytes", "temporary_bytes"):
        parser.add_argument(
            "--" + name.replace("_", "-"),
            type=int,
            default=getattr(ResourceLimits(), name),
        )
    parser.add_argument(
        "--max-depth",
        type=int,
        help="optional hard proof-search depth (a reached bound is resource exhaustion)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="optional hard wall-time limit in seconds (default: no wall limit)",
    )
    if allow_model:
        parser.add_argument(
            "--ranker", choices=("symbolic", "nnue"), default="symbolic"
        )
        parser.add_argument("--model", type=Path)
        parser.add_argument(
            "--action-model",
            type=Path,
            help="optional role-checked NNUE model for this command's decisions",
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="agdaprover", description="Local-first experimental Agda proof search"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    inspect = subparsers.add_parser("inspect", help="inspect structured Agda goals")
    inspect.add_argument(
        "source", type=Path, metavar="SOURCE", help="an .agda or .lagda.md source file"
    )
    inspect_goal = inspect.add_mutually_exclusive_group()
    add_project_options(inspect)
    inspect_goal.add_argument("--goal", type=int)
    inspect_goal.add_argument("--goal-position", type=int)
    inspect.add_argument(
        "--timeout",
        type=float,
        default=None,
        help="optional hard wall-time limit in seconds (default: no wall limit)",
    )

    prove_parser = subparsers.add_parser("prove", help="search for one proof")
    prove_parser.add_argument(
        "source", type=Path, metavar="SOURCE", help="an .agda or .lagda.md source file"
    )
    add_search_options(prove_parser)
    prove_parser.add_argument(
        "--trace", type=Path, help="write candidate attempts as JSON"
    )

    prove_prefix = subparsers.add_parser(
        "prove-prefix",
        help=(
            "jointly solve through the goal containing the requested position, "
            "or all open goals when outside a goal"
        ),
    )
    prove_prefix.add_argument(
        "source", type=Path, metavar="SOURCE", help="an .agda or .lagda.md source file"
    )
    add_search_options(prove_prefix, joint_selection=True)
    prove_prefix.add_argument(
        "--trace", type=Path, help="write joint source-state statistics as JSON"
    )

    interactive = subparsers.add_parser(
        "interactive",
        help=(
            "run a controllable joint search through the goal containing the "
            "requested position, or all goals when outside a goal"
        ),
    )
    interactive.add_argument(
        "source", type=Path, metavar="SOURCE", help="an .agda or .lagda.md source file"
    )
    add_search_options(interactive, joint_selection=True)

    step = subparsers.add_parser(
        "step", help="suggest one Agda-accepted refinement action"
    )
    step.add_argument(
        "source", type=Path, metavar="SOURCE", help="an .agda or .lagda.md source file"
    )
    add_search_options(step)
    step.add_argument("--trace", type=Path, help="write action attempts as JSON")

    doctor = subparsers.add_parser("doctor", help="audit the local runtime")
    doctor.add_argument(
        "--offline-audit",
        action="store_true",
        required=True,
        help="fail if a runtime module imports a network-capable client",
    )
    subparsers.add_parser(
        "editor-api",
        help="serve one versioned editor request from standard input",
    )
    return parser


def _editor_api() -> tuple[int, dict[str, Any]]:
    try:
        raw = sys.stdin.read(1_048_577)
        if len(raw.encode("utf-8")) > 1_048_576:
            raise ValueError("editor request exceeds the 1 MiB protocol limit")
        value = json.loads(raw)
        if not isinstance(value, dict):
            raise ValueError("editor request must be one JSON object")
        request = EditorRequest.from_dict(value)
        arguments = Namespace(**request.to_namespace_values())
        handlers = {
            "inspect": _inspect,
            "prove": _prove,
            "prove-prefix": _prove_prefix,
            "step": _step,
        }
        exit_code, result = handlers[request.operation](arguments)
        return exit_code, response_envelope(request, exit_code=exit_code, result=result)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        return 4, error_envelope(str(error))


def task_from_arguments(
    arguments: argparse.Namespace,
    source: Path,
    ranker: Literal["symbolic", "nnue"],
    model: Path | None,
) -> TaskSpec:
    profile = search_profile(getattr(arguments, "search_profile", "standard"))
    return TaskSpec(
        source_file=source,
        goal_id=arguments.goal,
        goal_position=arguments.goal_position,
        max_candidates=arguments.max_candidates
        if arguments.max_candidates is not None
        else profile.max_candidates,
        max_verifier_calls=getattr(arguments, "max_verifier_calls", None),
        max_term_size=arguments.max_term_size,
        resources=ResourceLimits(
            arguments.cpu_seconds,
            arguments.memory_bytes,
            arguments.io_bytes,
            arguments.temporary_bytes,
        ),
        max_depth=arguments.max_depth,
        timeout_seconds=arguments.timeout,
        ranker=ranker,
        model_path=model,
        action_model_path=getattr(arguments, "action_model", None),
        offline=True,
        project_configuration=project_configuration_from_arguments(arguments),
    )


def _inspect(arguments: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    outcome = inspect_source(
        arguments.source,
        goal_id=arguments.goal,
        goal_position=arguments.goal_position,
        timeout_seconds=arguments.timeout,
        project_configuration=project_configuration_from_arguments(arguments),
    )
    return outcome.exit_code, outcome.payload


def _prove(arguments: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    result = default_application.prove(
        task_from_arguments(
            arguments, arguments.source, arguments.ranker, arguments.model
        )
    )
    if arguments.trace:
        arguments.trace.parent.mkdir(parents=True, exist_ok=True)
        arguments.trace.write_text(
            json.dumps(
                result.to_dict(include_attempts=True), indent=2, ensure_ascii=False
            )
            + "\n"
        )
    return EXIT_CODES[result.status], result.to_dict()


def _prove_prefix(arguments: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    result = default_application.prove_prefix(
        task_from_arguments(
            arguments, arguments.source, arguments.ranker, arguments.model
        )
    )
    output = result.to_dict()
    if arguments.trace:
        arguments.trace.parent.mkdir(parents=True, exist_ok=True)
        arguments.trace.write_text(
            json.dumps(output, indent=2, ensure_ascii=False) + "\n"
        )
    return EXIT_CODES[result.status], output


def _step(arguments: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    result = default_application.step(
        task_from_arguments(
            arguments, arguments.source, arguments.ranker, arguments.model
        )
    )
    if arguments.trace:
        arguments.trace.parent.mkdir(parents=True, exist_ok=True)
        arguments.trace.write_text(
            json.dumps(
                result.to_dict(include_attempts=True), indent=2, ensure_ascii=False
            )
            + "\n"
        )
    exit_code = (
        0
        if result.status == "accepted-step"
        else EXIT_CODES[cast(Status, result.status)]
    )
    return exit_code, result.to_dict()


def _interactive(arguments: argparse.Namespace) -> int:
    task = task_from_arguments(
        arguments, arguments.source, arguments.ranker, arguments.model
    )
    with tempfile.TemporaryDirectory(prefix="agdaprover-interactive-") as temporary:
        root = Path(temporary)
        controller = launch_interactive_run(
            task,
            variation_path=root / "principal-variation.json",
            result_path=root / "result.json",
        )
        return serve_interactive(controller, sys.stdin, sys.stdout)


def _doctor(_arguments: argparse.Namespace) -> tuple[int, dict[str, Any]]:
    report = offline_audit()
    return (0 if report["offline_capable"] else 5), {
        "schema_version": "agdaprover.offline-audit.p0.v1",
        **report,
    }


def _interrupt_cli(_signal_number: int, _frame: FrameType | None) -> None:
    """Unwind active bridge context managers on editor/user interruption."""

    raise KeyboardInterrupt


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    arguments = parser.parse_args(argv)
    handled_signals = tuple(
        candidate
        for name in ("SIGINT", "SIGTERM", "SIGHUP")
        if (candidate := getattr(signal, name, None)) is not None
    )
    previous_handlers = {
        handled: signal.getsignal(handled) for handled in handled_signals
    }
    for handled in handled_signals:
        signal.signal(handled, _interrupt_cli)
    try:
        if arguments.command == "inspect":
            exit_code, output = _inspect(arguments)
        elif arguments.command == "prove":
            exit_code, output = _prove(arguments)
        elif arguments.command == "prove-prefix":
            exit_code, output = _prove_prefix(arguments)
        elif arguments.command == "step":
            exit_code, output = _step(arguments)
        elif arguments.command == "interactive":
            return _interactive(arguments)
        elif arguments.command == "doctor":
            exit_code, output = _doctor(arguments)
        elif arguments.command == "editor-api":
            exit_code, output = _editor_api()
        else:
            parser.error(f"unknown command: {arguments.command}")
    except KeyboardInterrupt:
        output = {
            "schema_version": "agdaprover.cancelled.v1",
            "status": "cancelled",
        }
        exit_code = 130
    finally:
        for handled, previous in previous_handlers.items():
            signal.signal(handled, previous)
    print(json.dumps(output, indent=2, sort_keys=True, ensure_ascii=False))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
