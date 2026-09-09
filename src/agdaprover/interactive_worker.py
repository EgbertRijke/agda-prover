"""Private worker entry point for the interactive run controller."""

from __future__ import annotations

import argparse
import json
import os
import signal
from pathlib import Path

from .application import default_application
from .contracts import TaskSpec
from .principal_variation import AtomicPrincipalVariationPublisher
from .resource_budget import ResourceLimits


def _write_result(path: Path, value: dict[str, object]) -> None:
    encoded = (json.dumps(value, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_bytes(encoded)
    os.replace(temporary, path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("source", type=Path)
    parser.add_argument("--variation-file", type=Path, required=True)
    parser.add_argument("--result-file", type=Path, required=True)
    goal = parser.add_mutually_exclusive_group()
    goal.add_argument("--goal", type=int)
    goal.add_argument("--goal-position", type=int)
    parser.add_argument("--max-candidates", type=int, required=True)
    parser.add_argument("--max-verifier-calls", type=int)
    parser.add_argument("--max-term-size", type=int, required=True)
    parser.add_argument("--max-depth", type=int)
    parser.add_argument("--timeout", type=float)
    parser.add_argument("--cpu-seconds", type=float)
    for name in ("memory_bytes", "io_bytes", "temporary_bytes"):
        parser.add_argument(
            "--" + name.replace("_", "-"),
            type=int,
            default=getattr(ResourceLimits(), name),
        )
    parser.add_argument("--ranker", choices=("symbolic", "nnue"), required=True)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--action-model", type=Path)
    arguments = parser.parse_args(argv)
    task = TaskSpec(
        source_file=arguments.source,
        goal_id=arguments.goal,
        goal_position=arguments.goal_position,
        max_candidates=arguments.max_candidates,
        max_verifier_calls=arguments.max_verifier_calls,
        max_term_size=arguments.max_term_size,
        max_depth=arguments.max_depth,
        timeout_seconds=arguments.timeout,
        resources=ResourceLimits(
            arguments.cpu_seconds,
            arguments.memory_bytes,
            arguments.io_bytes,
            arguments.temporary_bytes,
        ),
        ranker=arguments.ranker,
        model_path=arguments.model,
        action_model_path=arguments.action_model,
    )

    def stop_at_safe_boundary(_signal_number: int, _frame: object) -> None:
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, stop_at_safe_boundary)
    try:
        result = default_application.prove_prefix(
            task,
            progress_observer=AtomicPrincipalVariationPublisher(
                arguments.variation_file
            ),
        )
    except KeyboardInterrupt:
        return 130
    _write_result(arguments.result_file, result.to_dict())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
