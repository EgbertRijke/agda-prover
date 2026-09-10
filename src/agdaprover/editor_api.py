"""Versioned, editor-neutral request and response contracts.

Editors invoke one local process per request and cancel by terminating that
process.  This deliberately keeps editor SDKs outside the prover while giving
Emacs, VS Code, and other clients one stable protocol.
"""

from __future__ import annotations

import hashlib
import math
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from .project import agda_source_suffix
from .project_configuration import ProjectConfiguration
from .resource_budget import ResourceLimits
from .search_profiles import search_profile

EDITOR_REQUEST_SCHEMA = "agdaprover.editor.request.v1"
EDITOR_RESPONSE_SCHEMA = "agdaprover.editor.response.v1"
EditorOperation = Literal["inspect", "prove", "prove-prefix", "step"]
_REQUEST_KEYS = frozenset(
    {
        "schema_version",
        "request_id",
        "operation",
        "source_file",
        "source_sha256",
        "goal_position",
        "ranker",
        "model",
        "action_model",
        "max_candidates",
        "max_verifier_calls",
        "max_term_size",
        "max_depth",
        "timeout_seconds",
        "resources",
        "project_configuration",
        "search_profile",
    }
)


def source_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@dataclass(frozen=True)
class EditorRequest:
    request_id: str
    operation: EditorOperation
    source_file: Path
    source_sha256: str
    goal_position: int
    ranker: Literal["symbolic", "nnue"] = "symbolic"
    model: Path | None = None
    action_model: Path | None = None
    max_candidates: int = 500
    max_term_size: int = 8
    max_depth: int | None = None
    timeout_seconds: float | None = None
    max_verifier_calls: int | None = None
    resources: ResourceLimits = ResourceLimits()
    project_configuration: ProjectConfiguration | None = None

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> EditorRequest:
        unknown = set(value) - _REQUEST_KEYS
        if unknown:
            raise ValueError(f"unknown editor request fields: {sorted(unknown)!r}")
        if value.get("schema_version") != EDITOR_REQUEST_SCHEMA:
            raise ValueError("unsupported editor request schema")
        request_id = value.get("request_id")
        if not isinstance(request_id, str) or not re.fullmatch(
            r"[A-Za-z0-9._:-]{1,128}", request_id
        ):
            raise ValueError("editor request_id is malformed")
        operation = value.get("operation")
        if operation not in {"inspect", "prove", "prove-prefix", "step"}:
            raise ValueError("unsupported editor operation")
        profile = search_profile(value.get("search_profile", "standard"))
        if operation == "inspect" and "search_profile" in value:
            raise ValueError("search_profile is a search-only option")
        source_value = value.get("source_file")
        if not isinstance(source_value, str) or not source_value:
            raise ValueError("editor source_file must be nonempty text")
        source = Path(source_value).expanduser().resolve()
        if agda_source_suffix(source) is None or not source.is_file():
            raise ValueError("editor source_file must be an existing Agda source")
        digest = value.get("source_sha256")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError("editor source_sha256 is malformed")
        if source_sha256(source) != digest:
            raise ValueError("editor source changed before request execution")
        position = value.get("goal_position")
        if type(position) is not int or position < 1:
            raise ValueError("editor goal_position must be a positive integer")
        ranker = value.get("ranker", "symbolic")
        if ranker not in {"symbolic", "nnue"}:
            raise ValueError("unsupported editor ranker")

        def positive_int(name: str, default: int) -> int:
            item = value.get(name, default)
            if type(item) is not int or item < 1:
                raise ValueError(f"editor {name} must be a positive integer")
            return item

        max_depth = value.get("max_depth")
        max_verifier_calls = value.get("max_verifier_calls")
        if max_verifier_calls is not None:
            max_verifier_calls = positive_int("max_verifier_calls", 1)
            if operation == "inspect":
                raise ValueError("max_verifier_calls is a search-only option")
        if max_depth is not None and (type(max_depth) is not int or max_depth < 1):
            raise ValueError("editor max_depth must be null or a positive integer")
        timeout = value.get("timeout_seconds")
        if timeout is not None and (
            not isinstance(timeout, (int, float))
            or isinstance(timeout, bool)
            or not math.isfinite(float(timeout))
            or float(timeout) <= 0
        ):
            raise ValueError("editor timeout_seconds must be null or positive")

        def optional_path(name: str) -> Path | None:
            item = value.get(name)
            if item is None:
                return None
            if not isinstance(item, str) or not item:
                raise ValueError(f"editor {name} must be a path or null")
            return Path(item).expanduser().resolve()

        return cls(
            request_id=request_id,
            operation=operation,
            source_file=source,
            source_sha256=digest,
            goal_position=position,
            ranker=ranker,
            model=optional_path("model"),
            action_model=optional_path("action_model"),
            max_candidates=positive_int("max_candidates", profile.max_candidates),
            max_term_size=positive_int("max_term_size", 8),
            max_depth=max_depth,
            max_verifier_calls=max_verifier_calls,
            timeout_seconds=float(timeout) if timeout is not None else None,
            resources=ResourceLimits.from_dict(value["resources"])
            if "resources" in value
            else ResourceLimits(),
            project_configuration=ProjectConfiguration.from_dict(
                value["project_configuration"]
            )
            if "project_configuration" in value
            else None,
        )

    def to_namespace_values(self) -> dict[str, Any]:
        return {
            "source": self.source_file,
            "goal": None,
            "goal_position": self.goal_position,
            "ranker": self.ranker,
            "model": self.model,
            "action_model": self.action_model,
            "max_candidates": self.max_candidates,
            "max_verifier_calls": self.max_verifier_calls,
            "max_term_size": self.max_term_size,
            "max_depth": self.max_depth,
            "timeout": self.timeout_seconds,
            "trace": None,
            "cpu_seconds": self.resources.cpu_seconds,
            "memory_bytes": self.resources.memory_bytes,
            "io_bytes": self.resources.io_bytes,
            "temporary_bytes": self.resources.temporary_bytes,
            "project_configuration": self.project_configuration,
        }


def response_envelope(
    request: EditorRequest,
    *,
    exit_code: int,
    result: Mapping[str, Any],
) -> dict[str, Any]:
    if source_sha256(request.source_file) != request.source_sha256:
        exit_code = 4
        result = {
            "status": "invalid-task",
            "diagnostic": "editor source changed during request execution",
        }
    return {
        "schema_version": EDITOR_RESPONSE_SCHEMA,
        "request_id": request.request_id,
        "operation": request.operation,
        "source_file": str(request.source_file),
        "source_sha256": request.source_sha256,
        "exit_code": exit_code,
        "result": dict(result),
    }


def error_envelope(message: str) -> dict[str, Any]:
    return {
        "schema_version": EDITOR_RESPONSE_SCHEMA,
        "request_id": None,
        "operation": None,
        "source_file": None,
        "source_sha256": None,
        "exit_code": 4,
        "result": {"status": "invalid-task", "diagnostic": message},
    }
