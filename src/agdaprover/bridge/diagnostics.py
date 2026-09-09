"""Normalize Agda/version/process failures into stable bridge diagnostics."""

from __future__ import annotations

import hashlib
import re
from collections.abc import Iterable
from pathlib import Path

from .contracts import BridgeDiagnostic, DiagnosticPhase, SourceRange
from .versions.agda_2_8 import DecodedResponse

_ERROR_CODE = re.compile(r"(?:error|warning):\s*\[([^]]+)\]")
_BATCH_DIAGNOSTIC = re.compile(
    r"(?ms)(?:^|\n)(?P<header>[^\n]*?(?:error|warning):\s*\[(?P<code>[^]]+)\])"
    r"(?P<body>.*?)(?=\n[^\n]*?(?:error|warning):\s*\[[^]]+\]|\Z)"
)
_CAMEL = re.compile(r"(?<!^)(?=[A-Z])")

_PHASES: tuple[tuple[tuple[str, ...], DiagnosticPhase], ...] = (
    (("parse", "lexer", "character", "layout"), DiagnosticPhase.PARSING),
    (("scope", "notinscope", "ambiguous", "name"), DiagnosticPhase.SCOPE),
    (("instance",), DiagnosticPhase.INSTANCE_SEARCH),
    (("unif", "cannotapply", "mismatch", "unequal"), DiagnosticPhase.UNIFICATION),
    (("positiv",), DiagnosticPhase.POSITIVITY),
    (("coverage", "incomplete", "unreachable"), DiagnosticPhase.COVERAGE),
    (("terminat", "recursive"), DiagnosticPhase.TERMINATION),
    (("unsolved", "meta", "type", "constructor"), DiagnosticPhase.ELABORATION),
)


def _slug(value: str) -> str:
    pieces = _CAMEL.sub("-", value).replace("_", "-").lower()
    pieces = re.sub(r"[^a-z0-9]+", "-", pieces).strip("-")
    return pieces[:56] or "unknown"


def _phase(code: str) -> DiagnosticPhase:
    normalized = code.replace("-", "").lower()
    for needles, phase in _PHASES:
        if any(needle in normalized for needle in needles):
            return phase
    return DiagnosticPhase.ELABORATION


def redact_message(message: str, project_root: Path | None = None) -> str:
    result = message
    if project_root is not None:
        result = result.replace(str(project_root.resolve()), "<project>")
    home = str(Path.home())
    if home and home != "/":
        result = result.replace(home, "<home>")
    result = re.sub(
        r"/(?:private/)?(?:var/)?folders/[^\s:]+|/tmp/[^\s:]+",
        "<temporary>",
        result,
    )
    return result[:16_384]


def normalize_agda_message(
    message: str,
    *,
    raw: bytes | None = None,
    primary_range: SourceRange | None = None,
    project_root: Path | None = None,
    severity: str = "error",
) -> BridgeDiagnostic:
    matched = _ERROR_CODE.search(message)
    agda_code = matched.group(1) if matched else "UnknownError"
    return BridgeDiagnostic(
        code=f"agda-{_slug(agda_code)}",
        phase=_phase(agda_code),
        severity="warning" if severity == "warning" else "error",
        message=redact_message(message, project_root),
        primary_range=primary_range,
        retryable=False,
        raw_sha256=hashlib.sha256(
            raw if raw is not None else message.encode()
        ).hexdigest(),
        redaction="project-relative",
    )


def diagnostics_from_response(
    response: DecodedResponse,
    *,
    primary_range: SourceRange | None = None,
    project_root: Path | None = None,
) -> tuple[BridgeDiagnostic, ...]:
    result: list[BridgeDiagnostic] = []
    for event in response.events:
        info = event.value.get("info")
        if not isinstance(info, dict):
            continue
        if info.get("kind") == "IntroConstructorUnknown":
            constructors = info.get("constructors", [])
            alternatives = (
                tuple(str(item) for item in constructors)
                if isinstance(constructors, list)
                else ()
            )
            result.append(
                BridgeDiagnostic(
                    code="agda-intro-constructor-unknown",
                    phase=DiagnosticPhase.ELABORATION,
                    severity="info",
                    message="Agda found multiple applicable constructors",
                    primary_range=primary_range,
                    causes=alternatives,
                    raw_sha256=response.raw_sha256,
                )
            )
        if info.get("kind") == "IntroNotFound":
            result.append(
                BridgeDiagnostic(
                    code="agda-intro-not-found",
                    phase=DiagnosticPhase.ELABORATION,
                    severity="info",
                    message="Agda found no applicable introduction",
                    primary_range=primary_range,
                    raw_sha256=response.raw_sha256,
                )
            )
        if info.get("kind") == "Error":
            error = info.get("error", {})
            message = (
                str(error.get("message", "Agda error"))
                if isinstance(error, dict)
                else "Agda error"
            )
            result.append(
                normalize_agda_message(
                    message,
                    primary_range=primary_range,
                    project_root=project_root,
                )
            )
        if info.get("kind") == "AllGoalsWarnings":
            warnings = info.get("warnings", [])
            if isinstance(warnings, list):
                for warning in warnings:
                    message = (
                        str(warning.get("message", warning))
                        if isinstance(warning, dict)
                        else str(warning)
                    )
                    result.append(
                        normalize_agda_message(
                            message,
                            primary_range=primary_range,
                            project_root=project_root,
                            severity="warning",
                        )
                    )
    return tuple(result)


def diagnostics_from_checker_output(
    output: str, *, project_root: Path | None = None
) -> tuple[BridgeDiagnostic, ...]:
    matches = list(_BATCH_DIAGNOSTIC.finditer(output))
    if not matches and output.strip():
        return (
            BridgeDiagnostic(
                code="agda-checker-failure",
                phase=DiagnosticPhase.VALIDATION,
                severity="error",
                message=redact_message(output.strip(), project_root),
                raw_sha256=hashlib.sha256(output.encode()).hexdigest(),
                redaction="project-relative",
            ),
        )
    return tuple(
        normalize_agda_message(
            f"{match.group('header')}{match.group('body')}",
            raw=output.encode(),
            project_root=project_root,
            severity="warning" if "warning:" in match.group("header") else "error",
        )
        for match in matches
    )


def first_error(diagnostics: Iterable[BridgeDiagnostic]) -> BridgeDiagnostic | None:
    return next((item for item in diagnostics if item.severity == "error"), None)
