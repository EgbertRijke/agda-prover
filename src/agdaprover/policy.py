"""Structural source-patch policy independent of search and Agda transport."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass

from .bridge.contracts import BridgeDiagnostic, DiagnosticPhase
from .bridge.operations import PolicyProfile, SourcePatch
from .bridge.project import ResolvedProject
from .bridge.source_text import mask_agda_source

_IMPORT = re.compile(r"(?m)^\s*(?:open\s+)?import\s+[^\n]+$")
_MODULE = re.compile(r"(?m)^\s*module\s+[^\n]+$")
_OPTIONS = re.compile(r"\{-#\s*OPTIONS\b[\s\S]*?#-\}")
_DANGEROUS_PRAGMA = re.compile(
    r"\{-#\s*(?:TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|"
    r"NO_UNIVERSE_CHECK|COMPILE|FOREIGN|BUILTIN|REWRITE)\b",
    re.IGNORECASE,
)
_DANGEROUS_DECLARATION = re.compile(r"(?m)^\s*(?:postulate|primitive)\b", re.IGNORECASE)
_ASSUMPTION_DECLARATION = re.compile(
    r"(?m)^\s*(?P<kind>postulate|primitive)\s+(?P<name>\S+)", re.IGNORECASE
)
_INCOMPLETE_CHECKING_OPTIONS = frozenset(
    {
        "--allow-unsolved-metas",
        "--allow-incomplete-matches",
    }
)
_CHECKING_WAIVERS = _INCOMPLETE_CHECKING_OPTIONS | frozenset(
    {
        "--no-termination-check",
        "--no-positivity-check",
        "--no-universe-check",
    }
)


@dataclass(frozen=True)
class PolicyReport:
    accepted: bool
    candidate: str | None
    diagnostics: tuple[BridgeDiagnostic, ...]
    original_sha256: str
    candidate_sha256: str | None
    admitted_assumptions: tuple[str, ...] = ()


def _diagnostic(code: str, message: str) -> BridgeDiagnostic:
    return BridgeDiagnostic(
        code=code,
        phase=DiagnosticPhase.POLICY,
        severity="error",
        message=message,
        redaction="project-relative",
    )


def _apply_edits(source: str, patch: SourcePatch) -> str:
    candidate = source
    for edit in sorted(
        patch.edits, key=lambda item: item.source_range.start, reverse=True
    ):
        start = edit.source_range.start
        end = edit.source_range.end
        if start <= 0 or end <= start or end - 1 > len(candidate):
            raise ValueError("authorized source edit range is out of bounds")
        if candidate[start - 1 : end - 1] != edit.original:
            raise ValueError("source changed before the authorized patch was applied")
        candidate = candidate[: start - 1] + edit.replacement + candidate[end - 1 :]
    return candidate


def _surface(source: str, pattern: re.Pattern[str]) -> tuple[str, ...]:
    return tuple(" ".join(match.group(0).split()) for match in pattern.finditer(source))


def _type_signatures(source: str) -> tuple[tuple[str, str], ...]:
    signature = re.compile(r"(?m)^(?P<name>\S+)[ \t]*:")
    result: list[tuple[str, str]] = []
    ignored = {
        "constructor",
        "data",
        "field",
        "infix",
        "infixl",
        "infixr",
        "module",
        "open",
        "postulate",
        "primitive",
        "record",
    }
    for match in signature.finditer(source):
        name = match.group("name")
        if name in ignored:
            continue
        # A mixfix definition can start with its first pattern rather than the
        # declared name (`refl ∙ q = q`). Comparing text up to a name-matched
        # clause therefore made a safe hole-to-case-clause patch appear to
        # alter the preceding signature. Agda's top-level layout gives a
        # simpler boundary: continuation lines are indented, while the first
        # definition/declaration line begins in column zero.
        line_end = source.find("\n", match.end())
        end = len(source) if line_end < 0 else line_end + 1
        while end < len(source):
            following_end = source.find("\n", end)
            if following_end < 0:
                following_end = len(source)
            line = source[end:following_end]
            if line and not line[0].isspace():
                break
            end = min(len(source), following_end + 1)
        result.append((name, " ".join(source[match.start() : end].split())))
    return tuple(result)


def inspect_patch(
    project: ResolvedProject, patch: SourcePatch, profile: PolicyProfile
) -> PolicyReport:
    try:
        original_path = project.source_for(patch.module_id)
    except KeyError:
        diagnostic = _diagnostic(
            "patch-module-mismatch", "patch module is not in the resolved project"
        )
        return PolicyReport(False, None, (diagnostic,), "0" * 64, None)
    original = original_path.read_text()
    original_sha = hashlib.sha256(original.encode()).hexdigest()
    diagnostics: list[BridgeDiagnostic] = []
    if patch.environment_id != project.environment_id:
        diagnostics.append(
            _diagnostic(
                "patch-environment-mismatch", "patch belongs to another environment"
            )
        )
    if patch.source_revision != project.source_revision:
        diagnostics.append(
            _diagnostic(
                "patch-revision-mismatch", "patch belongs to a stale source revision"
            )
        )
    try:
        candidate = _apply_edits(original, patch)
    except ValueError as error:
        diagnostics.append(_diagnostic("patch-application-rejected", str(error)))
        return PolicyReport(False, None, tuple(diagnostics), original_sha, None)

    original_code = mask_agda_source(original, original_path)
    candidate_code = mask_agda_source(candidate, original_path)
    if _surface(original_code, _MODULE) != _surface(candidate_code, _MODULE):
        diagnostics.append(
            _diagnostic(
                "module-header-changed", "authorized patch changed the module header"
            )
        )
    if not profile.allow_import_changes and _surface(
        original_code, _IMPORT
    ) != _surface(candidate_code, _IMPORT):
        diagnostics.append(
            _diagnostic("imports-changed", "policy forbids changing imports")
        )
    if not profile.allow_unsafe_options and _surface(
        original_code, _OPTIONS
    ) != _surface(candidate_code, _OPTIONS):
        diagnostics.append(
            _diagnostic("options-changed", "policy forbids changing OPTIONS pragmas")
        )
    if _type_signatures(original_code) != _type_signatures(candidate_code):
        diagnostics.append(
            _diagnostic(
                "public-statement-changed",
                "authorized patch changed a top-level type signature",
            )
        )
    if not profile.allow_new_postulates:
        old_postulates = len(_DANGEROUS_DECLARATION.findall(original_code))
        new_postulates = len(_DANGEROUS_DECLARATION.findall(candidate_code))
        if new_postulates > old_postulates:
            diagnostics.append(
                _diagnostic(
                    "trust-assumption-added",
                    "policy forbids introducing postulate or primitive declarations",
                )
            )
    if not profile.allow_unsafe_options:
        old_pragmas = len(_DANGEROUS_PRAGMA.findall(original_code))
        new_pragmas = len(_DANGEROUS_PRAGMA.findall(candidate_code))
        if new_pragmas > old_pragmas:
            diagnostics.append(
                _diagnostic(
                    "unsafe-pragma-added",
                    "policy forbids introducing trust-changing pragmas",
                )
            )
    candidate_sha = hashlib.sha256(candidate.encode()).hexdigest()
    assumptions: list[str] = []
    checking_options = set(project.command_options)
    for library in project.libraries:
        checking_options.update(library.flags)
    for source in project.sources:
        text = (
            candidate if source.module == patch.module_id else source.path.read_text()
        )
        code = mask_agda_source(text, source.path)
        for pragma in _OPTIONS.findall(code):
            checking_options.update(re.findall(r"--[a-zA-Z][a-zA-Z-]*", pragma))
        assumptions.extend(
            f"{source.module.name}:{match.group('kind').lower()}:{match.group('name')}"
            for match in _ASSUMPTION_DECLARATION.finditer(code)
        )
        assumptions.extend(
            f"{source.module.name}:pragma:{' '.join(match.group(0).split())}"
            for match in _DANGEROUS_PRAGMA.finditer(code)
        )
    forbidden_options = checking_options & (
        _INCOMPLETE_CHECKING_OPTIONS
        if profile.allow_unsafe_options
        else _CHECKING_WAIVERS
    )
    if forbidden_options:
        diagnostics.append(
            _diagnostic(
                "unsafe-checking-option",
                "fresh validation cannot certify this checking profile: "
                + ", ".join(sorted(forbidden_options)),
            )
        )
    return PolicyReport(
        not diagnostics,
        candidate,
        tuple(diagnostics),
        original_sha,
        candidate_sha,
        tuple(sorted(assumptions)),
    )
