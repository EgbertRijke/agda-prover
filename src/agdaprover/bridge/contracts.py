"""Small, dependency-free value contracts for the Stage 1 bridge.

The bridge intentionally uses nominal identifier wrappers.  A source revision,
environment, command, and state are all hashes or integers at the wire level,
but accepting one in place of another is a correctness and authority bug.
Runtime constructors enforce the same separation that static typing documents.
"""

from __future__ import annotations

import hashlib
import json
import math
import re
import time
from collections.abc import Mapping
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Any, ClassVar, Literal

from ..resource_budget import current_ledgers
from ..source_files import is_agda_source_path

BRIDGE_SCHEMA_VERSION = "agdaprover.bridge.v1"
DIAGNOSTIC_SCHEMA_VERSION = "agdaprover.bridge-diagnostic.v1"
MAX_IDENTIFIER_BYTES = 512
MAX_DIAGNOSTIC_BYTES = 16_384
_SHA256 = re.compile(r"[0-9a-f]{64}")
_MODULE_NAME = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")


def stable_hash(value: object) -> str:
    encoded = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _expect_schema(value: Mapping[str, Any], expected: str) -> None:
    actual = value.get("schema_version")
    if actual != expected:
        raise ValueError(
            f"unsupported schema version {actual!r}; expected {expected!r}"
        )


def _expect_exact_keys(value: Mapping[str, Any], keys: set[str]) -> None:
    actual = set(value)
    if actual != keys:
        unknown = sorted(actual - keys)
        missing = sorted(keys - actual)
        raise ValueError(f"invalid fields; unknown={unknown}, missing={missing}")


def _bounded_text(value: object, *, name: str, limit: int) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{name} must be text")
    if len(value.encode()) > limit:
        raise ValueError(f"{name} exceeds {limit} bytes")
    return value


def _integer(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an integer")
    return value


def _number(value: object, *, name: str) -> int | float:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        raise ValueError(f"{name} must be numeric")
    if not math.isfinite(float(value)):
        raise ValueError(f"{name} must be finite")
    return value


def _boolean(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be Boolean")
    return value


@dataclass(frozen=True, order=True)
class EnvironmentId:
    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str) or not _SHA256.fullmatch(self.value):
            raise ValueError("environment id must be a lowercase SHA-256 digest")


@dataclass(frozen=True, order=True)
class SourceRevision:
    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str) or not _SHA256.fullmatch(self.value):
            raise ValueError("source revision must be a lowercase SHA-256 digest")


@dataclass(frozen=True, order=True)
class ModuleId:
    name: str
    relative_path: str

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not isinstance(self.relative_path, str):
            raise ValueError("module name and path must be text")
        if not _MODULE_NAME.fullmatch(self.name):
            raise ValueError(f"invalid Agda module name: {self.name!r}")
        path = self.relative_path.replace("\\", "/")
        if (
            path.startswith("/")
            or ".." in path.split("/")
            or not is_agda_source_path(path)
        ):
            raise ValueError(f"invalid module-relative path: {self.relative_path!r}")

    def to_dict(self) -> dict[str, str]:
        return {"name": self.name, "relative_path": self.relative_path}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ModuleId:
        _expect_exact_keys(value, {"name", "relative_path"})
        return cls(
            _bounded_text(
                value["name"], name="module name", limit=MAX_IDENTIFIER_BYTES
            ),
            _bounded_text(value["relative_path"], name="module path", limit=4096),
        )


@dataclass(frozen=True, order=True)
class ProjectHandle:
    environment_id: EnvironmentId
    nonce: str

    def __post_init__(self) -> None:
        if not isinstance(self.nonce, str):
            raise ValueError("project nonce must be text")
        _bounded_text(self.nonce, name="project nonce", limit=128)
        if not re.fullmatch(r"[0-9a-f]{32}", self.nonce):
            raise ValueError("project nonce must be 128-bit lowercase hexadecimal")

    def to_dict(self) -> dict[str, str]:
        return {
            "environment_id": self.environment_id.value,
            "nonce": self.nonce,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> ProjectHandle:
        _expect_exact_keys(value, {"environment_id", "nonce"})
        return cls(
            EnvironmentId(
                _bounded_text(value["environment_id"], name="environment id", limit=64)
            ),
            _bounded_text(value["nonce"], name="project nonce", limit=128),
        )


@dataclass(frozen=True, order=True)
class CommandId:
    session_nonce: str
    sequence: int

    def __post_init__(self) -> None:
        if not isinstance(self.session_nonce, str) or not re.fullmatch(
            r"[0-9a-f]{16}", self.session_nonce
        ):
            raise ValueError("command session nonce must be 64-bit hexadecimal")
        if type(self.sequence) is not int or self.sequence < 1:
            raise ValueError("command sequence must be positive")

    @property
    def value(self) -> str:
        return f"{self.session_nonce}:{self.sequence}"

    @classmethod
    def parse(cls, value: str) -> CommandId:
        nonce, separator, sequence = value.partition(":")
        if not separator or not sequence.isascii() or not sequence.isdecimal():
            raise ValueError("malformed command id")
        return cls(nonce, int(sequence))


@dataclass(frozen=True, order=True)
class InteractionId:
    value: int

    def __post_init__(self) -> None:
        if type(self.value) is not int or self.value < 0:
            raise ValueError("interaction id must be nonnegative")


@dataclass(frozen=True, order=True)
class MetaId:
    value: str

    def __post_init__(self) -> None:
        if not isinstance(self.value, str):
            raise ValueError("meta id must be text")
        text = _bounded_text(self.value, name="meta id", limit=MAX_IDENTIFIER_BYTES)
        if not text or any(character.isspace() for character in text):
            raise ValueError("meta id must be nonempty and contain no whitespace")


@dataclass(frozen=True, order=True)
class SourceRange:
    start: int
    end: int
    file: str | None = None

    def __post_init__(self) -> None:
        if (
            type(self.start) is not int
            or type(self.end) is not int
            or self.start < 0
            or self.end < self.start
        ):
            raise ValueError("source range must be ordered and nonnegative")
        if self.file is not None:
            _bounded_text(self.file, name="source file", limit=4096)

    def to_dict(self) -> dict[str, Any]:
        return {"start": self.start, "end": self.end, "file": self.file}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> SourceRange:
        _expect_exact_keys(value, {"start", "end", "file"})
        file_value = value["file"]
        if file_value is not None and not isinstance(file_value, str):
            raise ValueError("source range file must be text or null")
        return cls(
            _integer(value["start"], name="range start"),
            _integer(value["end"], name="range end"),
            file_value,
        )


@dataclass(frozen=True, order=True)
class StateToken:
    environment_id: EnvironmentId
    source_revision: SourceRevision
    module_id: ModuleId
    process_generation: int
    sequence: int
    structural_hash: str

    def __post_init__(self) -> None:
        if (
            type(self.process_generation) is not int
            or type(self.sequence) is not int
            or self.process_generation < 1
            or self.sequence < 1
        ):
            raise ValueError("state token generations and sequences must be positive")
        if not _SHA256.fullmatch(self.structural_hash):
            raise ValueError("state token structural hash must be SHA-256")

    def to_dict(self) -> dict[str, Any]:
        return {
            "environment_id": self.environment_id.value,
            "source_revision": self.source_revision.value,
            "module_id": self.module_id.to_dict(),
            "process_generation": self.process_generation,
            "sequence": self.sequence,
            "structural_hash": self.structural_hash,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> StateToken:
        _expect_exact_keys(
            value,
            {
                "environment_id",
                "source_revision",
                "module_id",
                "process_generation",
                "sequence",
                "structural_hash",
            },
        )
        module = value["module_id"]
        if not isinstance(module, Mapping):
            raise ValueError("state token module id must be an object")
        return cls(
            EnvironmentId(
                _bounded_text(value["environment_id"], name="environment id", limit=64)
            ),
            SourceRevision(
                _bounded_text(
                    value["source_revision"], name="source revision", limit=64
                )
            ),
            ModuleId.from_dict(module),
            _integer(value["process_generation"], name="process generation"),
            _integer(value["sequence"], name="state sequence"),
            _bounded_text(value["structural_hash"], name="structural hash", limit=64),
        )


class BridgeFailure(StrEnum):
    INVALID_REQUEST = "invalid-request"
    STALE_TOKEN = "stale-token"
    UNSUPPORTED_CAPABILITY = "unsupported-capability"
    AGDA_REJECTION = "agda-rejection"
    LOAD_FAILURE = "load-failure"
    PROTOCOL_FAILURE = "protocol-failure"
    TIMEOUT = "timeout"
    CANCELLED = "cancelled"
    RESOURCE_EXHAUSTED = "resource-exhausted"
    CHILD_PROCESS_FAILURE = "child-process-failure"
    POLICY_REJECTED = "policy-rejected"
    TOOLCHAIN_ERROR = "toolchain-error"
    INTERNAL_INVARIANT = "internal-invariant"


class DiagnosticPhase(StrEnum):
    RESOLUTION = "resolution"
    TRANSPORT = "transport"
    PARSING = "parsing"
    SCOPE = "scope"
    ELABORATION = "elaboration"
    UNIFICATION = "unification"
    INSTANCE_SEARCH = "instance-search"
    POSITIVITY = "positivity"
    COVERAGE = "coverage"
    TERMINATION = "termination"
    VALIDATION = "validation"
    POLICY = "policy"
    RESOURCE = "resource"
    PROTOCOL = "protocol"
    TOOLCHAIN = "toolchain"
    INTERNAL = "internal"


Severity = Literal["info", "warning", "error"]
RedactionClass = Literal["public", "project-relative", "sensitive"]


@dataclass(frozen=True)
class BridgeDiagnostic:
    code: str
    phase: DiagnosticPhase
    severity: Severity
    message: str
    primary_range: SourceRange | None = None
    related_ranges: tuple[SourceRange, ...] = ()
    causes: tuple[str, ...] = ()
    retryable: bool = False
    raw_sha256: str | None = None
    redaction: RedactionClass = "public"
    schema_version: str = DIAGNOSTIC_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != DIAGNOSTIC_SCHEMA_VERSION:
            raise ValueError("unsupported diagnostic schema version")
        if not re.fullmatch(r"[a-z][a-z0-9-]{1,63}", self.code):
            raise ValueError(f"invalid diagnostic code: {self.code!r}")
        _bounded_text(
            self.message, name="diagnostic message", limit=MAX_DIAGNOSTIC_BYTES
        )
        if len(self.related_ranges) > 64 or len(self.causes) > 32:
            raise ValueError("diagnostic relation or cause collection is too large")
        if self.raw_sha256 is not None and not _SHA256.fullmatch(self.raw_sha256):
            raise ValueError("raw diagnostic identity must be SHA-256")
        if self.severity not in {"info", "warning", "error"}:
            raise ValueError("invalid diagnostic severity")
        if self.redaction not in {"public", "project-relative", "sensitive"}:
            raise ValueError("invalid diagnostic redaction class")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "code": self.code,
            "phase": self.phase.value,
            "severity": self.severity,
            "message": self.message,
            "primary_range": (
                self.primary_range.to_dict() if self.primary_range else None
            ),
            "related_ranges": [item.to_dict() for item in self.related_ranges],
            "causes": list(self.causes),
            "retryable": self.retryable,
            "raw_sha256": self.raw_sha256,
            "redaction": self.redaction,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> BridgeDiagnostic:
        keys = {
            "schema_version",
            "code",
            "phase",
            "severity",
            "message",
            "primary_range",
            "related_ranges",
            "causes",
            "retryable",
            "raw_sha256",
            "redaction",
        }
        _expect_exact_keys(value, keys)
        _expect_schema(value, DIAGNOSTIC_SCHEMA_VERSION)
        primary = value["primary_range"]
        related = value["related_ranges"]
        causes = value["causes"]
        if primary is not None and not isinstance(primary, Mapping):
            raise ValueError("primary diagnostic range must be an object or null")
        if not isinstance(related, list) or not all(
            isinstance(item, Mapping) for item in related
        ):
            raise ValueError("related diagnostic ranges must be a list of objects")
        if not isinstance(causes, list) or not all(
            isinstance(item, str) for item in causes
        ):
            raise ValueError("diagnostic causes must be a list of text")
        return cls(
            code=_bounded_text(value["code"], name="diagnostic code", limit=64),
            phase=DiagnosticPhase(
                _bounded_text(value["phase"], name="diagnostic phase", limit=64)
            ),
            severity=_bounded_text(  # type: ignore[arg-type]
                value["severity"], name="diagnostic severity", limit=16
            ),
            message=_bounded_text(
                value["message"], name="diagnostic message", limit=MAX_DIAGNOSTIC_BYTES
            ),
            primary_range=SourceRange.from_dict(primary) if primary else None,
            related_ranges=tuple(SourceRange.from_dict(item) for item in related),
            causes=tuple(causes),
            retryable=_boolean(value["retryable"], name="diagnostic retryable"),
            raw_sha256=(
                _bounded_text(value["raw_sha256"], name="raw hash", limit=64)
                if value["raw_sha256"] is not None
                else None
            ),
            redaction=_bounded_text(  # type: ignore[arg-type]
                value["redaction"], name="diagnostic redaction", limit=32
            ),
        )


class BridgeError(RuntimeError):
    """A typed terminal failure at the version-neutral bridge boundary."""

    def __init__(
        self,
        failure: BridgeFailure,
        diagnostic: BridgeDiagnostic,
        *,
        command_id: CommandId | None = None,
    ) -> None:
        if diagnostic.severity != "error":
            raise ValueError("bridge errors require an error diagnostic")
        self.failure = failure
        self.diagnostic = diagnostic
        self.command_id = command_id
        super().__init__(diagnostic.message)


@dataclass(frozen=True)
class BridgeBudget:
    wall_seconds: float = 10.0
    cpu_seconds: float = 10.0
    memory_bytes: int = 1_073_741_824
    process_count: int = 4
    output_bytes: int = 8_388_608
    event_count: int = 100_000
    temporary_bytes: int = 268_435_456
    artifact_count: int = 10_000
    started: float = field(default_factory=time.monotonic, compare=False)

    def __post_init__(self) -> None:
        if (
            not isinstance(self.wall_seconds, (int, float))
            or isinstance(self.wall_seconds, bool)
            or math.isnan(self.wall_seconds)
            or self.wall_seconds <= 0
        ):
            raise ValueError("wall budget must be positive or infinite")
        if (
            not isinstance(self.cpu_seconds, (int, float))
            or isinstance(self.cpu_seconds, bool)
            or math.isnan(self.cpu_seconds)
            or self.cpu_seconds <= 0
        ):
            raise ValueError("CPU budget must be positive or infinite")
        for name in (
            "memory_bytes",
            "process_count",
            "output_bytes",
            "event_count",
            "temporary_bytes",
            "artifact_count",
        ):
            if type(getattr(self, name)) is not int or getattr(self, name) <= 0:
                raise ValueError(f"{name} budget must be positive")

    @classmethod
    def for_run(cls, wall_seconds: float) -> BridgeBudget:
        """Use the controller envelope, not hidden per-bridge capacity caps.

        Direct bridge clients retain their explicitly constructed BridgeBudget.
        A controller's aggregate ledger also charges every process/retry, so
        these local reservations cannot reset the task allowance.
        """
        ledgers = current_ledgers()
        if not ledgers:
            return cls(wall_seconds=wall_seconds, cpu_seconds=math.inf)
        return cls(
            wall_seconds=wall_seconds,
            cpu_seconds=min(
                (
                    ledger.limits.cpu_seconds
                    if ledger.limits.cpu_seconds is not None
                    else math.inf
                )
                for ledger in ledgers
            ),
            memory_bytes=min(ledger.limits.memory_bytes for ledger in ledgers),
            output_bytes=min(ledger.limits.io_bytes for ledger in ledgers),
            temporary_bytes=min(ledger.limits.temporary_bytes for ledger in ledgers),
        )

    @property
    def deadline(self) -> float:
        return self.started + self.wall_seconds

    def remaining_seconds(self) -> float:
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("bridge wall-time budget exhausted")
        return remaining

    def to_dict(self) -> dict[str, int | float | None]:
        return {
            "wall_seconds": (
                self.wall_seconds if math.isfinite(self.wall_seconds) else None
            ),
            "cpu_seconds": (
                self.cpu_seconds if math.isfinite(self.cpu_seconds) else None
            ),
            "memory_bytes": self.memory_bytes,
            "process_count": self.process_count,
            "output_bytes": self.output_bytes,
            "event_count": self.event_count,
            "temporary_bytes": self.temporary_bytes,
            "artifact_count": self.artifact_count,
        }


@dataclass
class BridgeCost:
    commands: int = 0
    bytes_written: int = 0
    bytes_read: int = 0
    events_decoded: int = 0
    process_starts: int = 0
    process_restarts: int = 0
    module_loads: int = 0
    rollback_replays: int = 0
    cancellations: int = 0
    peak_rss_bytes: int = 0
    temporary_bytes: int = 0
    elapsed_ms: float = 0.0
    cpu_ms: float = 0.0

    _INTEGER_FIELDS: ClassVar[frozenset[str]] = frozenset(
        {
            "commands",
            "bytes_written",
            "bytes_read",
            "events_decoded",
            "process_starts",
            "process_restarts",
            "module_loads",
            "rollback_replays",
            "cancellations",
            "peak_rss_bytes",
            "temporary_bytes",
        }
    )

    def __post_init__(self) -> None:
        for name, amount in self.to_dict().items():
            if (
                isinstance(amount, bool)
                or not math.isfinite(float(amount))
                or amount < 0
            ):
                raise ValueError(f"invalid bridge cost for {name}")
            if name in self._INTEGER_FIELDS and type(amount) is not int:
                raise ValueError(f"bridge cost {name} requires an integer")

    def add(self, **increments: int | float) -> None:
        fields = self.__dataclass_fields__
        for name, increment in increments.items():
            if name not in fields or name.startswith("_"):
                raise ValueError(f"unknown bridge cost: {name}")
            if (
                isinstance(increment, bool)
                or not math.isfinite(float(increment))
                or increment < 0
            ):
                raise ValueError(f"invalid bridge cost increment for {name}")
            if name in self._INTEGER_FIELDS and type(increment) is not int:
                raise ValueError(f"bridge cost {name} requires an integer")
            setattr(self, name, getattr(self, name) + increment)

    def copy(self) -> BridgeCost:
        return BridgeCost(
            commands=self.commands,
            bytes_written=self.bytes_written,
            bytes_read=self.bytes_read,
            events_decoded=self.events_decoded,
            process_starts=self.process_starts,
            process_restarts=self.process_restarts,
            module_loads=self.module_loads,
            rollback_replays=self.rollback_replays,
            cancellations=self.cancellations,
            peak_rss_bytes=self.peak_rss_bytes,
            temporary_bytes=self.temporary_bytes,
            elapsed_ms=self.elapsed_ms,
            cpu_ms=self.cpu_ms,
        )

    def delta(self, previous: BridgeCost) -> BridgeCost:
        values: dict[str, int | float] = {}
        for name, current in self.to_dict().items():
            before = previous.to_dict()[name]
            values[name] = current - before
        return BridgeCost(
            commands=int(values["commands"]),
            bytes_written=int(values["bytes_written"]),
            bytes_read=int(values["bytes_read"]),
            events_decoded=int(values["events_decoded"]),
            process_starts=int(values["process_starts"]),
            process_restarts=int(values["process_restarts"]),
            module_loads=int(values["module_loads"]),
            rollback_replays=int(values["rollback_replays"]),
            cancellations=int(values["cancellations"]),
            peak_rss_bytes=int(values["peak_rss_bytes"]),
            temporary_bytes=int(values["temporary_bytes"]),
            elapsed_ms=float(values["elapsed_ms"]),
            cpu_ms=float(values["cpu_ms"]),
        )

    def to_dict(self) -> dict[str, int | float]:
        return {
            name: getattr(self, name)
            for name in self.__dataclass_fields__
            if not name.startswith("_")
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> BridgeCost:
        expected = {
            name for name in cls.__dataclass_fields__ if not name.startswith("_")
        }
        _expect_exact_keys(value, expected)
        for name in cls._INTEGER_FIELDS:
            _integer(value[name], name=f"bridge cost {name}")
        for name in ("elapsed_ms", "cpu_ms"):
            _number(value[name], name=f"bridge cost {name}")
        return cls(
            commands=int(value["commands"]),
            bytes_written=int(value["bytes_written"]),
            bytes_read=int(value["bytes_read"]),
            events_decoded=int(value["events_decoded"]),
            process_starts=int(value["process_starts"]),
            process_restarts=int(value["process_restarts"]),
            module_loads=int(value["module_loads"]),
            rollback_replays=int(value["rollback_replays"]),
            cancellations=int(value["cancellations"]),
            peak_rss_bytes=int(value["peak_rss_bytes"]),
            temporary_bytes=int(value["temporary_bytes"]),
            elapsed_ms=float(value["elapsed_ms"]),
            cpu_ms=float(value["cpu_ms"]),
        )


@dataclass(frozen=True)
class CapabilityManifest:
    agda_version: str
    adapter: str
    operations: tuple[str, ...]
    limitations: tuple[str, ...] = ()
    schema_version: str = BRIDGE_SCHEMA_VERSION

    def __post_init__(self) -> None:
        if self.schema_version != BRIDGE_SCHEMA_VERSION:
            raise ValueError("unsupported capability schema version")
        if tuple(sorted(set(self.operations))) != self.operations:
            raise ValueError("capabilities must be unique and sorted")
        if len(self.operations) > 128 or len(self.limitations) > 128:
            raise ValueError("capability manifest is too large")

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "agda_version": self.agda_version,
            "adapter": self.adapter,
            "operations": list(self.operations),
            "limitations": list(self.limitations),
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> CapabilityManifest:
        _expect_exact_keys(
            value,
            {
                "schema_version",
                "agda_version",
                "adapter",
                "operations",
                "limitations",
            },
        )
        _expect_schema(value, BRIDGE_SCHEMA_VERSION)
        operations = value["operations"]
        limitations = value["limitations"]
        if not isinstance(operations, list) or not all(
            isinstance(item, str) for item in operations
        ):
            raise ValueError("capability operations must be a text list")
        if not isinstance(limitations, list) or not all(
            isinstance(item, str) for item in limitations
        ):
            raise ValueError("capability limitations must be a text list")
        return cls(
            agda_version=_bounded_text(
                value["agda_version"], name="Agda version", limit=128
            ),
            adapter=_bounded_text(value["adapter"], name="adapter", limit=256),
            operations=tuple(operations),
            limitations=tuple(limitations),
        )


@dataclass(frozen=True)
class BridgeResourceSummary:
    process_generation: int
    commands: int
    process_starts: int
    process_restarts: int
    cancellations: int
    bytes_read: int
    bytes_written: int
    peak_rss_bytes: int
    overlays_removed: int
    orphan_processes: int
    close_elapsed_ms: float

    def __post_init__(self) -> None:
        for name, amount in self.to_dict().items():
            if (
                not isinstance(amount, (int, float))
                or isinstance(amount, bool)
                or not math.isfinite(float(amount))
                or amount < 0
            ):
                raise ValueError(f"invalid resource summary field {name}")

    def to_dict(self) -> dict[str, int | float]:
        return {name: getattr(self, name) for name in self.__dataclass_fields__}

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> BridgeResourceSummary:
        expected = set(cls.__dataclass_fields__)
        _expect_exact_keys(value, expected)
        for name in expected - {"close_elapsed_ms"}:
            _integer(value[name], name=f"resource summary {name}")
        _number(value["close_elapsed_ms"], name="resource summary close elapsed")
        return cls(
            process_generation=int(value["process_generation"]),
            commands=int(value["commands"]),
            process_starts=int(value["process_starts"]),
            process_restarts=int(value["process_restarts"]),
            cancellations=int(value["cancellations"]),
            bytes_read=int(value["bytes_read"]),
            bytes_written=int(value["bytes_written"]),
            peak_rss_bytes=int(value["peak_rss_bytes"]),
            overlays_removed=int(value["overlays_removed"]),
            orphan_processes=int(value["orphan_processes"]),
            close_elapsed_ms=float(value["close_elapsed_ms"]),
        )
