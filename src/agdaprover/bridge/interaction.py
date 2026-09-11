"""Typed intent for Agda-owned syntax operations, independent of transport."""

from dataclasses import dataclass
from enum import StrEnum
from typing import Literal


class RewriteMode(StrEnum):
    """Agda's distinct reification policies; these are not compute modes."""

    AS_IS = "as-is"
    INSTANTIATED = "instantiated"
    HEAD_NORMAL = "head-normal"
    SIMPLIFIED = "simplified"
    NORMAL = "normal"


@dataclass(frozen=True)
class ClauseAction:
    """A make-case request. Agda, not the caller, classifies its subjects."""

    kind: Literal["variables", "result", "ellipsis"]
    subjects: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.kind not in ("variables", "result", "ellipsis"):
            raise ValueError("unknown clause action")
        if not isinstance(self.subjects, tuple) or any(
            not isinstance(name, str)
            or not name
            or name == "."
            or any(c.isspace() for c in name)
            for name in self.subjects
        ):
            raise ValueError("clause subjects must be individual context names")
        if bool(self.subjects) != (self.kind == "variables"):
            raise ValueError("only variable actions require subjects")

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": "agdaprover.clause-action.v1",
            "kind": self.kind,
            "subjects": list(self.subjects),
        }

    @classmethod
    def from_dict(cls, value: dict[str, object]) -> "ClauseAction":
        if (
            set(value) != {"schema_version", "kind", "subjects"}
            or value["schema_version"] != "agdaprover.clause-action.v1"
            or not isinstance(value["subjects"], list)
        ):
            raise ValueError("malformed clause action")
        return cls(value["kind"], tuple(value["subjects"]))  # type: ignore[arg-type]
