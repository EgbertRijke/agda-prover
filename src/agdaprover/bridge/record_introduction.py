"""Closed, read-only record-introduction protocol for the optional Agda bridge."""

from __future__ import annotations

import json
from dataclasses import dataclass

SCHEMA = "agdaprover.record-introduction.v1"
KIND = "AgdaProverRecordIntroduction"
MARKER = "agdaprover:record-introduction:v1:"


def request_payload(output_bytes: int) -> str:
    if type(output_bytes) is not int or output_bytes <= 0:
        raise ValueError("invalid record-introduction output reservation")
    return MARKER + json.dumps({"output_bytes": output_bytes})


@dataclass(frozen=True)
class RecordIntroduction:
    expression: str | None
    required_bytes: int | None = None


def decode(value: object, *, goal_id: int, output_bytes: int) -> RecordIntroduction:
    request_payload(output_bytes)
    if (
        type(goal_id) is not int
        or goal_id < 0
        or not isinstance(value, dict)
        or set(value)
        != {
            "kind",
            "schema_version",
            "interaction_id",
            "output_bytes",
            "status",
            "expression",
            "required_bytes",
        }
        or value["kind"] != KIND
        or value["schema_version"] != SCHEMA
        or type(value["interaction_id"]) is not int
        or value["interaction_id"] != goal_id
        or type(value["output_bytes"]) is not int
        or value["output_bytes"] != output_bytes
    ):
        raise ValueError("invalid record-introduction response identity")
    expression, required = value["expression"], value["required_bytes"]
    if value["status"] == "output-limited":
        if (
            expression is not None
            or type(required) is not int
            or required <= output_bytes
        ):
            raise ValueError("invalid record-introduction resource refusal")
        return RecordIntroduction(None, required)
    if required is not None:
        raise ValueError("unexpected record-introduction resource field")
    if value["status"] == "not-record" and expression is None:
        return RecordIntroduction(None)
    if (
        value["status"] != "record"
        or not isinstance(expression, str)
        or not expression.strip()
        or "\0" in expression
    ):
        raise ValueError("invalid record-introduction proposal")
    return RecordIntroduction(expression)
