"""Bounded command/event codec for Agda 2.8.0's public JSON protocol."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ..contracts import CapabilityManifest, SourceRange

PROMPT = b"JSON> "


def _quote(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


@dataclass(frozen=True)
class RawEvent:
    kind: str
    value: dict[str, Any]


@dataclass(frozen=True)
class DecodedResponse:
    events: tuple[RawEvent, ...]
    raw_sha256: str
    raw_bytes: int


@dataclass(frozen=True)
class ContextObservation:
    original_name: str
    reified_name: str
    type_text: str
    in_scope: bool


@dataclass(frozen=True)
class GoalObservation:
    interaction_id: int
    target: str
    context: tuple[ContextObservation, ...]
    source_range: SourceRange
    boundary: tuple[str, ...]


@dataclass(frozen=True)
class CandidateObservation:
    accepted: bool
    elaborated_term: str | None


@dataclass(frozen=True)
class RefinementObservation:
    accepted: bool
    preview: str | None
    goals: tuple[GoalObservation, ...]


@dataclass(frozen=True)
class CaseObservation:
    accepted: bool
    clauses: tuple[str, ...]
    variant: str | None


@dataclass(frozen=True)
class InferObservation:
    accepted: bool
    inferred_type: str | None


@dataclass(frozen=True)
class NormalizeObservation:
    accepted: bool
    normal_form: str | None
    complete: bool


@dataclass(frozen=True)
class ConstraintObservation:
    constraint_id: str
    kind: str
    rendered: str


@dataclass(frozen=True)
class MetaObservation:
    meta_id: str
    type_text: str
    source_range: SourceRange
    interaction_id: int | None


class Agda28Adapter:
    version = "2.8.0"
    name = "agda-interaction-json-2.8.0"

    def capabilities(self) -> CapabilityManifest:
        return CapabilityManifest(
            agda_version=self.version,
            adapter=self.name,
            operations=tuple(
                sorted(
                    {
                        "case-split",
                        "check-definition",
                        "close",
                        "infer",
                        "inspect-goals",
                        "load-module",
                        "normalize",
                        "open-project",
                        "try-action",
                        "validate-patch",
                    }
                )
            ),
            limitations=(
                "case-split responses are source clauses and cannot be committed in-place",
                "internal term constructors are unavailable; terms are tagged Agda renderings",
                "binder modality and quantity absent from JSON are represented as unknown",
            ),
        )

    def command_wire(
        self,
        source_file: Path,
        command: str,
        *,
        highlighting_method: str = "Direct",
    ) -> bytes:
        if highlighting_method not in {"Direct", "Indirect"}:
            raise ValueError("unsupported Agda highlighting method")
        return (
            f"IOTCM {_quote(str(source_file))} None {highlighting_method} ({command})\n"
        ).encode()

    def load(self, source_file: Path, options: tuple[str, ...]) -> str:
        rendered_options = "[" + ",".join(_quote(item) for item in options) + "]"
        return f"Cmd_load {_quote(str(source_file))} {rendered_options}"

    def inspect_goal(self, interaction_id: int) -> str:
        return f'Cmd_goal_type_context Normalised {interaction_id} noRange ""'

    def infer(self, interaction_id: int | None, expression: str) -> str:
        if interaction_id is None:
            return f"Cmd_infer_toplevel Normalised {_quote(expression)}"
        return f"Cmd_infer Normalised {interaction_id} noRange {_quote(expression)}"

    def normalize(
        self, interaction_id: int | None, expression: str, compute_mode: str
    ) -> str:
        if interaction_id is None:
            return f"Cmd_compute_toplevel {compute_mode} {_quote(expression)}"
        return (
            f"Cmd_compute {compute_mode} {interaction_id} noRange {_quote(expression)}"
        )

    def check_term(self, interaction_id: int, expression: str) -> str:
        return (
            f"Cmd_goal_type_context_check Normalised {interaction_id} noRange "
            f"{_quote(expression)}"
        )

    def give(self, interaction_id: int, expression: str) -> str:
        return f"Cmd_give WithoutForce {interaction_id} noRange {_quote(expression)}"

    def refine(self, interaction_id: int, expression: str) -> str:
        return (
            f"Cmd_refine_or_intro False {interaction_id} noRange {_quote(expression)}"
        )

    def case_split(self, interaction_id: int, local_name: str) -> str:
        return f"Cmd_make_case {interaction_id} noRange {_quote(local_name)}"

    def auto(self, interaction_id: int) -> str:
        return f'Cmd_autoOne AsIs {interaction_id} noRange ""'

    def module_contents(self, interaction_id: int, module_name: str) -> str:
        return (
            f"Cmd_show_module_contents Normalised {interaction_id} noRange "
            f"{_quote(module_name)}"
        )

    def constraints(self) -> str:
        return "Cmd_constraints"

    def metas(self) -> str:
        return "Cmd_metas AsIs"

    def decode(self, raw: bytes, *, event_limit: int) -> DecodedResponse:
        events: list[RawEvent] = []
        for line_number, raw_line in enumerate(raw.splitlines(), 1):
            line = raw_line.strip()
            if not line:
                continue
            if len(events) >= event_limit:
                raise ValueError(f"Agda response exceeds {event_limit} events")
            try:
                value = json.loads(line)
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValueError(
                    f"malformed Agda JSON event at response line {line_number}"
                ) from error
            if not isinstance(value, dict):
                raise ValueError(
                    f"Agda JSON event at response line {line_number} is not an object"
                )
            kind = value.get("kind")
            if not isinstance(kind, str) or not kind:
                raise ValueError(
                    f"Agda JSON event at response line {line_number} has no kind"
                )
            events.append(RawEvent(kind, value))
        return DecodedResponse(tuple(events), hashlib.sha256(raw).hexdigest(), len(raw))

    def error_payload(self, response: DecodedResponse) -> dict[str, Any] | None:
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "Error":
                continue
            error = info.get("error")
            return error if isinstance(error, dict) else {"message": "Agda error"}
        return None

    def interaction_points(
        self, response: DecodedResponse
    ) -> tuple[GoalObservation, ...]:
        points: list[dict[str, Any]] = []
        targets: dict[int, str] = {}
        for event in response.events:
            if event.kind == "InteractionPoints":
                raw_points = event.value.get("interactionPoints", [])
                if isinstance(raw_points, list):
                    points = [item for item in raw_points if isinstance(item, dict)]
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "AllGoalsWarnings":
                continue
            visible = info.get("visibleGoals", [])
            if not isinstance(visible, list):
                continue
            for goal in visible:
                if not isinstance(goal, dict):
                    continue
                constraint = goal.get("constraintObj", {})
                if isinstance(constraint, dict) and isinstance(
                    constraint.get("id"), int
                ):
                    targets[constraint["id"]] = str(goal.get("type", ""))
        result: list[GoalObservation] = []
        for point in points:
            identifier = point.get("id")
            if not isinstance(identifier, int):
                continue
            result.append(
                GoalObservation(
                    interaction_id=identifier,
                    target=targets.get(identifier, ""),
                    context=(),
                    source_range=self.source_range(point.get("range")),
                    boundary=(),
                )
            )
        return tuple(sorted(result, key=lambda goal: goal.interaction_id))

    def goal(self, response: DecodedResponse) -> GoalObservation | None:
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "GoalSpecific":
                continue
            goal_info = info.get("goalInfo")
            interaction = info.get("interactionPoint")
            if not isinstance(goal_info, dict) or not isinstance(interaction, dict):
                continue
            if goal_info.get("kind") != "GoalType":
                continue
            identifier = interaction.get("id")
            if not isinstance(identifier, int):
                continue
            context: list[ContextObservation] = []
            entries = goal_info.get("entries", [])
            if isinstance(entries, list):
                for entry in entries:
                    if not isinstance(entry, dict):
                        continue
                    context.append(
                        ContextObservation(
                            original_name=str(entry.get("originalName", "")),
                            reified_name=str(
                                entry.get("reifiedName")
                                or entry.get("originalName")
                                or ""
                            ),
                            type_text=str(entry.get("binding", "")),
                            in_scope=bool(entry.get("inScope", False)),
                        )
                    )
            boundary_value = goal_info.get("boundary", [])
            boundary = (
                tuple(str(item) for item in boundary_value)
                if isinstance(boundary_value, list)
                else ()
            )
            return GoalObservation(
                interaction_id=identifier,
                target=str(goal_info.get("type", "")),
                context=tuple(context),
                source_range=self.source_range(interaction.get("range")),
                boundary=boundary,
            )
        return None

    def candidate(self, response: DecodedResponse) -> CandidateObservation:
        if self.error_payload(response) is not None:
            return CandidateObservation(False, None)
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict):
                continue
            goal_info = info.get("goalInfo")
            if not isinstance(goal_info, dict):
                continue
            type_aux = goal_info.get("typeAux")
            if (
                isinstance(type_aux, dict)
                and type_aux.get("kind") == "GoalAndElaboration"
            ):
                return CandidateObservation(True, str(type_aux.get("term", "")))
        return CandidateObservation(False, None)

    def refinement(self, response: DecodedResponse) -> RefinementObservation:
        if self.error_payload(response) is not None:
            return RefinementObservation(False, None, ())
        preview: str | None = None
        for event in response.events:
            if event.kind == "GiveAction":
                result = event.value.get("giveResult")
                if isinstance(result, dict):
                    preview = str(result.get("str", ""))
        return RefinementObservation(
            preview is not None,
            preview,
            self.interaction_points(response),
        )

    def auto_term(self, response: DecodedResponse) -> str | None:
        """Extract a term proposed by Agda's built-in proof search."""

        return self.refinement(response).preview

    def case(self, response: DecodedResponse) -> CaseObservation:
        if self.error_payload(response) is not None:
            return CaseObservation(False, (), None)
        for event in response.events:
            if event.kind != "MakeCase":
                continue
            clauses = event.value.get("clauses", [])
            if not isinstance(clauses, list):
                continue
            rendered = tuple(str(item) for item in clauses)
            if rendered:
                variant = event.value.get("variant")
                return CaseObservation(
                    True,
                    rendered,
                    str(variant) if variant is not None else None,
                )
        return CaseObservation(False, (), None)

    def named_contents(self, response: DecodedResponse) -> tuple[tuple[str, str], ...]:
        if self.error_payload(response) is not None:
            return ()
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "ModuleContents":
                continue
            contents = info.get("contents", [])
            if not isinstance(contents, list):
                return ()
            return tuple(
                (str(item.get("name", "")), str(item.get("term", "")))
                for item in contents
                if isinstance(item, dict) and item.get("name") and item.get("term")
            )
        return ()

    def inferred(self, response: DecodedResponse) -> InferObservation:
        if self.error_payload(response) is not None:
            return InferObservation(False, None)
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict):
                continue
            if info.get("kind") == "GoalSpecific":
                goal_info = info.get("goalInfo")
                if (
                    isinstance(goal_info, dict)
                    and goal_info.get("kind") == "InferredType"
                ):
                    return InferObservation(True, str(goal_info.get("expr", "")))
            if info.get("kind") == "InferredType":
                return InferObservation(True, str(info.get("expr", "")))
        return InferObservation(False, None)

    def normalized(self, response: DecodedResponse) -> NormalizeObservation:
        if self.error_payload(response) is not None:
            return NormalizeObservation(False, None, False)
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict):
                continue
            if info.get("kind") == "GoalSpecific":
                goal_info = info.get("goalInfo")
                if (
                    isinstance(goal_info, dict)
                    and goal_info.get("kind") == "NormalForm"
                ):
                    return NormalizeObservation(
                        True, str(goal_info.get("expr", "")), True
                    )
            if info.get("kind") == "NormalForm":
                return NormalizeObservation(True, str(info.get("expr", "")), True)
        return NormalizeObservation(False, None, False)

    def constraint_items(
        self, response: DecodedResponse
    ) -> tuple[ConstraintObservation, ...]:
        # Agda 2.8 can report the same rendered constraint more than once in
        # one `Cmd_constraints` response (notably for blocked dependent
        # constructor problems). ProofState models constraints as an
        # identity-indexed set, so coalesce only field-identical observations
        # after canonical JSON rendering.
        # Distinct problem annotations remain distinct because they are part
        # of the canonical rendered payload and therefore of the digest.
        by_id: dict[str, ConstraintObservation] = {}
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "Constraints":
                continue
            constraints = info.get("constraints", [])
            if not isinstance(constraints, list):
                continue
            for item in constraints:
                if isinstance(item, dict):
                    kind = str(item.get("kind", "constraint"))
                    rendered = json.dumps(item, ensure_ascii=False, sort_keys=True)
                else:
                    kind = "constraint"
                    rendered = str(item)
                observation = ConstraintObservation(
                    constraint_id=hashlib.sha256(rendered.encode()).hexdigest(),
                    kind=kind,
                    rendered=rendered,
                )
                existing = by_id.setdefault(observation.constraint_id, observation)
                if existing != observation:
                    raise ValueError("constraint digest collision")
        return tuple(sorted(by_id.values(), key=lambda item: item.constraint_id))

    def meta_items(self, response: DecodedResponse) -> tuple[MetaObservation, ...]:
        result: list[MetaObservation] = []
        for event in response.events:
            info = event.value.get("info")
            if not isinstance(info, dict) or info.get("kind") != "AllGoalsWarnings":
                continue
            for collection_name, visible in (
                ("visibleGoals", True),
                ("invisibleGoals", False),
            ):
                collection = info.get(collection_name, [])
                if not isinstance(collection, list):
                    continue
                for item in collection:
                    if not isinstance(item, dict):
                        continue
                    constraint = item.get("constraintObj")
                    if not isinstance(constraint, dict):
                        continue
                    raw_identity = constraint.get("id" if visible else "name")
                    if not isinstance(raw_identity, (str, int)):
                        continue
                    interaction = (
                        raw_identity
                        if visible and isinstance(raw_identity, int)
                        else None
                    )
                    meta_id = (
                        f"interaction:{raw_identity}"
                        if interaction is not None
                        else f"agda:{raw_identity}"
                    )
                    result.append(
                        MetaObservation(
                            meta_id=meta_id,
                            type_text=str(item.get("type", "")),
                            source_range=self.source_range(constraint.get("range")),
                            interaction_id=interaction,
                        )
                    )
        return tuple(sorted(result, key=lambda item: item.meta_id))

    @staticmethod
    def source_range(value: object) -> SourceRange:
        if not isinstance(value, list) or not value:
            return SourceRange(0, 0)
        first = value[0]
        if not isinstance(first, dict):
            return SourceRange(0, 0)
        start = first.get("start", {})
        end = first.get("end", {})
        if not isinstance(start, dict) or not isinstance(end, dict):
            return SourceRange(0, 0)
        try:
            return SourceRange(int(start.get("pos", 0)), int(end.get("pos", 0)))
        except (TypeError, ValueError):
            return SourceRange(0, 0)
