"""Datatype-polymorphic elimination proposals for zero-constructor results.

The generator never identifies an empty type. It builds bounded local
applications and asks Agda whether an absurd pattern eliminates their result.
Thus zero constructors, impossible indices, and all other rejection/acceptance
decisions remain consequences of the datatype definitions known to the kernel.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from .contracts import GoalInfo
from .focused import TypeExpr, parse_type
from .terms import Term, render_term

ZERO_CONSTRUCTOR_ACTION_SCHEMA = "agdaprover.zero-constructor-action.v1"


@dataclass(frozen=True)
class ZeroConstructorEliminationAction:
    scrutinee: Term
    displayed_type: str
    target_type: str
    helper_name: str
    application_count: int
    schema_version: str = ZERO_CONSTRUCTOR_ACTION_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != ZERO_CONSTRUCTOR_ACTION_SCHEMA:
            raise ValueError("unsupported zero-constructor action schema")
        if self.application_count < 0:
            raise ValueError("zero-constructor application count cannot be negative")
        if not self.displayed_type or not self.target_type or not self.helper_name:
            raise ValueError("zero-constructor proposal requires displayed types")

    @property
    def expression(self) -> str:
        return (
            f"let {self.helper_name} : ({self.displayed_type}) → _; "
            f"{self.helper_name} = λ () in "
            f"{self.helper_name} ({render_term(self.scrutinee)})"
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "tag": "eliminate-by-zero-constructor-pattern",
            "scrutinee": self.scrutinee.to_dict(),
            "displayed_type": self.displayed_type,
            "target_type": self.target_type,
            "helper_name": self.helper_name,
            "application_count": self.application_count,
            "expression": self.expression,
            "elaboration": "agda-candidate-check",
            "datatype_assumption": "none",
        }

    @classmethod
    def from_dict(cls, value: dict[str, Any]) -> ZeroConstructorEliminationAction:
        if value.get("schema_version") != ZERO_CONSTRUCTOR_ACTION_SCHEMA:
            raise ValueError("unsupported zero-constructor action schema")
        if value.get("tag") != "eliminate-by-zero-constructor-pattern":
            raise ValueError("unsupported zero-constructor action tag")
        if value.get("datatype_assumption") != "none":
            raise ValueError("zero-constructor action contains a datatype assumption")
        try:
            action = cls(
                scrutinee=Term.from_dict(value["scrutinee"]),
                displayed_type=str(value["displayed_type"]),
                target_type=str(value["target_type"]),
                helper_name=str(value["helper_name"]),
                application_count=int(value["application_count"]),
            )
        except (KeyError, TypeError, ValueError) as error:
            raise ValueError("malformed zero-constructor action") from error
        if value.get("expression") != action.expression:
            raise ValueError("zero-constructor action expression mismatch")
        return action


@dataclass(frozen=True)
class _TypedTerm:
    term: Term
    type_expr: TypeExpr
    application_count: int


def generate_zero_constructor_actions(
    goal: GoalInfo,
    *,
    max_actions: int,
    max_rounds: int = 4,
    max_term_size: int = 32,
    max_terms: int = 256,
) -> tuple[ZeroConstructorEliminationAction, ...]:
    """Forward-chain bounded local applications, without inspecting type heads."""

    if max_actions <= 0 or max_rounds <= 0 or max_term_size <= 0 or max_terms <= 0:
        return ()
    terms: list[_TypedTerm] = []
    inhabitants: dict[TypeExpr, list[_TypedTerm]] = {}
    seen: set[tuple[Term, TypeExpr]] = set()

    def retain(typed: _TypedTerm) -> bool:
        key = (typed.term, typed.type_expr)
        if key in seen or typed.term.size > max_term_size or len(terms) >= max_terms:
            return False
        seen.add(key)
        terms.append(typed)
        inhabitants.setdefault(typed.type_expr, []).append(typed)
        return True

    for entry in goal.context:
        if not entry.in_scope or not entry.name:
            continue
        try:
            type_expr = parse_type(entry.type)
        except ValueError:
            continue
        retain(_TypedTerm(Term.local(entry.name), type_expr, 0))
        if len(terms) >= max_terms:
            break

    actions: list[ZeroConstructorEliminationAction] = []
    action_terms: set[Term] = set()
    local_names = {entry.name for entry in goal.context if entry.name}
    helper_name = "agdaprover-eliminate"
    suffix = 0
    while helper_name in local_names:
        suffix += 1
        helper_name = f"agdaprover-eliminate{suffix}"

    def retain_action(typed: _TypedTerm) -> None:
        if (
            typed.type_expr.tag != "atom"
            or typed.term in action_terms
            or len(actions) >= max_actions
        ):
            return
        action_terms.add(typed.term)
        actions.append(
            ZeroConstructorEliminationAction(
                scrutinee=typed.term,
                displayed_type=typed.type_expr.canonical(),
                target_type=goal.target,
                helper_name=helper_name,
                application_count=typed.application_count,
            )
        )

    # Derived contradictions are normally more selective than direct locals, so
    # retain them first.  The direct-local fallback is nevertheless essential:
    # a parameter of an arbitrary zero-constructor family must close an
    # unrelated target without the engine knowing that family's name.
    for _round in range(max_rounds):
        changed = False
        snapshot = tuple(terms)
        for function in snapshot:
            domains, result = function.type_expr.domains_and_result()
            if not domains:
                continue
            arguments: list[_TypedTerm] = []
            for domain in domains:
                available = inhabitants.get(domain)
                if not available:
                    break
                arguments.append(available[0])
            else:
                applied = function.term
                application_count = function.application_count
                for argument in arguments:
                    applied = Term.app(applied, argument.term)
                    application_count += 1 + argument.application_count
                candidate = _TypedTerm(applied, result, application_count)
                if retain(candidate):
                    changed = True
                    retain_action(candidate)
                    if len(actions) >= max_actions:
                        return tuple(actions)
        if not changed:
            break
    for typed in terms:
        if typed.application_count == 0:
            retain_action(typed)
            if len(actions) >= max_actions:
                break
    return tuple(actions)
