"""Policy selection and exact input lineage for one contextual-evidence closure.

One instance belongs to one parent state and interaction. It does not infer
types, discover premises, inspect final proof text or publish validation credit.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from ..contracts import GoalInfo
from ..observability.policy_trace import PolicyChoice
from ..or_policy import ORPolicyRouter, policy_candidate
from ..reasoning.evidence import EvidenceApplication, explicit_domains
from ..resource_budget import checkpoint


@dataclass(frozen=True)
class EvidenceSelection:
    application: EvidenceApplication
    choice: PolicyChoice | None


class EvidencePolicy:
    def __init__(self, router: ORPolicyRouter, goal: GoalInfo) -> None:
        self.router = router
        self.goal = goal
        self._choices: dict[str, tuple[PolicyChoice, ...]] = {}

    def select(
        self, proposals: Iterable[EvidenceApplication], *, expected_type: bool = False
    ) -> EvidenceSelection | None:
        # Materialize only this actual frontier, not a beam or invented actions.
        distinct: dict[str, EvidenceApplication] = {}
        for proposal in sorted(
            proposals, key=lambda p: (p.depth, len(p.expression), p.expression)
        ):
            checkpoint()
            distinct.setdefault(proposal.expression, proposal)
        if not distinct:
            return None
        candidates = tuple(
            policy_candidate(
                family="evidence-application-v1",
                tag=(
                    "check-evidence-application"
                    if expected_type
                    else "infer-evidence-application"
                ),
                expression=p.expression,
                type_text=p.function.type_text,
                symbolic_key=(p.depth, len(p.expression), p.expression),
                metadata=(
                    ("application-depth", str(p.depth)),
                    ("argument-count", str(len(p.arguments))),
                    ("derived-arguments", str(sum(a.depth > 0 for a in p.arguments))),
                    ("derived-function", str(p.function.depth > 0)),
                    (
                        "function-arity",
                        str(len(explicit_domains(p.function.type_text))),
                    ),
                ),
            )
            for p in distinct.values()
        )
        ranked = self.router.rank(self.goal, candidates)
        chosen = ranked.candidates[0]
        choice = (
            PolicyChoice(ranked.decision_id, chosen.candidate_id)
            if ranked.decision_id
            else None
        )
        return EvidenceSelection(distinct[chosen.expression], choice)

    def dependencies(self, expressions: Iterable[str]) -> tuple[PolicyChoice, ...]:
        """Look up actual constructed inputs, never substrings of output text."""
        return tuple(
            dict.fromkeys(
                choice
                for expression in expressions
                for choice in self._choices.get(expression, ())
            )
        )

    def retain(self, selection: EvidenceSelection) -> None:
        application = selection.application
        inherited = self.dependencies(
            t.expression for t in (application.function, *application.arguments)
        )
        self._choices[application.expression] = tuple(
            dict.fromkeys(
                (*inherited, *((selection.choice,) if selection.choice else ()))
            )
        )
