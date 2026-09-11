"""Kernel-backed declaration catalogues for one lexical module scope."""

from __future__ import annotations

from .bridge.contracts import StateToken
from .contracts import GoalInfo
from .kernel.protocol import (
    ScopeDeclarationSession,
    TermInferenceSession,
    TransactionalKernelSession,
)
from .type_syntax import result_head


def visible_scope_declarations(
    session: ScopeDeclarationSession,
    state: StateToken,
    goal: GoalInfo,
) -> tuple[tuple[tuple[str, str], ...], int]:
    """Return current and opened-module declarations with query provenance.

    Agda's empty module-contents query reports declarations introduced in the
    current module, but not declarations made visible by ``open`` directives.
    The source-derived module scope supplies those module names; Agda remains
    authoritative for their exported contents and later accepts or rejects
    every proposed use.  Restrictions and renamings may leave conservative
    extras in this heuristic catalogue, never authorize a proof action.
    """

    declarations = list(session.scope_declarations(state, goal_id=goal.goal_id))
    queries = 1
    if goal.module_scope is not None and isinstance(
        session, TransactionalKernelSession
    ):
        opened = tuple(
            dict.fromkeys(
                directive.target
                for directive in goal.module_scope.directives
                if directive.kind in {"open", "open-module-alias"}
            )
        )
        for module_name in opened:
            declarations.extend(
                session.constructor_candidates(
                    state,
                    goal_id=goal.goal_id,
                    type_head=module_name,
                )
            )
            queries += 1
    if isinstance(session, TermInferenceSession):
        # Empty module-contents also omits outer lexical declarations inside
        # parameterized sections. Resolve heads actually observed in the goal
        # and telescope through Agda, under their local spelling. This neither
        # invents a global name nor bypasses hiding/renaming restrictions.
        known = (
            {name for name, _ in declarations}
            | {e.name for e in goal.context}
            | set(goal.sort_names)
        )
        heads = tuple(
            dict.fromkeys(
                result_head(ty) for ty in (goal.target, *(e.type for e in goal.context))
            )
        )
        for head in heads:
            if not head or head in known:
                continue
            inferred = session.infer_type(state, goal_id=goal.goal_id, expression=head)
            queries += 1
            if inferred is not None:
                declarations.append((head, inferred))
    return tuple(dict.fromkeys(declarations)), queries


__all__ = ["visible_scope_declarations"]
