"""Deterministic proof rendering and source-reconstruction boundary.

Search controllers request presentation operations here. The implementation
remains in the prototype's compatibility modules so public imports and golden
rendering behavior stay unchanged during the architectural migration.
"""

from ..proof_formatter import format_proof_term
from ..reconstruction import (
    apply_source_edit,
    declaration_name_at_goal,
    guided_clause_region,
    reconstruct_case_split,
    reconstruct_checked_clause_completion,
    reconstruct_guided_completion,
    reconstruct_hole_completion,
    reconstruct_intro_as_clause,
    reconstruct_joint_completion,
    reconstruct_term_as_clause,
)

__all__ = [
    "apply_source_edit",
    "declaration_name_at_goal",
    "format_proof_term",
    "guided_clause_region",
    "reconstruct_case_split",
    "reconstruct_checked_clause_completion",
    "reconstruct_guided_completion",
    "reconstruct_hole_completion",
    "reconstruct_intro_as_clause",
    "reconstruct_joint_completion",
    "reconstruct_term_as_clause",
]
