"""Symbolic action-provider and structural-classification boundary."""

from .classifications import (
    STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION,
    StructuralClassification,
    classify_structural_scheduling,
    has_relational_context_evidence,
    has_relational_elimination_shape,
    has_result_subject_elimination_shape,
    is_higher_order_structural_field,
    is_reflexive_relation_target,
    reorders_homogeneous_coordinates,
)
from .providers import (
    ActionProposal,
    ActionProvider,
    ProposalBatch,
    RefinementActionProvider,
    refinement_action_provider,
)

__all__ = [
    "ActionProposal",
    "ActionProvider",
    "ProposalBatch",
    "RefinementActionProvider",
    "STRUCTURAL_CLASSIFICATION_SCHEMA_VERSION",
    "StructuralClassification",
    "classify_structural_scheduling",
    "has_relational_context_evidence",
    "has_relational_elimination_shape",
    "has_result_subject_elimination_shape",
    "is_higher_order_structural_field",
    "is_reflexive_relation_target",
    "refinement_action_provider",
    "reorders_homogeneous_coordinates",
]
