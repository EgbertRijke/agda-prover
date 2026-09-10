"""Role-checked loading of rankers at the application/search boundary."""

from __future__ import annotations

from dataclasses import dataclass

from ..artifacts import optional_file_sha256
from ..contracts import TaskSpec
from ..nnue import NNUEModel
from .bundled import FOCUSED_MODEL, OR_MODEL, STEP_MODEL
from .protocol import ProofTermRanker, SparsePolicyRanker, StepActionRanker


@dataclass(frozen=True)
class LoadedProofModels:
    term: ProofTermRanker | None
    focused: SparsePolicyRanker | None
    refinement: SparsePolicyRanker | None
    primary_id: str | None
    refinement_id: str | None


def configured_model_ids(
    task: TaskSpec, *, deadline: float | None, command: str = "prove"
) -> dict[str, str | None]:
    """Hash configured model artifacts before their role is interpreted."""

    if command == "step":
        paths = {
            "step": (task.model_path or STEP_MODEL.path)
            if task.ranker == "nnue"
            else None
        }
    else:
        paths = {
            "primary": (task.model_path or FOCUSED_MODEL.path)
            if task.ranker == "nnue"
            else None,
            "refinement": task.action_model_path
            or (OR_MODEL.path if task.ranker == "nnue" else None),
        }
    return {
        role: optional_file_sha256(path, deadline=deadline)
        for role, path in paths.items()
    }


def load_proof_models(
    task: TaskSpec,
    *,
    deadline: float | None,
    command: str,
) -> LoadedProofModels:
    """Load the proof and shared OR-policy models for one search operation."""

    term: ProofTermRanker | None = None
    focused: SparsePolicyRanker | None = None
    refinement: SparsePolicyRanker | None = None
    primary_id: str | None = None
    refinement_id: str | None = None
    if task.ranker == "nnue":
        primary = (
            NNUEModel.load(task.model_path, deadline=deadline)
            if task.model_path is not None
            else FOCUSED_MODEL.load(deadline=deadline)
        )
        primary_id = primary.model_id
        if primary.role == "proof-term-ranking":
            term = primary
        elif primary.role == "focused-search-branch-policy":
            focused = primary
        else:
            raise ValueError(
                f"the {command} --model must rank proof terms or focused branches"
            )
    if task.action_model_path is not None:
        concrete_refinement = NNUEModel.load(
            task.action_model_path,
            expected_role="or-decision-ranking",
            deadline=deadline,
        )
        refinement = concrete_refinement
        refinement_id = concrete_refinement.model_id
    elif task.ranker == "nnue":
        refinement = OR_MODEL.load(deadline=deadline)
        refinement_id = refinement.model_id
    return LoadedProofModels(
        term,
        focused,
        refinement,
        primary_id,
        refinement_id,
    )


def load_step_model(
    task: TaskSpec, *, deadline: float | None
) -> StepActionRanker | None:
    """Load the optional one-step ranker with its exact role contract."""

    if task.ranker != "nnue":
        return None
    if task.model_path is None:
        return STEP_MODEL.load(deadline=deadline)
    return NNUEModel.load(
        task.model_path,
        expected_role="one-step-refinement-ranking",
        deadline=deadline,
    )
