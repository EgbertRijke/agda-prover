"""Role-checked paths and identities for native inference, not a ranking policy."""

from dataclasses import dataclass, replace
from pathlib import Path

from ..contracts import TaskSpec
from ..ranking.bundled import FOCUSED_MODEL, OR_MODEL, STEP_MODEL
from ..ranking.runtime import load_or_model, load_proof_models, load_step_model


@dataclass(frozen=True)
class NativeModels:
    primary_path: Path | None
    or_path: Path | None
    identities: dict[str, str]
    primary_role: str | None

    @property
    def primary_id(self) -> str | None:
        return self.identities.get(self.primary_role) if self.primary_role else None

    @property
    def or_id(self) -> str | None:
        return self.identities.get("or-decision-ranking")

    @property
    def mode(self) -> str:
        # Opt-out removes models by role at loading. The native router may
        # still use an explicitly supplied OR model with a symbolic primary.
        return "nnue" if self.identities else "symbolic"


def load_native_models(
    task: TaskSpec,
    *,
    one_move: bool,
    policy_override: Path | None,
    deadline: float | None,
) -> NativeModels:
    if policy_override is not None:
        if (
            task.action_model_path is not None
            and task.action_model_path.resolve() != policy_override.resolve()
        ):
            raise ValueError("conflicting native policy_model and --action-model")
        task = replace(task, action_model_path=policy_override)
    primary_role = None
    primary_id = None
    if one_move:
        primary = load_step_model(task, deadline=deadline)
        policy = load_or_model(task, deadline=deadline)
        policy_id = policy.model_id if policy else None
        default_path = STEP_MODEL.path
        if primary is not None:
            primary_id, primary_role = primary.model_id, "one-step-refinement-ranking"
    else:
        loaded = load_proof_models(task, deadline=deadline, command="prove")
        primary_id, policy_id = loaded.primary_id, loaded.refinement_id
        default_path = FOCUSED_MODEL.path
        if primary_id is not None:
            primary_role = (
                "proof-term-ranking"
                if loaded.term is not None
                else "focused-search-branch-policy"
            )
    identities = {}
    if primary_id is not None and primary_role is not None:
        identities[primary_role] = primary_id
    if policy_id is not None:
        identities["or-decision-ranking"] = policy_id
    return NativeModels(
        (task.model_path or default_path) if primary_id else None,
        (task.action_model_path or OR_MODEL.path) if policy_id else None,
        identities,
        primary_role,
    )
