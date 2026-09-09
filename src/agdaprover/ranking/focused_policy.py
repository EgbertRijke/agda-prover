"""Incremental focused-search policy over the sparse ranking protocol."""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import Sequence
from dataclasses import dataclass

from ..focused import (
    Assumption,
    FocusedAction,
    TypeExpr,
    focused_action_feature_tokens,
    focused_state_feature_tokens,
)
from .features import hash_features, sparse_delta
from .protocol import SparsePolicyRanker


@dataclass
class FocusedPolicy:
    """Cache and incrementally update state accumulators for focused search."""

    model: SparsePolicyRanker
    cache_capacity: int = 4096

    def __post_init__(self) -> None:
        if self.cache_capacity <= 0:
            raise ValueError("focused policy cache capacity must be positive")
        self.model.require_role("focused-search-branch-policy")
        self._cache: OrderedDict[tuple[str, ...], list[float]] = OrderedDict()
        self._last_features: dict[int, float] | None = None
        self._last_accumulator: list[float] | None = None
        self.cache_hits = 0
        self.full_refreshes = 0
        self.incremental_updates = 0
        self.incremental_features_touched = 0
        self.actions_scored = 0

    def score_actions(
        self,
        goal: TypeExpr,
        assumptions: tuple[Assumption, ...],
        actions: Sequence[FocusedAction],
    ) -> list[float]:
        state_tokens = focused_state_feature_tokens(goal, assumptions)
        state_features = hash_features(state_tokens, self.model.input_size)
        cached = self._cache.get(state_tokens)
        if cached is not None:
            self.cache_hits += 1
            self._cache.move_to_end(state_tokens)
            accumulator = cached
        elif self._last_features is None or self._last_accumulator is None:
            self.full_refreshes += 1
            accumulator = self.model.accumulator(state_features)
        else:
            self.incremental_updates += 1
            remove, add = sparse_delta(self._last_features, state_features)
            self.incremental_features_touched += len(remove) + len(add)
            accumulator = self.model.update_accumulator(
                self._last_accumulator,
                remove=remove,
                add=add,
            )
        if cached is None:
            self._cache[state_tokens] = accumulator
            if len(self._cache) > self.cache_capacity:
                self._cache.popitem(last=False)
        self._last_features = state_features
        self._last_accumulator = accumulator

        self.actions_scored += len(actions)
        return self.model.score_feature_batches(
            accumulator,
            tuple(
                hash_features(
                    focused_action_feature_tokens(goal, assumptions, action),
                    self.model.input_size,
                )
                for action in actions
            ),
        )

    def metrics(self) -> dict[str, int]:
        return {
            "cache_hits": self.cache_hits,
            "full_refreshes": self.full_refreshes,
            "incremental_updates": self.incremental_updates,
            "incremental_features_touched": self.incremental_features_touched,
            "actions_scored": self.actions_scored,
            "cached_states": len(self._cache),
        }


__all__ = ["FocusedPolicy"]
