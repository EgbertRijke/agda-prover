"""Exact deterministic frontier ordering shared by symbolic search engines."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Generic, TypeVar

_T = TypeVar("_T")


@dataclass(frozen=True)
class _FrontierItem(Generic[_T]):
    priority: tuple[int, ...]
    sequence: int
    payload: _T


class BatchedFrontier(Generic[_T]):
    """Order a batch exactly by priority and stable insertion sequence."""

    def __init__(self) -> None:
        self._items: list[_FrontierItem[_T]] = []
        self._ordered: list[_FrontierItem[_T]] = []

    def push(self, priority: tuple[int, ...], sequence: int, payload: _T) -> None:
        self._items.append(_FrontierItem(priority, sequence, payload))

    def extend(self, items: Sequence[tuple[tuple[int, ...], int, _T]]) -> None:
        self._items.extend(_FrontierItem(*item) for item in items)

    def _flush(self) -> None:
        if not self._items:
            return
        combined = self._ordered + self._items
        self._items = []
        self._ordered = sorted(
            combined,
            key=lambda item: (item.priority, item.sequence),
            reverse=True,
        )

    def pop(self) -> _T:
        self._flush()
        if not self._ordered:
            raise IndexError("pop from empty frontier")
        return self._ordered.pop().payload

    def __len__(self) -> int:
        return len(self._items) + len(self._ordered)


__all__ = ["BatchedFrontier"]
