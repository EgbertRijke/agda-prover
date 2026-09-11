"""Branch-local, fair expansion of newly admitted evidence.

The caller owns typing, admission, identities, ranking and resource limits.
An expansion is lazy: discovering evidence need not materialize its entire
application cross product. Discovery order never makes an expansion disappear.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Hashable, Iterator
from typing import Generic, TypeVar

Proposal = TypeVar("Proposal")


class EvidenceAgenda(Generic[Proposal]):
    """Interleave one proposal per expansion without repeating its admission.

    Keys identify exact evidence in one immutable parent state, not merely
    types or relation endpoints. Distinct witnesses can have distinct futures.
    The caller must create a new agenda for a different state or interaction.
    """

    def __init__(self) -> None:
        self._keys: set[Hashable] = set()
        self._pending: deque[Iterator[Proposal]] = deque()
        self.peak_pending = 0

    def add(self, key: Hashable, proposals: Iterator[Proposal]) -> bool:
        if key in self._keys:
            return False
        self._keys.add(key)
        self._pending.append(proposals)
        self.peak_pending = max(self.peak_pending, len(self._pending))
        return True

    def pop(self) -> Proposal | None:
        """Return the next proposal, or None when all expansions are drained."""
        while self._pending:
            proposals = self._pending.popleft()
            try:
                proposal = next(proposals)
            except StopIteration:
                continue
            self._pending.append(proposals)
            return proposal
        return None

    @property
    def pending(self) -> int:
        return len(self._pending)
