"""Pure declaration-boundary values shared by parsing and presentation."""

from dataclasses import dataclass


@dataclass(frozen=True)
class SourceEntry:
    name: str
    parts: tuple[tuple[int, int], ...]
    reason: str = ""

    @property
    def start(self) -> int:
        return self.parts[0][0]
