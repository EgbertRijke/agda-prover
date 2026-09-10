"""User-facing effort presets; resolved before invoking shared search."""

from dataclasses import dataclass


@dataclass(frozen=True)
class SearchProfile:
    name: str
    max_candidates: int


def search_profile(name: str) -> SearchProfile:
    """Presets alter effort, never kernel policy, candidate rules or proof semantics."""

    if name == "standard":
        return SearchProfile(name, 500)
    if name == "deep":
        return SearchProfile(name, 8_000)
    raise ValueError(f"unknown search profile: {name!r}; expected standard or deep")
