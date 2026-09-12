"""User-facing effort presets; resolved before invoking shared search."""

from dataclasses import dataclass


@dataclass(frozen=True)
class SearchProfile:
    name: str
    max_candidates: int | None


def search_profile(name: str) -> SearchProfile:
    """Compatibility names; whole-run action ceilings are now opt-in only."""

    if name == "standard":
        return SearchProfile(name, None)
    if name == "deep":
        return SearchProfile(name, None)
    raise ValueError(f"unknown search profile: {name!r}; expected standard or deep")
