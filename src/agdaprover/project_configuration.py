"""Explicit, portable checking inputs shared by tasks and frontends.

This is configuration, not proof authority or a resolved project snapshot.
The kernel resolver pins the executable, libraries and sources before checking.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any

PROJECT_CONFIGURATION_SCHEMA = "agdaprover.project-configuration.v1"


@dataclass(frozen=True)
class ProjectConfiguration:
    executable: str = "agda"
    library_file: Path | None = None
    options: tuple[str, ...] = ("--without-K", "--exact-split")

    def __post_init__(self) -> None:
        if (
            not isinstance(self.executable, str)
            or not self.executable.strip()
            or "\x00" in self.executable
        ):
            raise ValueError("Agda executable must be nonempty text")
        if self.library_file is not None:
            if not isinstance(self.library_file, Path):
                raise ValueError("library_file must be a Path or null")
            object.__setattr__(
                self, "library_file", self.library_file.expanduser().resolve()
            )
        if len(Path(self.executable).parts) > 1 or self.executable.startswith("~"):
            object.__setattr__(
                self, "executable", str(Path(self.executable).expanduser().resolve())
            )
        if not isinstance(self.options, tuple) or not all(
            isinstance(option, str) for option in self.options
        ):
            raise ValueError("Agda options must be a tuple of strings")
        # Process, filesystem and library routing belong to the bridge, not
        # unchecked command-line fragments. Agda decides pragma applicability.
        forbidden = {
            "--include-path",
            "--library",
            "--library-file",
            "--no-libraries",
            "--no-default-libraries",
            "--local-interfaces",
            "--ignore-interfaces",
            "--only-scope-checking",
            "--interaction",
            "--interaction-json",
            "--compile",
            "--compile-dir",
            "--html",
            "--html-dir",
            "--latex",
            "--latex-dir",
            "--vim",
            "--dependency-graph",
            "--help",
            "--version",
            "--print-agda-dir",
            "--print-agda-app-dir",
        }
        for option in self.options:
            if (
                not option.startswith("--")
                or len(option.encode()) > 4096
                or any(
                    character.isspace() or character == "\x00" for character in option
                )
                or option.split("=", 1)[0] in forbidden
            ):
                raise ValueError(f"not a project checking option: {option!r}")

    @classmethod
    def from_dict(cls, value: object) -> ProjectConfiguration:
        if not isinstance(value, dict) or set(value) != {
            "schema_version",
            "executable",
            "library_file",
            "options",
        }:
            raise ValueError("malformed project configuration")
        if value["schema_version"] != PROJECT_CONFIGURATION_SCHEMA:
            raise ValueError("unsupported project configuration schema")
        library = value["library_file"]
        if library is not None and (
            not isinstance(library, str) or not library or "\x00" in library
        ):
            raise ValueError("library_file must be nonempty text or null")
        options = value["options"]
        if not isinstance(options, list):
            raise ValueError("project options must be an array")
        return cls(
            value["executable"],
            Path(library) if library is not None else None,
            tuple(options),
        )

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": PROJECT_CONFIGURATION_SCHEMA,
            "executable": self.executable,
            "library_file": str(self.library_file)
            if self.library_file is not None
            else None,
            "options": list(self.options),
        }
