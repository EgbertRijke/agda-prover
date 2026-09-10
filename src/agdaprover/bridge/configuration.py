"""Translate frontend checking configuration at the kernel boundary."""

from pathlib import Path

from ..project_configuration import ProjectConfiguration
from .operations import OpenProjectRequest


def project_request(
    source: Path,
    configuration: ProjectConfiguration | None = None,
    *,
    executable: str = "agda",
) -> OpenProjectRequest:
    if configuration is None:
        return OpenProjectRequest(source, executable=executable)
    return OpenProjectRequest(
        source,
        executable=configuration.executable,
        options=configuration.options,
        library_file=configuration.library_file,
    )
