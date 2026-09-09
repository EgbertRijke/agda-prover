"""Stable source-file and lexical-module analysis boundary."""

from ..bridge.source_text import (
    mask_agda_source,
    mask_comments_and_strings,
    mask_literate_markdown,
)
from ..module_scope import ModuleScope, analyze_module_scope, attach_module_scope
from ..source_files import (
    AGDA_SOURCE_SUFFIXES,
    PROVER_SOURCE_SUFFIXES,
    agda_interface_path,
    agda_source_suffix,
    is_agda_source_path,
    is_prover_source_path,
    iter_agda_source_files,
    require_agda_source_file,
)

__all__ = [
    "AGDA_SOURCE_SUFFIXES",
    "PROVER_SOURCE_SUFFIXES",
    "ModuleScope",
    "agda_interface_path",
    "agda_source_suffix",
    "analyze_module_scope",
    "attach_module_scope",
    "is_agda_source_path",
    "is_prover_source_path",
    "iter_agda_source_files",
    "mask_agda_source",
    "mask_comments_and_strings",
    "mask_literate_markdown",
    "require_agda_source_file",
]
