"""Pure source-project policies shared by all solver use cases."""

from .goals import choose_goal, choose_goal_prefix
from .sources import (
    ModuleScope,
    agda_source_suffix,
    analyze_module_scope,
    attach_module_scope,
    iter_agda_source_files,
    require_agda_source_file,
)

__all__ = [
    "ModuleScope",
    "agda_source_suffix",
    "analyze_module_scope",
    "attach_module_scope",
    "choose_goal",
    "choose_goal_prefix",
    "iter_agda_source_files",
    "require_agda_source_file",
]
