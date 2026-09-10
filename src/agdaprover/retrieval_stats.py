"""Bounded retrieval telemetry shared by nested search controllers."""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Literal

TraceKind = Literal["decisions", "widenings"]
TRACE_BYTES = 1024**2
TRACE_RECORDS = 64


@dataclass(kw_only=True)
class ScopedRetrievalStats:
    scoped_retrieval_queries: int = 0
    scoped_retrieval_candidates: int = 0
    scoped_retrieval_extra_candidate_views: int = 0
    scoped_retrieval_postings: int = 0
    scoped_retrieval_nodes: int = 0
    scoped_retrieval_elapsed_ms: float = 0.0
    scoped_retrieval_decisions: list[dict[str, object]] = field(default_factory=list)
    scoped_retrieval_decisions_omitted: int = 0
    scoped_retrieval_widenings: list[dict[str, object]] = field(default_factory=list)
    scoped_retrieval_widenings_omitted: int = 0
    scoped_retrieval_refinement_reuses: int = 0
    scoped_retrieval_frontier_pruned: int = 0
    scoped_retrieval_composition_head_deferrals: int = 0
    scoped_retrieval_index_builds: int = 0
    scoped_retrieval_incremental_builds: int = 0
    scoped_retrieval_index_build_elapsed_ms: float = 0.0
    scoped_retrieval_index_feature_rows_reused: int = 0
    scoped_retrieval_index_posting_updates: int = 0
    _scoped_trace_bytes: int = field(default=0, init=False, repr=False)

    def record_retrieval(self, kind: TraceKind, record: dict[str, object]) -> None:
        if kind not in ("decisions", "widenings"):
            raise ValueError("unknown retrieval trace kind")
        records = getattr(self, f"scoped_retrieval_{kind}")
        size = len(json.dumps(record, ensure_ascii=False).encode())
        if (
            len(records) < TRACE_RECORDS
            and self._scoped_trace_bytes + size <= TRACE_BYTES
        ):
            records.append(record)
            self._scoped_trace_bytes += size
        else:
            omitted = f"scoped_retrieval_{kind}_omitted"
            setattr(self, omitted, getattr(self, omitted) + 1)

    def merge_retrieval(self, source: ScopedRetrievalStats) -> None:
        if source is self:
            raise ValueError("cannot accumulate retrieval telemetry into itself")
        if not source.scoped_retrieval_queries:
            return
        for name in (
            "queries",
            "candidates",
            "extra_candidate_views",
            "postings",
            "nodes",
            "elapsed_ms",
            "refinement_reuses",
            "frontier_pruned",
            "composition_head_deferrals",
            "index_builds",
            "incremental_builds",
            "index_build_elapsed_ms",
            "index_feature_rows_reused",
            "index_posting_updates",
        ):
            field_name = f"scoped_retrieval_{name}"
            setattr(
                self,
                field_name,
                getattr(self, field_name) + getattr(source, field_name),
            )
        for kind in ("decisions", "widenings"):
            for record in getattr(source, f"scoped_retrieval_{kind}"):
                self.record_retrieval(kind, record)
            omitted = f"scoped_retrieval_{kind}_omitted"
            setattr(self, omitted, getattr(self, omitted) + getattr(source, omitted))

    def stats_dict(self) -> dict[str, object]:
        return {
            name: value
            for name, value in self.__dict__.items()
            if value is not None
            and not name.startswith("_")
            and (name != "scoped_retrieval_extra_candidate_views" or value != 0)
            and (
                self.scoped_retrieval_queries
                or not name.startswith("scoped_retrieval_")
            )
        }
