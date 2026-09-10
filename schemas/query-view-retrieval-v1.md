# Optional raw/normalized query retrieval

This ranking-only capability is disabled by default. Set
`AGDAPROVER_SCOPED_RETRIEVAL=1` and `AGDAPROVER_SCOPED_QUERY_VIEWS=1` with an
explicitly configured, newly built Agda 2.8 adapter. The latter flag is captured
when the kernel session opens. It requires live scope; it does not silently
enable a different bridge. Older adapters or mismatched responses fail closed.

## Kernel boundary

Live-scope requests use marker `agdaprover:scoped-retrieval:v8:` and response
`agdaprover.live-scope.v8`, or v9 for both when permitted dependencies are enabled.
The closed request retains `excluded_names` and the caller's `output_bytes`.
All v6/v7 fields retain their meanings. The additional required response field is:

```json
{
  "normalized_query": {
    "policy": "agda-normalise-query-type-v1",
    "features": {"result_head": "local:1", "symbols": [], "arity": 0},
    "structure_nodes": 1,
    "conversion_checked": true
  }
}
```

The bridge fully normalizes the instantiated target in the original interaction
telescope, including arguments of neutral heads. It does not close the type and
reinterpret closed binder indices as local coordinates. Agda checks conversion
at relevant relevance under `dontAssignMetas`. Ordinary lookup/reduction retains
abstraction and opacity. Blocked metas remain unknown, not assigned or accepted
as solved. The whole observation runs in the existing speculative transaction.

Scope membership and identity-wide exclusions precede feature projection.
Normalized query tokens come only from aliases of already-allowed declarations;
the view cannot introduce premises. Declaration features and raw query features
are preserved. Source/state/adapter identities bind the complete observation.
The new view's positive node count is included in total `structure_nodes`.
Native CPU, memory, wall time and bytes use the same caller-owned transport
envelope. Output overflow emits the existing closed resource refusal, bound to
the exact v8/v9 request; it never emits a truncated successful scope. No partial
normalization is advertised as full. Old v6/v7 behavior remains unchanged.

## Retrieval and search boundary

`RetrievalQuery.normalized` optionally carries a `NormalizedQueryView` with the
checked policy, `TypeFeatures` and authorized alias tokens. It changes query
identity, not an existing index's membership or identity. With no alternate view,
query identities, rankings and serialized results remain unchanged.

Both views use the same index and requested ranking lanes. Their rankings are
interleaved raw-first, skipping duplicate declaration identities. Computing each
view's top k suffices for the merged top k, so output widths are prefix-stable
without sorting or retaining the whole ranked population. Identical feature and
token views require only one scoring pass. Normalization itself is still charged.

Result `agdaprover.symbolic-retrieval.v5` binds policy
`raw-normalized-query-interleave-v1/<single-view-policy>`, plus
`normalized_query_policy` and `query_views_scored` (one or two). `candidate_count`
is the unchanged allowed population; `scored_count` counts candidate/view pairs.
Posting and dependency-posting work sums the actual view passes. Each item adds
`query_view` (`raw` or `normalized`) and its one-based `query_view_rank`.
Its ordinary components belong to that emitting view, not an unexplained maximum
or mixture of incompatible presentations. A view rank is not the merged rank.
The aggregate `scoped_retrieval_extra_candidate_views` counter retains additional
scoring work even when bounded decision traces are omitted; it is absent at zero
to preserve disabled-policy telemetry.

Scoped search decision v7 records the policy, view count, work and item provenance.
Existing progressive admission remains a separate heuristic over that pool.
Shared OR/NNUE metadata receives the emitting view and view rank alongside the
existing components. No trained weights, allowed actions or proof authority are
changed. Cancellation/exhaustion cannot publish a partial merged ranking or
mutate the immutable index. Final proofs still require fresh Agda validation.

This capability is not a default promotion, complete typed-term reconstruction,
or a claim that normalization is inexpensive. Downstream and corpus qualification
must include its additional cost, gains and losses under the same allowances.
