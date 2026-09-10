# Optional type-family query evidence

This Agda 2.8 capability is off by default. Set
`AGDAPROVER_SCOPED_RETRIEVAL=1` and
`AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY=1` with the explicitly configured embedded
adapter. The latter option is captured when the session opens and is mutually
exclusive with `AGDAPROVER_SCOPED_QUERY_VIEWS=1`. It does not enable the bridge
implicitly. Older or mismatched responses fail closed.

## Native boundary

The marker is `agdaprover:scoped-retrieval:v10:` and the response schema is
`agdaprover.live-scope.v10`; both use v11 with permitted dependencies. The closed
request retains the exclusions and caller-owned output reservation. Raw v6/v7
fields retain their meanings. The additional required field is:

```json
{
  "type_family_query": {
    "policy": "agda-type-family-whnf-query-v1",
    "status": "checked",
    "features": {"result_head": "local:1", "symbols": [], "arity": 0},
    "structure_nodes": 1,
    "conversion_checked": true,
    "term_visits": 2,
    "type_position_reductions": 1
  }
}
```

Agda's internal typed traversal visits the original instantiated query in its
interaction telescope. At each term, its inferred type decides whether to
weak-head reduce: universes and functions returning universes qualify. Ordinary
value/function positions receive an identity pre-action, not explicit unfolding;
Agda's typed traversal can still reconstruct their syntax. This is **not full
normalization**, canonical identity, or evidence of premise applicability.
Ordinary abstraction/opacity rules apply. Binder coordinates are not changed
by artificially closing the query.

The attempt runs in a local Agda state under `dontAssignMetas`. Relevant
conversion must succeed without new blocking or nonblocking constraints;
the fresh-meta counter must not advance. Success and failure both restore
the parent state. Typechecking rejection or a blocked internal traversal returns
`kernel-rejected`, null features, zero structure nodes and false conversion.
Process/IO errors and cancellation propagate normally, not as safe misses.

When the complete response exceeds the output reservation but a complete raw
scope with reduction metadata fits, the alternate features alone are discarded:
status becomes `output-limited`, features null and conversion remains true.
The attempted positive structure count and traversal work remain recorded.
If even that complete response does not fit, the existing closed scope resource
refusal is emitted, bound to v10/v11. No allowed declaration is truncated.
Whole-request CPU/memory/deadline exhaustion is still `resource-exhausted`;
there is no hidden extra allowance or attempt to continue a killed transport.

Both views obtain lexical tokens only from already-authorized aliases. Native
exclusions precede feature construction. Source, state, adapter, request and
observation identities bind the result. `structure_nodes` includes the alternate
feature traversal; `term_visits` and `type_position_reductions` count the typed
traversal separately, with `0 ≤ reductions ≤ visits`.

## Retrieval and search

`RetrievalQuery.type_family` carries `TypeFamilyQueryView`; it cannot coexist with
the full `normalized` view. The pure index retains exactly the same allowed scope
and scorer. The alternate is interleaved raw-first only when both result heads
are known and equal, arities agree, and features/tokens differ. Otherwise one raw
pass is used. Classification, in precedence order, is `kernel-rejected` or
`output-limited` for unavailable evidence, then `unknown-head`, `changed-head`,
`changed-arity`, `identical`, or `stable-head-and-arity`. These are scheduling
observations, never proofs of irrelevance or impossibility.

Result v6 uses `raw-stable-type-family-query-interleave-v1/<single-view-policy>`.
It includes `type_family_query_policy`, `type_family_classification`, and
`query_views_scored`. Item view is `raw` or `type-family`, with its own one-based
view rank and unchanged score components. Bounded orders are prefix-stable;
candidate/view and posting counts account for actual scoring passes. The old
raw and full-normalization serialized identities remain unchanged when this
option is absent.

Scoped decision v8 records the classification, query evidence, work and item
provenance. The existing OR/NNUE interface receives
`retrieval-type-family-classification` alongside view/rank metadata. Progressive
admission and proof checking retain their separate authorities. Aggregate counters
`scoped_retrieval_type_family_queries`, `scoped_retrieval_type_family_term_visits`
and `scoped_retrieval_type_family_reductions` survive trace omission/nested merges
and are absent at zero. Existing extra-candidate-view counters still apply.

This is an optional ranking policy, not a default promotion or a claim of
representative recall. Qualification must include unchanged-denominator recall
and end-to-end fixed-total-cost tests, not just short-query timing. Fresh Agda
validation remains mandatory for a verified proof.
