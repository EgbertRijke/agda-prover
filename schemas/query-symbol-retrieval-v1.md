# Query-symbol retrieval lane v1

This optional ranking policy operates only on an immutable `AllowedPremiseSet`.
It cannot add aliases, discharge a goal or authorize a recursive call.

`RetrievalQuery.query_symbol_lane` is a strict Boolean, defaulting to `false`.
When false, existing query identities, ranking order and result serialization
remain unchanged. When true, the query identity binds the distinct
`head-symbol-arity-lexical-query-symbol-interleave-v1` policy. With allowed
dependency evidence the combined policy is
`head-dependency-symbol-arity-lexical-query-symbol-interleave-v1`.

Two ordered lanes are merged before the requested limit is applied:

1. All allowed declarations in the existing symbolic ranking order.
2. Allowed declarations whose exact declaration ID occurs in the query's
   structural `symbols`, in that same ranking order.

The merge alternates starting with lane 1, skips already emitted declaration
IDs, and continues the other lane when one is exhausted. It is deterministic
and prefix-stable across limits. Aliases are not independent candidates.
Neither unmatched heads nor declarations outside lane 2 are excluded. A query
with no allowed symbol references reproduces the original ordering.

No name substring, private reference body, usage label, normalization request
or additional dependency edge is used. Hidden constants may already occur in
the authorized goal's structural features; they do not become premises unless
they are independently present in the allowed set.

Results with the lane enabled use `agdaprover.symbolic-retrieval.v3`. Existing
fields and optional dependency counters are preserved; every item's components
also include `query_symbol_match` (0 or 1). The result's query ID and policy bind
the lane. The index ID still binds the same immutable scope/features/dependency
evidence. Candidate counts count unique allowed declarations, not lane entries.
There are no extra kernel/model requests. Traversals poll the caller's physical
resource envelope; interruptions do not publish partial results.

The live constructor controller enables the policy only with
`AGDAPROVER_SCOPED_QUERY_SYMBOL_LANE=1`; it still requires a live scoped feed.
The option is captured when the controller starts and does not change a pinned
query during search. Scoped decision v5 records the ranking policy and the
query-symbol component, alongside optional incremental-build work. OR metadata
adds `retrieval-ranking-policy` and `retrieval-query-symbol-match`; these are
ranking hints, never assertions of applicability. Existing admission and
progressive-search policies retain their separate identities.

The development worker index and private recall evaluator accept the explicit
keyword-only `query_symbol_lane: bool = False`. The evaluator must reproduce
the independently requested policy from worker-only evidence before examining
labels; it must not adopt the policy of the supplied result automatically.
A supplied result with altered items, policy
or query identity is rejected. This policy is not a default promotion or a
claim of calibrated C3 recall or fixed-budget downstream improvement.

The separate [symbol-rarity extension](symbol-rarity-retrieval-v1.md) adds an
optional third lane. It uses its own query/result policy and schema; leaving
that extension disabled preserves this two-lane contract unchanged.
