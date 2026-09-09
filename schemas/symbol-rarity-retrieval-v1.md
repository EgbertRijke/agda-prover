# Symbol-rarity retrieval lane v1

This opt-in extension to [query-symbol retrieval](query-symbol-retrieval-v1.md)
adds a third ranking lane. It receives only the immutable authorized scope and
query; neither hidden declarations nor private proof labels supply statistics.
It is a similarity hint, not a unification test or proof authority.

`RetrievalQuery.symbol_rarity_lane` is a strict Boolean, false by default.
Enabling it requires `query_symbol_lane=true`; other combinations are rejected.
With it disabled, existing identities, serialization and ordering are unchanged.
The new policy is `head-symbol-arity-lexical-query-symbol-rarity-interleave-v1`,
or `head-dependency-symbol-arity-lexical-query-symbol-rarity-interleave-v1` when
allowed dependency evidence is supplied. Query/result identities bind the
policy. Index and scope identities are unchanged.

For N allowed declarations, let df(s) count declarations whose structural
symbol set contains s. Let L be a declaration's number of distinct symbols,
and A be the mean L over the allowed scope, floored at 1. Its score is:

```text
idf(s) = log1p((N - df(s) + 0.5) / (df(s) + 0.5))
symbol_rarity = sum(idf(s) for shared query/type symbols)
                * 2.2 / (1 + 1.2 * (0.25 + 0.75 * L / A))
```

Symbols are exact structural identities, each counted once per type; shared
weights are summed in sorted symbol order. Empty overlap scores zero. The
third lane sorts by descending score, then the existing symbolic tie-breaker.
It is round-robin merged with the baseline and direct-query-symbol lanes,
starting with the baseline and skipping duplicate declaration IDs. Exhausted
lanes are drained; the result is deterministic and prefix-stable. No candidate
is excluded by a low score. Each lane needs only its first requested k entries.

Results use `agdaprover.symbolic-retrieval.v4`, adding finite, nonnegative
`symbol_rarity` to each item's components. Existing counters retain their
meaning: unique candidates and actual posting visits, not lane entries.
There are no extra kernel/model requests. Ranking traversals poll the caller's
physical envelope. Interrupted work publishes no partial result or mutation.

The controller captures `AGDAPROVER_SCOPED_SYMBOL_RARITY_LANE=1` at startup,
enabling both this and the query-symbol lane; a live scoped feed is still
required. Decision v6 records the policy and raw scores, retaining optional
dependency and incremental work. Existing OR/NNUE metadata carries
`retrieval-symbol-rarity-band` with values `0`, `0-1`, `1-2`, `2-4`, `4-8`,
`8-16`, `16-32`, or `32+` (upper bounds inclusive). Binning avoids a vocabulary
of individual floating-point scores. No trained model or admission rule changes.

The development worker/evaluator must explicitly request both Boolean options.
The evaluator reproduces the worker-only ranking before inspecting labels;
the supplied result cannot choose its own policy or statistics. This option
is not a default promotion or a claim that retrieval quality gates are met.
