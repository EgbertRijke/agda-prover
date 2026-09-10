# Optional contextual result-spine features

Use `AGDAPROVER_SCOPED_RETRIEVAL=1` and
`AGDAPROVER_SCOPED_TYPE_SPINE_HEADS=1` with the explicitly configured Agda 2.8
embedded adapter. The option is captured at project open and is mutually
exclusive with `AGDAPROVER_SCOPED_QUERY_VIEWS=1` and
`AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY=1`. It is off by default and never enables
the embedded adapter implicitly.

This policy improves structural matching through reducible type aliases for
both goals and premises. It weak-head reduces the result Pi spine under its
original binders. Result heads and arities come from this checked view; symbols
and lexical tokens retain the original contextual type's vocabulary. It does
not recursively normalize domains or neutral value arguments, bypass abstraction,
change scope membership, or confer action/proof authority.

## Bridge contract

The request marker and response schema use `agdaprover:scoped-retrieval:v12:`
and `agdaprover.live-scope.v12`, respectively; use v13 with dependency evidence.
The closed request retains exclusions and the caller's output reservation. The
response has feature policy `agda-result-spine-head-raw-symbols-v1`. Each existing
target/declaration feature row has the projected head/arity and original symbols.
The root and every declaration additionally carry exactly:

```json
{
  "type_spine": {
    "status": "checked",
    "head_reductions": 2,
    "conversion_checked": true,
    "raw_result_head": "global:1:2",
    "raw_arity": 1
  }
}
```

`checked` requires one head reduction per resulting Pi plus one for the result.
`kernel-rejected` requires false conversion and unchanged raw head/arity, with
the actual attempted reduction count. All counts are nonnegative integers,
not Booleans. Kernel type rejection rolls back and retains that entry's raw
features. Native process/IO/resource errors and asynchronous cancellation retain
their ordinary failure semantics. Both successful and rejected attempts restore
the local Agda state, cannot assign or create metas, and cannot leave constraints.
Fresh Agda validation is still mandatory for a verified proof.

Exclusions precede feature queries. The complete scope, observation, state,
adapter and feature policy bind index identity. `structure_nodes` includes the
raw feature traversal and attempted head reductions; it is not reduction fuel.
An output overflow emits the version-bound resource refusal, never a truncated
scope. There is no hidden retry or enlarged resource allowance.

## Search, diagnostics and ranking

`ScopedPremises.type_spine_work` retains total queries, head reductions and
per-entry rejections. Scoped decision v9 records this work and the feature policy.
Aggregate `scoped_retrieval_type_spine_queries`, `_reductions`, and `_rejected`
survive nested merges and trace omission; zero fields remain absent. The existing
OR/NNUE boundary receives `retrieval-feature-policy`, along with head-match and
other score features. No model, score weights or pure retrieval format changes.
This is a single feature/scoring view, not an extra normalized-query lane.

The constructor-search statistics hook reports once on every exit, including
exceptions. Its controller consumers only aggregate in-memory counters, before
any later budget checkpoint can fail. Single-goal, joint and case search thus
retain completed work on interruption without suppressing the exception,
continuing search, or redefining physical verifier counts.

Qualification must compare unchanged-scope recall and complete fixed-budget
search against the default, including protected regressions. The option itself
does not claim representative recall or justify default promotion.
