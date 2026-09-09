# Nameable live premise scope

This internal Agda 2.8.0 capability supports the optional scoped retriever.
It does not enable that retriever by default or alter proof validation.
The native adapter and Python gateway must be upgraded together.

## Requests and response versions

`agdaprover:scoped-retrieval:v4:` followed by a JSON exclusion array requests
`agdaprover.live-scope.v4`. With permitted dependency evidence enabled, the
marker is `agdaprover:scoped-retrieval:v5:` and the response is
`agdaprover.live-scope.v5`. Capability identities include the matching version
and exact adapter hash. Older responses fail closed; they are not silently
treated as having checked nameability.

The closed response contains:

- `kind: AgdaProverScope`, the schema version and requested `interaction_id`;
- `excluded_names`, exactly the sorted requested exclusions;
- `feature_policy: agda-term-body-head-symbol-arity-v1` and
  `type_view_policy: agda-normalise-contextual-type-v1`;
- `target: {result_head, symbols, arity}`;
- `declarations`, rows `{id, aliases, type, features}` with exact native IDs,
  sorted unique aliases, contextual normalized type views and original
  structural type features;
- `structure_nodes`, the nonnegative visited term-body count; and
- `omitted_aliases: {ambiguous, unnameable}`, two sorted unique string arrays.

The dependency version additionally contains
`dependency_policy: permitted-clause-rhs-references-v1`, `dependency_nodes`
(included in `structure_nodes`) and per-declaration `rhs_dependencies`.
Those dependencies are sorted unique allowed IDs or null for unavailable
concrete evidence. No excluded endpoint or intermediary can occur.

## Membership before features

The native observer enters the requested interaction-meta closure. It uses
Agda's concrete-name structure to withhold aliases containing an anonymous
`IsNoName` component before resolution. Anonymous declarations' distinct native
IDs do not make `_` a usable spelling. Ordinary mixfix names and independently
exposed named members of anonymous modules remain eligible.

Agda's non-throwing name resolver classifies unresolved ambiguous spellings.
They are omitted without discarding independently resolved qualified aliases.
Supported constructor and projection overload sets remain available; the
retriever never chooses an ambiguous ordinary function by arbitrary order.

Only resolved members can grant scope. Excluding a resolved alias or its final
component excludes that declaration identity under all aliases. Types and
permitted dependencies are queried only after this allowed set is fixed.
Missing members cannot re-enter through a dependency or omission record.

Omission arrays are diagnostics, disjoint from each other and all returned
usable aliases. Malformed, empty, duplicate, unordered, NUL-containing or
overlapping rows are rejected before hashing. They do not contribute query
tokens, scores, structural features or action permissions. The full response
still participates in exact scope identity and replay provenance.

## Authority and cost

The query retains exact-state checks, `localStateCommandM`/`dontAssignMetas`
isolation, physical request charging, timeout/cancellation and process cleanup.
It cannot assign metas, accept a proof or broaden module assumptions. Proposed
applications need kernel elaboration; complete results need fresh
policy-compliant validation.

The current native request retains its existing defensive capacities (5,000
scope aliases/declarations, 250,000 traversed term nodes, 65,536 characters per
type view/exclusion payload, 16 MiB output). They are observer-capacity limits,
not claims about theorem validity; their resource-policy migration is separate.
The Python omission traversal polls the caller's shared resource envelope and
adds no independent shape ceiling. This revision does not change ranking,
progressive admission, model weights, training or the public-protocol path.
