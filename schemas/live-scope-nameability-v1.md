# Nameable live premise scope

This internal Agda 2.8.0 capability supports the optional scoped retriever.
It does not enable that retriever by default or alter proof validation.
The native adapter and Python gateway must be upgraded together.

## Requests and response versions

`agdaprover:scoped-retrieval:v6:` followed by the closed JSON object
`{excluded_names, output_bytes}` requests `agdaprover.live-scope.v6`. With
permitted dependency evidence enabled, the marker uses `v7` and the response
is `agdaprover.live-scope.v7`. Exclusions are sorted unique nonempty strings
without NUL; `output_bytes` is the caller's positive integer byte reservation.
There is no independent exclusion-count or string-length ceiling.
Capability identities include the matching version and exact adapter hash.
Older responses fail closed; adapters and gateways must be rebuilt together.

The closed response contains:

- `kind: AgdaProverScope`, the schema version and requested `interaction_id`;
- `excluded_names`, exactly the sorted requested exclusions;
- `output_bytes`, exactly the requested reservation;
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

Native scope cardinality, feature-node visits and rendered type lengths no
longer have separate fixed ceilings. Feature extraction strictly consumes
Agda's term-body traversal without retaining a second complete term list;
normalization and pretty-printing remain Agda operations. This is not a claim
that all kernel traversals are stack-safe or that observations have unlimited
capacity. The process supervisor checks the caller's CPU, memory, wall and
I/O envelope, including during silent normalization and rendering. The Python
consumer polls the shared envelope and checks complete scope integrity.

The complete JSON response must fit `output_bytes`. Before publication, the
native observer checks both the accumulated encoded-row lower bound and the
final UTF-8 byte count. Exceeding it emits only the closed resource refusal:

```json
{
  "kind": "AgdaProverScopeResource",
  "schema_version": "agdaprover.live-scope-resource.v1",
  "request_schema": "agdaprover.live-scope.v6",
  "interaction_id": 0,
  "resource": "output-bytes",
  "limit": 1024,
  "observed_lower_bound": 1100
}
```

The gateway requires exactly one scope or refusal, verifies the request schema,
interaction and limit, and requires an integer lower bound strictly above the
limit. A valid refusal becomes `resource-exhausted`, never Agda rejection,
`invalid-task`, a truncated scope or negative proof evidence. Unknown versions,
extra fields and mismatched refusals remain protocol errors. Native rollback
also applies to refusals. The surrounding transport independently bounds the
entire command and response, including framing and errors; a tiny allowance
may be exhausted before a refusal can be returned. Retrying cannot reset the
controller's aggregate ledger. No automatic retry or budget enlargement is
introduced here.

The reservation and wire version bind exact observation identity, while
feature policies, ranking, progressive admission, weights and the default
public-protocol path are unchanged. The capability remains explicitly opt-in.
