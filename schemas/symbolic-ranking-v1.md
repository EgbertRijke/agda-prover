# Haskell symbolic ranking contract

Scope: optional typed Haskell core, not a new model format or a new default
search engine. Agda remains the sole proof authority.

## Model and feature compatibility

`NNUE.Model` accepts APNNUE1, APNNUE2 and APNNUE3 artifacts with their existing
little-endian float32 layouts. Role/feature-schema/family, canonical v3 policy
domain, dimensions, payload length and finite parameters are checked before
inference. SHA-256 covers the complete artifact. V1 can recover a missing role
from its adjacent `.json` training manifest; the manifest is never executable.
Artifact/header allocation limits remain 16 MiB/64 KiB. The legacy sidecar is
also bounded to 64 KiB. Dimension and seed fields must be JSON integers; the
Haskell reader does not emulate Python's accidental coercion of strings,
booleans or fractional dimension values. Standard saved models are unchanged.

`NNUE.Features` preserves the current `agdaprover.features.p0.v2` token contracts
for proof terms, one-step refinements, focused branches and OR decisions. Model
families are respectively `proof-term-v2`, `one-step-refinement-v2`,
`focused-branch-v2` and `or-decision-v4`. OR domains retain v1/v2 legacy-family
fallback; v3 declares its supported domain, including `evidence-application-v1`.
No type or theorem name is assigned special semantics.

Compatibility text is an explicit view. Agda types and expressions retain
their native structure independently; the feature summary is not a parser for
semantic candidate generation, a type equality test or a proof-state key.
Unknown structural facts remain distinct from false. Ordered metadata is
preserved verbatim. Sparse hashing retains first insertion order and zero
collisions, using BLAKE2b-64 personalized with `AgdaProverP0`.

## Numeric ownership and native scoring

Accumulators carry an immutable artifact identity; a changed artifact cannot
reuse them. Sparse features check dimension, index range and finite values.
Incremental updates remove old features before adding new ones. Exact-token
LRU caching is purely numerical; eviction loses no search alternative. Cache
capacity is a caller resource choice, not a proof-depth bound.

The Haskell reference evaluates in double precision over loaded float32 values.
Rust ABI3 receives validated float32 buffers and sorted CSR action entries, as
the existing Python binding does. Numerical parity is tested with float32
tolerance; bit-identical ordering across different arithmetic backends is not
promised for nearly tied scores. Exact ties preserve symbolic order. A batch
native error, float32 range failure, absent library or opt-out uses the entire
reference batch. No partially scored candidate set is returned.

Native handles are lifetime-owned and locked through calls and unload. A
retained IO callback after close returns `native-scorer-closed`, not a dangling
pointer access. Async cancellation is not caught as a successful model result.
Trusted custom native libraries have ordinary executable-code privileges;
models and proof inputs cannot specify executable paths.

## Decisions and proof credit

`rankBatch` takes a typed ranking domain, unique structural candidate IDs,
nonnegative structural tiers in symbolic order, and feature views. It only
reorders complete batches. Empty/singleton batches do not invoke a model.
Explicit symbolic mode, absent role weights, unsupported domains and failed
feature/scoring preparation preserve exact symbolic order. Invalid IDs or tiers
are precise caller errors, not candidate pruning.
Presentation strings need not be unique; overloaded names do not identify the
underlying typed candidates. Their distinct IDs remain present in both orders.

`agdaprover.symbolic-policy-decision.v1` records:

- `decision_id`, `role`, `family`, `model_id`, `model_seed`, `feature_family`;
- `symbolic_order`, `model_order`, `priority_tiers`, `scores_in_symbolic_order`;
- `fallback_reason`, `backend`, `native_fallback`;
- `model_items_scored`, `model_elapsed_ns`, `scoring_elapsed_ns`;
- `validated_proof: false`.

Elapsed model work includes feature/accumulator preparation, scoring and fallback;
the separate scoring counter isolates inference. Deterministic/disabled decisions
report no scoring. Interrupted operations require the enclosing session's
dispatch and sampled-cost accounting; they do not fabricate final zero work.

The Haskell ranker has no proof-credit operation. Search must carry exact
selected decision/candidate identities through branches, reconstruction and
application handoff. Only after independent fresh Agda validation may the
application attach the existing `agdaprover.validated-policy-proof.v1` receipt,
binding task, source, patch, validation and trust-report identities. Accepted
speculative steps, principal-variation previews, abandoned branches and
resource exhaustion are not successful training labels. The H4/H8 integration
must preserve this existing application-side boundary.
