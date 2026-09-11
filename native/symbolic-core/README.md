# Haskell symbolic core

This is the experimental native observation and checking boundary for the typed symbolic
engine migration. It does **not** replace AgdaProver's current search engine.
There is no search operation or default-engine switch yet.

## Build and inspect

From the AgdaProver checkout:

```sh
scripts/build-symbolic-core
scripts/build-symbolic-core --print-path
```

The build requires GHC 9.6.7 and installed Agda 2.8.0/aeson 2.2.4.1 packages,
plus `blake2-0.3.0.1` and `cryptohash-sha256-0.11.102.1` for compatible feature
and artifact hashes. Provision these exact packages before the offline build.
`AGDAPROVER_AGDA_PACKAGE_DB` overrides the package database location. Builds are
offline and refuse to silently rebuild Agda. Build output stays in the ignored
`dist-newstyle` directory. No development repository or corpus is needed.

The resulting executable accepts:

```text
agdaprover-symbolic capabilities
agdaprover-symbolic observe ABSOLUTE-FILE GOAL MODE [ABSOLUTE-INCLUDE ...]
agdaprover-symbolic session ABSOLUTE-FILE [ABSOLUTE-INCLUDE ...]
```

Use a prepared project copy and ordinary process supervision for observations.
Modes are `raw`, `instantiated`, `head-normal`, `simplified`, and `normalized`.
Agda checks the source under its declared options. No library registry is
discovered implicitly; imports use explicit include roots and Agda's primitives.
Agda may generate normal import interfaces in that copy.

For `observe`, stdout is one JSON response; progress and diagnostics go to stderr. A checking or
unsupported-observation failure has a nonzero exit status. An observation is
never a verified proof and never edits goal bodies.

## Resident checking

`session` loads once and reads newline-delimited JSON requests. It supports
observations, speculative `give`, retained branches, eviction/replay, cost
snapshots, cancellation, and close. It does not choose candidates or solve goals
autonomously. See [the session protocol](../../schemas/symbolic-session-v1.md)
for fields, events, resource supervision, and failure semantics.

All requests address a session/epoch/branch key. A successful check returns a
different child key and keeps its parent unchanged. Hidden metas and remaining
constraints are not mistaken for completion. Even `apparently-closed` is only
provisional checking evidence, not an independently verified proof.

Source and loaded-import changes invalidate the epoch. Use immutable prepared
project copies for runs. The initial implementation conservatively rechecks
exact source bytes around each native operation; it claims no whole-search
speedup yet. Cancellation restores the parent without resetting work counters.
An evicted branch can be replayed, but replay issues new keys rather than
silently changing the meaning of old checked evidence.

## Boundaries

- `core/`: compiler-independent protocol, feature views and NNUE inference; no Agda internals.
- `adapter/`: Agda 2.8 types, scoped snapshots, and structural codecs.
- `app/`: process entrypoint and response/error framing.

Terms remain Agda's typed Haskell syntax inside the adapter. Their JSON trees
are observations, not a second typechecker or authority for proof acceptance.
The codec preserves eliminations, binders, annotations, levels, and known metas.
It rejects unknown atom references and unbound indices during reconstruction.
Dummy nodes and reflection meta literals currently produce explicit unsupported
observations. Names and metas are session-local, not reusable external handles.

The context telescope stays raw, independently of the requested target view.
Scope aliases are resolved by Agda, with ambiguous/unknown names retained as
such. Full native scopes and local let bindings remain in the scoped snapshot.
Structural round trips are not conversion proofs or fresh validation.

The codec is shared with development tools through an annotation-view provider.
Older development snapshots retain their presentation format; the runtime view
also preserves domain-name provenance. No training, benchmark, or library-specific
dispatch code belongs here.

## Existing NNUE compatibility

The Haskell library reads the existing APNNUE v1/v2/v3 models, retaining artifact
SHA-256, role restrictions and scoped decision families. No weights are changed
or trained. Custom model paths work offline. The feature layer preserves the
current tokens and personalized BLAKE2 hash, including tri-state structural
classification. Presentation features never authorize semantic operations.

Immutable model-bound accumulators support full and incremental updates, with
an exact-token LRU cache. The reference scorer uses double-precision arithmetic
over float32 model weights. An optional, application-supplied native library
path uses AgdaProver's existing Rust ABI3 and float32 batches. Unsupported ABI,
missing library, explicit `AGDAPROVER_DISABLE_NATIVE=1`, or failed native scoring
retains the reference path. The library remains loaded through borrowed calls;
stale scorer handles fail safely.

The policy router accepts complete symbolic candidate batches. It preserves
structural priority tiers and stable tie order; symbolic opt-out, unsupported
families and feature/scoring failures never remove candidates. Decision records
include ordering, weights, backend, fallbacks and elapsed work, but cannot grant
proof credit. Only the application's independent fresh validation may do that.
See [the ranking contract](../../schemas/symbolic-ranking-v1.md).

Action generation, integration with autonomous search, and engine selection
are subsequent migration tasks. Current production search and model bytes
remain unchanged until those tasks are qualified.
