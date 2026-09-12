# Haskell symbolic core

This is the experimental typed Haskell core. It supports resident checking and
autonomous evidence/application and structural-construction fragments, including
the bundled NNUE.
It does **not** replace AgdaProver's current search engine. A default-engine
switch requires the remaining clause, recursion, joint-search and qualification work.

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
agdaprover-symbolic session ABSOLUTE-FILE [ABSOLUTE-INCLUDE ...] [-- CHECKING-OPTIONS ...]
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
snapshots, cancellation, and close. `solve-evidence` additionally chooses typed
applications and lambdas inside that resident checker. See [the session protocol](../../schemas/symbolic-session-v1.md)
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

## Evidence search

The first native fragment handles exact local/global evidence, lambda
introduction, partial applications, hidden/instance inference, dependent
arguments and function-valued record projections. All semantic terms retain
Agda abstract/internal structure. NNUE presentation features do not decide
typing or scope. A failed later argument can revisit earlier argument choices
with the full checker state restored.

The structural extension adds scoped datatype constructors, dependent record
literals (including records without a named constructor), and absurd elimination.
Field types come from Agda's instantiated telescope; later fields can infer
omitted hidden/instance fields or cause earlier choices to be retried. Agda
checks constructor indices and emptiness, including impossible indexed domains.
The native draft retains generated helpers; replay never depends on a temporary
checker-generated helper name. At source handoff, Agda's relative expression
layout is anchored at the hole, including multiline typed lets.

Use `ProverApplication.prove_evidence(task, engine=NativeEvidenceEngine(path))`
from `agdaprover.application.service` and `agdaprover.application.evidence` to
exercise the explicit application path. `path` is the built executable, not a
source directory. It uses the bundled OR model unless `task.ranker` is
`symbolic`; `policy_model` and `native_scorer` select user-supplied inference
assets. No model bytes or training policy change in this milestone.

The application prepares an immutable project overlay, supervises its worker,
reconstructs the candidate and freshly validates it with ordinary Agda before
reporting `verified`. This slice accepts standalone projects and explicit
source imports; `.agda-lib` manifest routing awaits H8 and is explicitly
rejected here, never silently ignored. Existing production library support is
unchanged. Clause splitting, induction, joint solving and editor migration remain
later milestones, not implied by `search_available`.

`work_units` optionally limits native inference/checking queries. Its default
`None` widens search depth under the caller's physical resource envelope and
cancellation, without a fixed proof-depth or 20-second cutoff. The current
implementation is a first functional slice, not a performance claim: repeated
scope preparation and iterative deepening can be expensive. Broader agenda and
reuse work follows in H7. Exhaustion and failure to find evidence are not
impossibility certificates. Full benchmarks run at H10, not after every edit.
