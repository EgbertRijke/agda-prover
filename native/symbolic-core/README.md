# Haskell symbolic core

This is the experimental typed Haskell core. It supports resident checking and
autonomous evidence/application, focused logic, structural-construction and recursive-call fragments, including
the bundled NNUE.
It does **not** replace AgdaProver's default search engine. Single-goal,
joint-prefix, one-step and interactive workflows are connected, but the native
engine has not passed the required joint benchmarks. Keep Python as the default.

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

For relocatable executables, build the linked Agda library **and** the separate
Agda checker with `+use-xdg-data-home`. Agda's default build can retain an
absolute Cabal data-directory dependency even when the executable has no
non-system dynamic libraries. The XDG build uses Agda's embedded runtime data
in the application's private data directory. See [build and relocation](BUILDING.md).

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

Resident sessions additionally accept `--library-file=ABSOLUTE-REGISTRY` and
repeated `--pin-config=ABSOLUTE-FILE` arguments before the checking-options
separator. Supply the registry and every prepared project manifest as pins.
The application does this automatically through the existing overlay boundary.
Default-library discovery stays disabled, and Agda's own manifest parser and
runtime-directory lookup remain authoritative. Configuration bytes are pinned
before loading and checked at every resident request.

For `observe`, stdout is one JSON response; progress and diagnostics go to stderr. A checking or
unsupported-observation failure has a nonzero exit status. An observation is
never a verified proof and never edits goal bodies.

## Resident checking

`session` loads once and reads newline-delimited JSON requests. It supports
observations, speculative `give`, native `make-clause` proposals and checked
`apply-clause` transitions, retained branches,
read-only `infer-helper` signatures,
eviction/replay, cost snapshots, cancellation, and close. `solve-evidence` additionally chooses typed
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
Only the final replay handle is published. Internal intermediate checkpoints
release their resident checking state while preserving the replay recipe;
existing caller-owned snapshots still require explicit eviction.

`make-clause` delegates ordered variable batches, hidden/instance binder exposure,
result splitting and ellipsis expansion to Agda. It retains native clauses and
generation state internally, rendering with Agda's own interaction printer.
Generation is not acceptance: no source is edited, no child is issued, and no
proof is claimed.

`apply-clause` executes an admissible action through a checked local dependent
helper. Agda generates the helper's native clauses and checks the final draft;
new goals retain their dependent types and can be split or filled in subsequent
branches. The original global definitions and parent remain intact. Rejections,
cancellation and replay preserve the same transaction/cost rules as `give`.
Displayed evidence can require exposing hidden parent binders before insertion;
the source-export/application path below performs that operation. Direct
session results never substitute for independently checked source export.

`reconstruct-goal` assembles retained native drafts for an original goal along
one descendant branch. It preserves binders, helper declarations and clause
structure, then rechecks the expression from the original parent. Accepted text
inputs are scoped once and retained as native drafts for replay. Partial drafts
remain partial, and the returned evidence is not fresh verification. Source
patching and hidden-binder exposure belong to the separate export operation.

`reconstruct-goals` rechecks an ordered batch in one new branch. Later entries
can depend on earlier reconstructed definitions; unselected goals stay open.
`export-goals` adds a native source presentation to each checked entry. Hidden
clause binders referenced by the proof are exposed by Agda and mapped by native
binding identity. Relative helper layout is retained. The application anchors
the resulting expression or whole-clause edit and validates it freshly. The
supported formats are `.agda` and `.lagda.md`. See the source-presentation contract in
the session schema.
The batch returns each entry's checked evidence and the final pending state.
A failed batch publishes no intermediate states, while preserving its spent
work. Whole-source fresh validation is still required.

`infer-helper` uses Agda's helper-function inference directly, including
abstraction over compound arguments and the five observation modes. It retains
the native signature in a parent-branded snapshot and returns Agda's rendering
for inspection. It neither installs a helper nor claims a proof.

`solve-helper` additionally searches the finite one-constructor/available-value
helper fragment for a supplied application. Clauses come from Agda, candidates
use the existing NNUE and checked-transition boundary, and complete results
still require independent fresh validation. The autonomous agenda also uses
Agda-generated local helpers for structural elimination; general arbitrary
helper-application invention is not implemented.

## Boundaries

The pure agenda schedules opaque coupled states and typed actions. Stable
cost-ordered alternatives survive failed descendants and provisional candidate
rejection. A censored step retains its queue; resumable work advances scheduling
cost so it cannot permanently starve finite-cost siblings. Ancestry pruning
requires an exact adapter witness, not a display or hash match.

The native agenda executor connects resident evidence, clause and finite-helper
moves to that queue. A move must belong to its actual parent; accepted moves
carry all dependent pending goals, metas and constraints together. Exhausted
coarse evidence attempts retain the queue as censored work, not refuted branches.
Retrying such an attempt repeats and charges its work; fine-grained inner
suspension is still pending. Planners supply moves through the typed adapter
API. Source export is connected; whole-benchmark qualification remains open.
Neither layer confers proof acceptance.

`proposeTerms`/`applyTerm` provide native one-move evidence, application prefixes,
lambdas and record literals through the Haskell session API. Application arity
comes from Agda's telescope and is not capped at ten arguments. Explicit operand
holes and inferred hidden parameters remain coupled in the checked child;
partial applications retain their structure. Catalogue censorship is a distinct
typed result, not an empty completed search. Existing NNUE head ranking and
shared structural ordering apply.

`AgendaSearch` provides an autonomous Haskell controller over these primitive
term moves, native case proposals and clause-generated local helpers. Datatype
and inductive-record subjects come from Agda's context/metadata; shared NNUE
ranking orders eligible choices. Case analysis may generalize captured module
or lambda variables into checked local helpers, while Agda still enforces
coverage, modalities and without-K. Hidden-binder exposure retains Agda's
original source-clause operation.

Scheduling slices keep the queue and alternatives after provisional solutions.
Coarse evidence search runs in soft, increasing work slices and yields to other
branches; retries are charged, not treated as free continuation inside Agda.
Increasing a run's work allowance does not reset accumulated work. Typed
catalogue censorship pauses the run rather than discarding unexplored moves.
The Haskell API exposes generic agenda events and cost snapshots. Autonomous
helper-application invention is not implied. The application routes public
operations to this controller and supervises shared physical resource limits.

The resident protocol exposes `start-search`, `advance-search`, `search-cost`
and `discard-search`. An advance uses a configurable scheduling quantum and
returns a revised run handle; it retains alternatives after provisional
candidates. Allowances can be increased without erasing spent work. Existing
`cancel` interrupts the active request while preserving a resumable/discardable
run. Versioned progress events use the current request ID. The caller still
supervises process resources and freshly validates reconstructed source.
See the session schema for exact fields and revision/cancellation semantics.

`start-search` optionally selects pending `goal_ids`. Generated dependent
subgoals inherit that selection; unselected original goals stay in the same
coupled state without being scheduled. Candidate replies report both the
selection and all remaining obligations. Selected candidates need source
reconstruction and independent validation, not a whole-file closure claim.

The Python bridge exposes a supervised resident connection for these coarse
requests. One prepared overlay, process and resource/output envelope cover all
slices; resuming does not reset them. The existing single evidence operation
uses this same transport. Symbolic choices remain native, and user-facing
engine selection and interactive controls use the shared application API.
Native search remains opt-in pending full benchmark qualification.

An optional `depth_limit` counts accepted branch transitions. Blocked items are
parked, not discarded; `advance-search` can increase or remove the limit on the
same retained run. Depth is not a measure of expression size or checker work
inside a compound move. Those costs remain supervised and fully charged.

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

The focused path builds ordinary nondependent implication proofs entirely in
memory from native type identities. It reuses positive subproofs, detects cycles,
retains alternative inhabitants and handles observed empty datatypes. Only
completed candidates are checked by Agda. Dependent, hidden and unsupported
types retain the general native path; a failed fast path never proves impossibility.
Its separately role-checked NNUE uses the unchanged focused weights.

The algebraic path recognizes supplied commutativity/associativity and relation
operations from native telescopes and application spines. It constructs explicit
rewrite proofs, including symmetry, composition, binary congruence and shared
outer application contexts. It works with an arbitrary supplied relation, not
only identity, and preserves distinct evidence with the same endpoints. All
operations must be available in scope; no names or notation grant algebraic laws.
Agda checks every candidate and failed continuations retain other evidence.
The existing widening depth and cumulative work allowance bound exploration;
there is no separate fixed term/node ceiling or unbounded normalizer. This is
the current binary AC fragment, not general algebraic decision-procedure coverage.

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

Recursive calls use the enclosing source definition and Agda's checked clause
patterns. The current mutual group is never ordinary evidence. Dedicated calls
can use direct descendants, function-valued children and reconstructed wrappers;
Agda infers unchanged and hidden parameters from the expected result. Unknown
descent through with-abstraction retains a typed fallback, not a termination
claim. Generated helper goals retain their source owner across branch replay.
New helpers join that owner's mutual group before Agda checks termination, so
cycles spanning a helper and the source function cannot evade the check.

Expected-result applications are tried before unconstrained operand enumeration.
Agda relates their inferred result to the goal before arguments are searched,
preserving dependencies even when constructor elaboration creates fresh hidden
parameters. Other application alternatives remain available. A recursive winner
must pass a non-forced assignment and owner-group termination check inside search;
rejection resumes alternatives. The final draft is checked again from its parent
and still requires independent fresh validation.

The `copattern-evidence-v1` fragment also handles finite coinductive observations
and fills Agda-generated coinductive projection clauses. Native checked patterns
and their record metadata admit dedicated owner-call proposals; they do not
assert productivity. The same owner-group check rejects unguarded cycles.
Dependent and function-valued fields retain ordinary typed application and
lambda search. Neither inductive case splitting nor eta is assumed for a
coinductive value. `copattern_proposals` is a subset of `recursive_proposals`.
This composes the existing `apply-clause` and `solve-evidence` operations;
autonomous clause selection and full interactive source export remain pending.

Structural scheduling and NNUE share model-independent tri-state facts. The
adapter obtains constructor availability, result-head matches and descent
information from native Agda data. Unknown is not false; pending dependency and
relational classifications remain unknown. These facts reorder construction
and application continuations without dropping either. Evidence-policy traces
include the same classification supplied to the unchanged feature encoder.

Primitive application proposals retain Agda's inferred telescope and compare
only rigid result shapes: functions, universes, and actual datatype/record
identities. A stuck family, variable or meta remains unknown and never warrants
discarding an application. Hidden arguments and dependent indices are still
inferred by Agda when the proposal is checked. This avoids queuing provably
unrelated heads without replacing conversion with textual type comparisons.

The agenda's optional `progress_ordering` uses spent cost plus sixteen units
per remaining selected interaction. This soft estimate lets a completed prefix
advance while retaining every alternative; it is neither a proof-cost lower
bound nor a discount against resource accounting. Receipts identify
`cost-plus-obligations-v2`; disabling it retains `cost-only-v1`. One-step ordering
is unchanged. See the [session contract](../../schemas/symbolic-session-v1.md).

Use `ProverApplication.prove_evidence(task, engine=NativeEvidenceEngine(path))`
from `agdaprover.application.service` and `agdaprover.application.evidence` to
exercise the explicit application path. `path` is the built executable, not a
source directory. It uses the bundled OR and focused models unless `task.ranker` is
`symbolic`; `policy_model` and `native_scorer` select user-supplied inference
assets. No model bytes or training policy change in this milestone.

The application prepares an immutable project overlay, supervises its worker,
reconstructs the candidate and freshly validates it with ordinary Agda before
reporting `verified`. This slice accepts standalone projects and isolated
`.agda-lib` environments, preserving per-library and explicit command options.
Existing production library support is unchanged. Complete native joint and
editor workflow integration remain later milestones, not implied by
`search_available`.

The autonomous controller is also available through the explicit application
API (not yet a default or editor backend):

```python
from agdaprover.application.native import NativeAgendaEngine
from agdaprover.application.service import ProverApplication

application = ProverApplication(engine=NativeAgendaEngine(path))
result = application.prove(task)          # Exactly the selected goal.
result = application.prove_prefix(task)   # Existing cursor/prefix semantics.
```

`test_entries` on this application uses the same native engine for independent
virtual-entry tests. The original file stays unchanged between tests. Native
single and prefix candidates share immutable project preparation, source export,
resource supervision and the ordinary fresh validator. A rejected candidate
resumes the retained native frontier, not a new search or a Python fallback.

For the existing closed abstract-implication fragment, the native agenda can
also propose a [refutation certificate](../../schemas/native-refutation-v1.md).
A small, widening side slice prevents general proof search from delaying this
finite check indefinitely. Only exact recipe replay and fresh safe Agda checking
can return `impossible`; the file stays unchanged. Censorship and failure to
find a proof never suffice. This does not broaden the supported logical fragment.

For this controller, `task.max_candidates` limits native move attempts (including
the standard/deep frontend numeric presets). An independent engine `work_units`
limit optionally bounds scheduler steps, native checking attempts and in-memory
symbolic actions; `None`
adds no such limit. Raising one allowance never overrides the other. A native
move can include several checker calls; it is not identical in granularity to
a legacy Python action. Generated/attempted moves and native checking are
reported separately. Wall/CPU/memory/I/O/temporary and physical request
budgets remain shared across slices and validation. No wall cap or source-size
multiplier is introduced. The bounded evidence-only API retains its original
allowance behavior described below.

One-step and principal-variation publication are not yet qualified for the
selected native application and are explicitly refused, not silently delegated.
Explicit legacy depth limits and refinement-model overrides are also refused
until migrated. Use `policy_model` for a role-checked native OR model and
`task.model_path` for focused weights. CLI/default selection, full editor
integration and required benchmark qualification remain open. Agenda progress
has no inferred training credit merely because a branch was visited.

`focused_search=False` on `NativeEvidenceEngine` disables only the focused fast
path for paired measurements. `task.model_path` replaces the focused weights;
the OR-policy override remains separate. Each model is role-checked and pinned.

`work_units` optionally limits native queries plus in-memory focused/rewrite actions. Its default
`None` widens search depth under the caller's physical resource envelope and
cancellation, without a fixed proof-depth or 20-second cutoff. The current
implementation is a first functional slice, not a performance claim: repeated
scope preparation and iterative deepening can be expensive. Broader agenda and
reuse work follows in H7. Exhaustion and failure to find evidence are not
impossibility certificates. Full benchmarks run at H10, not after every edit.
