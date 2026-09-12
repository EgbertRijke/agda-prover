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
eviction/replay, explicit state release, ownership/cost snapshots, cancellation, and close. `solve-evidence` additionally chooses typed
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
existing caller-owned snapshots still require explicit eviction or release.
Use `release` only after relinquishing every use of that state handle, including
retained runs or exported variations. Unlike eviction, release also drops replay
history once no live descendant needs it. Live descendants preserve their
ancestors' recipes; siblings are unaffected. Internal replay ancestors are
collected with their last descendant. No search alternatives are discarded
automatically. `retention` reports owned state/cache counts, not heap sizes or
proof acceptance.
The application bridge releases its own temporary source-export branches after
copying their serialized views, so repeated previews do not accumulate checking
snapshots. The original search branch remains live. Serialized source remains
available for independent acceptance; its native keys are provenance after
release, not live handles. Direct protocol clients retain explicit control of
their exported states.
Replay recipes and queued primitive proposals eagerly seal their small
name/interaction allocation watermarks; unused alternatives must not retain a
whole speculative checking state through a suspended watermark projection.

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
The helper abstracts the selected subjects and their datatype indices, together
with the dependent context suffix. Unrelated earlier parameters remain captured
instead of being copied into new arguments at every nested split. Native coverage
checking can fall back to the full telescope when more generalization is needed;
all attempts remain charged and checked.
Leading hidden and instance function arguments are introduced using Agda's
reduced target and retained as explicit native lambdas before helper preparation.
Their identities, hiding and modality therefore remain available when child
proofs are reconstructed. Result splitting stops after introducing arguments;
splitting a resulting record requires a subsequent action, as in Agda itself.
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
When a proof has observed dependencies on prerequisite assignments omitted from
that batch, the adapter reports those goals as a blocker. Include them in the
batch or use a parent that already owns them; the adapter never silently imports
another branch's helpers or enlarges the source edit. This conservative reuse
check does not rule out a different, independent proof.
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

Closed recursive evidence in an indexed, single-constructor datatype can also
be generalized autonomously. Agda's with-abstraction infers the helper telescope
and case splitting produces its open branches for ordinary search. Native
parameter/index structure, not relation names, determines the proposal. Hidden
value parameters and complete helper signatures are retained. This shares the
`recursive_evidence_operands` ablation and normal owner-termination checks.
Inadmissible generalizations (including without-K restrictions on repeated
indices) leave ordinary alternatives available; they do not refute the goal.

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

The catalogue also specializes a function-valued operand with an authorized
callable mentioned in the goal's native syntax. Agda's telescope identifies
the function slot; local binding identities and resolved declaration names
identify hints without parsing their display. Constructors, dependent
functions and function-valued record projections share this path, including
hidden/instance binders. One function operand is specialized per proposal;
other operands retain ordinary holes or inference, and unspecialized applications
remain available. Occurrence in the goal never grants premise visibility.
The hint includes Agda's weak-head view of a named result type and of an
already authorized callable. Thus transparent aliases can remain useful even
when elaboration exposes their implementation in the goal. Proposals still
use the authorized source expression, not a private implementation name;
abstract definitions remain opaque under Agda's reduction rules.
`target_function_operands=false` disables these additional proposals and their
observations for ablation. The run receipt records the setting across slices.
`application_generation_steps` counts specialized-spine construction against
the existing work allowance and physical symbolic ledger; Agda queries keep
their own counters. Every proposed application still needs normal checking.

Coarse evidence search shares that native rigid-head criterion before building
fully applied dependent skeletons. It does not normalize under binders or guess
alias equality: unknown, dependent and rewrite-enabled heads retain ordinary
checking. Partial/forward application remains available. The informational
`application_shape_observations` and `application_shape_rejections` counters
describe this precheck within charged inference operations; they do not add
spine-construction work or alter proof authority.

`recursive_evidence_operands` additionally offers closed native recursive
results as application operands, optionally together with one goal-mentioned
function. Both proposal sources retain their existing NNUE provenance. Before
offering these compositions, Agda must determine all remaining operand types
without extra unification metas or blocked constraints. Ordinary applications
are retained when that condition is not met. This controls speculative fan-out;
it is not a proof rule or a restriction on Agda's accepted proofs.

The option defaults to true in the opt-in native engine; false restores the
earlier catalogue for ablation, and the run receipt retains it across slices.
Only scoped expressions with closed inferred values/types are reused. New
helper declarations and temporary meta identities cannot escape observation;
owner exclusion and Agda's termination/productivity checks still apply to the
whole composed move. All inference, preflight checks and spine construction
are charged. This improves some induction searches, not every workload; whole
native qualification remains open.

When compound construction supplies the same single-lambda/open-body action,
the controller keeps its preferred copy instead of also scheduling the ordinary
one. This comparison requires the same parent, goal and binder modality; it
does not merge proof states, populated bodies or multi-binder constructions.

`AgendaSearch` provides an autonomous Haskell controller over these primitive
term moves, native case proposals and clause-generated local helpers. Datatype
and inductive-record subjects come from Agda's context/metadata; shared NNUE
ranking orders eligible choices. Case analysis may generalize captured module
or lambda variables into checked local helpers, while Agda still enforces
coverage, modalities and without-K. Hidden-binder exposure retains Agda's
original source-clause operation.

Generated case actions carry opaque parent-bound native binding identities,
including when different locals have the same base spelling. Helper drafts
retain hidden patterns explicitly. During source export, Agda freshens nested
pattern spellings without changing the retained search terms. Known datatype
and sort leaves omit redundant result-split wrappers; record/function and
unknown results keep the operation. User clause commands are unchanged.
Whole search coalesces a function-result split with an already generated
ordinary lambda-to-hole introduction for the exact same parent and goal.
It keeps subject eliminations and record-result splits; it does not identify
their resulting proof states. `coalesce_introductions=false` restores the
overlapping routes. The command catalogue and one-step mode are unchanged.

New clause obligations have a local-closure handoff before broad planning.
Agda tests local inhabitants without new meta assignments or constraints; the
existing NNUE role orders admissible choices. Each choice produces an ordinary
checked transition, while an exact-parent cursor retains other choices and
ordinary planning fallback. Resuming that fallback does not invent a proof
state or increase accepted proof depth. The existing `contextual_evidence=false`
ablation disables this whole-search phase; the cost receipt records
`local_closure_handoffs`. This is the first checked procedure handoff, not
complete native workflow qualification or a replacement for fresh validation.

Contextual composition also adapts the endpoints of an existing hypothesis,
including one just exposed by elimination. Supplied laws produce checked paths
from its endpoints to the goal's endpoints. A changed source endpoint requires
a supplied symmetry operation; changed endpoints are joined using supplied
composition. Unchanged endpoints need no invented reflexivity proof. The
result is an explicit proof proposal, not a silent conversion of the hypothesis.
This applies to abstract relations as well as inductive ones, retains distinct
direct proof alternatives, and shares the existing contextual-evidence switch,
NNUE ordering, resource ledger and final validation boundary.

Scheduling slices keep the queue and alternatives after provisional solutions.
Coarse evidence search runs in soft, increasing work slices and yields to other
branches. It retains pending alternatives, dependent operand substitutions and
their rollback states for the exact parent and goal. Services, including the
NNUE scorer and response channel, are supplied anew on each advance. No Agda
checker call is suspended internally. Native catalogue builders and stateful
scope operations that cannot yet retain progress are replayed and fully charged;
the evidence receipt reports `replayed_catalogues` and `replayed_scopes` separately.
The existing `evidence_depth_reuse=false` ablation restores restarting at depth
zero; true now retains operand progress as well. The agenda receipt identifies
this as `evidence_continuation: operand-progress-v1`. Direct `solve-evidence`
still starts fresh, and one-step behavior is unchanged.
By default, an exhausted retry's queue priority includes its measured work,
so doubling allowances cannot monopolize search ahead of cheap alternatives.
`retry_work_ordering=false` retains the uniform-cost ablation. No continuation
is removed and the physical resource counters are unchanged.
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
When no source goals remain, explicit selection requires the same zero-meta,
zero-constraint closure as an unselected whole run. An implicit metavariable is
not a completed proof merely because its source interaction has disappeared.
Rejected source exports report their status, pending counts and kernel detail,
not a second serialized copy of every proof tree. The diagnostic text uses the
existing presentation allowance; proof structures and search are not truncated.

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

Repeated operations in one native session reuse decoded models after comparing
the current complete file bytes (and legacy role sidecar). Exact hits keep the
existing byte buffers as well as the decoded model; newly read identical buffers
are not promoted into long-lived cache entries. There is one cache
slot per model role. Custom-model edits and invalid inputs remain detectable;
already retained searches keep their original weights. This saves repeated
decoding, not Agda proof checking, and does not change scores or search order.

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

Whole-search construction can additionally expose a finite introduction tree
in one compound action. Agda checks constructor compatibility against the
expected indices using the complete inferred application telescope, including
hidden parameters. A sole surviving constructor, dependent record fields and
function binders can be expanded together; a uniquely matching, meta-free local
can close a leaf. Genuine choices stay as explicit dependent goals. Repeated
families expand only when their native type structure decreases, so recursive
or growing families do not cause unbounded scaffold generation. This is a
proposal termination guard, not an assertion about Agda termination or logical
impossibility. Original alternatives remain available.

An unresolved leaf can also use a shallow projection from an argument introduced
by this same compound construction, with a single-constructor datatype or
inductive record. Agda generates the case
clauses and checks the exposed fields' instantiated types; no projection
function has to be declared beforehand. Only an unambiguous local completion
is retained by this compound action. Multiple possible fields or containers
remain ordinary search choices. This does not recursively enumerate case
trees or treat coinductive records as inductive data.
Ambient inputs stay with ordinary shared elimination, so this shortcut does
not independently project one field ahead of dependent sibling operands.

Completed clause helpers retain their native declarations and scoped hole
solutions. A meta-free helper application alone is insufficient: its body
may still contain obligations, and its generated name cannot survive checking
rollback without the declaration. Ordinary application values keep Agda's
usual reification. All speculative checking and case generation are charged;
source export, replay and independent validation remain required.

Each generated function binder extends both Agda's typed context and its local
syntactic scope with the same native identity. Nested holes therefore retain
usable explicit, hidden and instance names, including function-valued record
fields. Replay restores that scope; it does not recover bindings from display
text or conflate equally typed alternatives.

Types containing native metavariables also remain ordinary obligations instead
of being eagerly expanded. This avoids multiplying postponed substitutions
while building a compound proposal. Atomic refinement and dependent elimination
remain available to constrain those types; this restriction applies only to
the optimization, not to solvability, proof size, or the user's search budget.

The compound construction uses the session's usual state-bound proposal,
checking, budget, exclusion and replay contracts. Its individual observations
and checks count toward work, even though it is one agenda action. It is
disabled with the existing `evidence_macro=false` scheduling switch and never
runs as part of `start-step`; one-step editing still exposes its children.
Constructor-headed applications and record literals also share the existing
construction-priority tier, with model order retained within that tier.

Joint search can propose defining clauses from a contiguous block of later
selected computation statements. It inspects native type applications for an
owner application at one endpoint, converts its operands with Agda's own
term-to-pattern operation, and retains the other endpoint as a structured RHS.
Constructor/literal patterns must be linear, captured variables must belong to
the current context, and referenced declarations must be available at the
definition site. This does not recognize a particular relation or assume its
laws; every proposed definition and every selected statement still needs proof.
Agda decides coverage, dependent indices and source-owner termination.

Solved metas are instantiated before inspecting clause patterns. The original
full-pattern candidate remains preferred. When it is unavailable, the observer
can omit hidden/instance patterns and let Agda infer their indices from the
original signature and explicit patterns. Captured RHS variables and visibility
checks remain unchanged. This is a checked generalization attempt, not permission
to assume that a specialized carrier is the arbitrary carrier in the signature.

These proposals precede later constructor probes, which could otherwise turn
the useful computation statements into suspended constraints before the
definition is constructed. Other alternatives remain available. Source order
is preserved independently of agenda order; unselected goals are not consulted.
Unsupported pattern forms fall back to ordinary search. Observation work is
charged, drafts retain their state and allocation identities, and the existing
`evidence_macro=false` switch disables this whole-search path. One-step editing
does not run it. This restores an existing joint-search capability in native
form; it does not establish whole-workload qualification or change the default.

Recursive calls use the enclosing source definition and Agda's checked clause
patterns. The current mutual group is never ordinary evidence. Dedicated calls
can use direct descendants, function-valued children and reconstructed wrappers;
Agda infers unchanged and hidden parameters from the expected result. Unknown
descent through with-abstraction retains a typed fallback, not a termination
claim. Generated helper goals retain their source owner across branch replay.
New helpers join that owner's mutual group before Agda checks termination, so
cycles spanning a helper and the source function cannot evade the check.

Primitive moves also expose fully applied recursive calls anchored by a scoped
descendant, including applications of function-valued children. Remaining
arguments are coupled interaction goals, with inference-first and explicitly
supplied hidden/instance forms. Actual coinductive copattern contexts can
propose owner calls without claiming inductive descent. Every move still passes
the same owner-group termination/productivity check. The recursive head is not
made an ordinary premise, and explicit exclusions apply before generation.
Native descent facts feed the existing scheduling/NNUE boundary. These moves
also rebuild shallow wrappers from single-constructor argument families,
including named and anonymous inductive records. Agda's constructor arity
separates fields from uniform parameters; inferred and supplied hidden forms
remain available. Scope/exclusions apply to constructors and record fields,
and coinductive records are not inductive wrappers. These finite proposals
complement the coarse search for more elaborate recursive operands;
they do not establish whole-benchmark coverage or promote the native default.

Recursive templates can also propose a completed call when their coupled
operands have unambiguous local inhabitants. Agda checks the whole application
first, so a later argument and the expected result can determine earlier
dependent domains. This shares the constructor scaffold's local-value check;
ambiguous or unresolved operands retain the original open template. Only
meta-free completions leave the speculative transaction, and all inspection
and checking is charged. Completion does not replace termination or fresh
validation, nor does it trigger exhaustive argument search during generation.

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
only rigid result shapes: functions, universes, actual datatype/record identities,
and fixed parameters of the current goal. Parameters introduced while inspecting
a function's telescope, stuck definitions and metas remain unknown and never
warrant discarding an application. Hidden arguments and dependent indices are still
inferred by Agda when the proposal is checked. This avoids queuing provably
unrelated heads without replacing conversion with textual type comparisons.

Hidden and instance operands are not limited to inference-only applications.
The primitive catalogue retains those original forms and also offers prefixes
with supplied interaction holes, including hidden operands after explicit ones.
The two native spines grow linearly with the telescope; no omission-pattern
powerset is generated. Agda still instantiates dependent types in the same
branch, and unresolved hidden metas never qualify as a closed proof.

Autonomous result splitting omits rigid local-type leaves as well as known
datatype/sort leaves: these have no fields or trailing function arguments to
expose. It does not repeatedly wrap them in empty local helpers. Dependent
variable elimination, function/record result splitting and explicit user
commands remain available.

Primitive moves can also eliminate a computed empty value. The adapter asks
Agda whether a supplied function's dependent codomain is empty, including
impossible indices and empty record fields. A typed eliminator leaves its
arguments as ordinary, coupled goals. Blocked or inhabited codomains do not
justify this move; broader evidence search remains available. Native binder
identities, hiding and modalities are retained, and the reconstructed proof
still requires independent validation.

Native constructor closures introduce the expected telescope and finish with a
visible constructor that has no fields. They retain binder hiding and native
identities; Agda, not the generator, decides whether result indices match.
Joint search also offers these small proposals on other selected goals with
observed dependencies so that later laws can constrain earlier definitions.
Missing dependency evidence retains the ordinary schedule without assuming
independence. `joint_constructor_propagation=false`
disables that cross-goal scheduling without changing the resource envelope.
Source assignments inferred by Agda are retrieved through its solved-goal
operation, then checked and recorded as ordinary reconstructible moves. No
interaction is silently removed or accepted on the strength of a meta count.
Partially inferred values retain their native structure, with missing values
reintroduced as explicit, fresh interaction holes through Agda's elaboration
view. They never carry anonymous meta identities into source reconstruction;
checking the proposal in its original branch preserves coupled constraints.

Autonomous case search also offers one compound move for local variables with
one-constructor inductive types or inductive records. Within that batch, native
type dependencies put a dependent witness before its prerequisites; NNUE order breaks ties among
ready subjects. Dependencies through unselected context entries are retained
without making those entries new case subjects. Agda owns all dependent
substitutions and admissibility checks. The move creates a local helper once,
then extends Agda's native split clauses with their telescopes, patterns and
targets intact. Agda's substitutions update pending subject indices; forced
nonvariables no longer need splitting. Rejected subjects are retried only after
another successful split changes the context. The assembled partial helper is
checked from the original parent even if no further subject can be split.
Rejections preserve accepted progress and charge their work without relaxing
Agda's rules; explicit user commands still mean exactly the requested splits.
This reuse is local to one atomic preparation request, not a continuation that
can resume halfway through a cancelled kernel operation.
Individual eliminations retain their original ranked order and remain
available; multi-constructor variables are not combined into an exponential
case tree. `multi_subject_clauses=false` retains single-subject scheduling for
comparison without changing the user's resource envelope.

The agenda's optional `progress_ordering` uses spent cost plus sixteen units
per remaining selected interaction and unresolved hidden obligation. The latter
uses the larger of the hidden-meta and constraint counts, since they can overlap.
Moving an open goal into suspended checking therefore does not masquerade as
progress. Early constructor propagation also requires a closed checked term
without increasing outstanding constraints, and an observed newly completed
assignment to another open source goal. Merely dependent but nonspecifying
proofs keep their ordinary place in the search. Ordinary search retains deferred
alternatives. This soft estimate is neither a proof-cost lower bound nor a
discount against resource accounting. Receipts identify
`cost-plus-pending-obligations-v3`; disabling it retains `cost-only-v1`. One-step
ordering is unchanged. See the [session contract](../../schemas/symbolic-session-v1.md).

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

Autonomous case catalogues receive the same name exclusions as term proposals.
They do not expose an excluded constructor or record field through generated
patterns. Explicit user clause commands remain separate. Native draft replay
preserves the registration and source range of an already existing interaction;
only fresh draft holes are registered anew. Presentation ranges cannot replace
the identity of an existing obligation.

`work_units` optionally limits native queries plus in-memory focused/rewrite actions. Its default
`None` widens search depth under the caller's physical resource envelope and
cancellation, without a fixed proof-depth or 20-second cutoff. The current
implementation is a first functional slice, not a performance claim: repeated
scope preparation and iterative deepening can be expensive. Broader agenda and
reuse work follows in H7. Exhaustion and failure to find evidence are not
impossibility certificates. Full benchmarks run at H10, not after every edit.
