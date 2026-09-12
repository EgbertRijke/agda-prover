# Resident symbolic session v1

H2 provides single-owner checking, retained branches, explicit eviction/replay,
source invalidation, and cumulative work. H4 adds the coarse `solve-evidence`
operation; H5.2 adds Agda-native clause proposals and checked clause transitions.
None grants proof verification authority or edits user files.

## Invariants

- One owner serializes access to its Agda states. Each key binds to a fresh
  session nonce, epoch, and issued branch; a context additionally binds to a
  live interaction in that branch. Wire keys are validated, not trusted.
- The owner uses Agda's library-level operations directly. It has no separate
  editor `CommandState`; Agda's interaction/meta store is part of the saved
  `TCState`. The existing JSON bridge remains unchanged.
- Each candidate starts from the requested full state. Failure, interruption,
  observation, and success all leave the parent available and unchanged.
  A successful proof transition publishes a child key distinct from its parent;
  an identical application may reuse its already checked, resident child.
  Checked native evidence belongs to
  that child, not to a parent or sibling with coincidentally equal meta numbers.
- Pending interactions, hidden metas, and constraints remain obligations.
  `apparently-closed` is not `verified`; fresh validation remains independent.
- Dropping a snapshot keeps its structured action ancestry. Replay runs Agda
  again and issues a new key. An old key/evidence never silently changes meaning.
- Source witnesses cover the loaded root and imports. Changed/missing inputs
  invalidate the session, including retained branches. Hashes are not the
  authority for witness equality.
- Work is charged outside snapshots. Rejections, replay and cancellation cannot
  reset the ledger. An operation-start receipt precedes checking so a supervisor
  can retain dispatched work if the worker is killed; unknown final work is not
  reported as zero. Process CPU/RSS/I/O supervision remains the caller's duty.

## Requests and events

Start `agdaprover-symbolic session ABSOLUTE-FILE [ABSOLUTE-INCLUDE ...]` in a
prepared project copy. No ambient library registry is consulted. The initial
`session-start` event supplies the root state key. All events have
`schema_version: "agdaprover.symbolic-session-event.v1"`.

The optional startup flag `--reuse=exact` (default) enables exact application
reuse; `--reuse=disabled` forces each application to check again. It precedes
`-- CHECKING-OPTIONS`, may occur at most once, and accepts no other values.
Capabilities advertise these values as `transition_reuse_policies`.

Library-backed startup adds `--library-file=ABSOLUTE-REGISTRY` and repeated
`--pin-config=ABSOLUTE-FILE` before `-- CHECKING-OPTIONS ...`. Exactly one or no
registry is allowed. Every configuration path is absolute; the registry itself
must be pinned. Agda loads only this registry, with default libraries disabled.
The native owner compares every manifest in Agda's actual library cache against
preload pins. Agda locates its own primitive-library manifests; these are also
pinned, not exempted or recognized by hard-coded filename. Missing pins or a
configuration change during load prevent session startup. Subsequent byte/path
changes invalidate the epoch. The cumulative input ledger includes these reads.

The application supplies paths from the existing immutable project overlay,
not the user's ambient registry. Per-library flags remain attached to their
original libraries, while explicit command options retain their existing role.
No library-specific interpretation or semantic source rewriting is performed.

A request is one UTF-8 JSON line, with these exact common fields:

```json
{"schema_version":"agdaprover.symbolic-session-request.v1","request_id":1,"operation":"pending","state":{"session":"nonce","epoch":0,"branch":0}}
```

Request IDs are nonnegative and strictly increasing per connection. State keys
have exactly `session`, `epoch`, and `branch`, with nonnegative integer counters.
Each operation permits only its listed additional fields:

| Operation | Additional fields | Result |
| --- | --- | --- |
| `pending` | `state` | Open goal IDs, open metas, constraints |
| `observe` | `state`, `goal_id`, `mode` | Structured observation v1 |
| `dependencies` | `state`, `work_units` | Parent-bound conservative native dependency observation |
| `give` | `state`, `goal_id`, `expression` | Child state, native evidence view, obligations |
| `make-clause` | `state`, `goal_id`, `action` | Parent-bound native clause proposal, not a child state |
| `apply-clause` | `state`, `goal_id`, `action` | Checked native helper/clause child, evidence view and dependent obligations |
| `reconstruct-goal` | `state`, `goal_id`, `descendant` | Assemble native drafts from a descendant, recheck from the original goal's parent, return a provisional checked transition |
| `reconstruct-goals` | `state`, `goal_ids`, `descendant` | Reconstruct a nonempty ordered selection into one new coupled branch; return all entries and final pending obligations |
| `export-goals` | `state`, `goal_ids`, `descendant` | The same checked batch with native source presentations, including required hidden-clause binders |
| `start-search` | `state`, `limits`, `ranker`, `model_path`, `native_path`, `focused_search`, `exclude_names`; optional `primary_model_path`, `focused_model_path`, `scheduling`, `goal_ids`, `action_limit`, `depth_limit` | Create a retained autonomous run over all or selected pending source goals |
| `start-step` | Same fields; exactly one `goal_ids` entry is required | Retain one-move root alternatives; yield each checked transition without solving its children |
| `advance-search` | `run`, `steps`, `limits`; optional `action_limit`, `depth_limit` | Advance a scheduling slice; return a new run revision or terminal finite exhaustion |
| `search-cost` | `run` | Retained run cost snapshot |
| `discard-search` | `run` | Retire the run handle/frontier, retaining its cost receipt |
| `infer-helper` | `state`, `goal_id`, `mode`, `application` | Parent-bound native helper signature, not a proof transition |
| `solve-helper` | `state`, `goal_id`, `mode`, `application`, `limits`, `ranker`, `model_path`, `native_path` | Finite native helper search with the ordinary provisional candidate/cost result |
| `solve-evidence` | `state`, `goal_id`, `limits`, `ranker`, `model_path`, `native_path`, `exclude_names`; optional `primary_model_path`, `focused_model_path`, `focused_search` | Search status, provisional child/evidence, cumulative search cost, selected policy choices |
| `propose-refutation` | `state`, `goal_id`, `work_units` | Source-bound negative recipe for the existing abstract implication fragment; no proof authority |
| `evict` | `state` | Drop child snapshot; preserve replay ancestry |
| `release` | `state` | Relinquish a handle permanently; collect ancestry no live descendant needs |
| `retention` | none | Owned state/cache counts; no checking or proof authority |
| `replay` | `state` | Rechecked state key (resident states are returned unchanged) |
| `cost` | none | Current cumulative native-operation counters |
| `cancel` | none | Cancel the active request, or report idle |
| `close` | none | Cancel any active request, then close the session |

`start-step` shares native ranked primitive/clause proposals, ownership, costs,
slicing and source export with `start-search`. It disables compound evidence
search and refutation. Each candidate is a single accepted transition from the
original parent; rejecting a source presentation retains the other root moves.
Partial exports retain native interaction identities until source rendering.
The application fresh-loads an authorized partial edit before returning
`accepted-step`, never `verified`. Its action uses `agdaprover.native-step.v1`,
tag `native-refinement`, `expression`, `source_edit`,
`expected_state_effect.subgoals`, and `reconstruction_validation`; it always
sets `complete_proof: false`. Existing editors apply the structured source edit.

Goal IDs must fit Agda's nonnegative machine-sized interaction identifier.
The [native refutation contract](native-refutation-v1.md) defines its scoped
fragment, recipe, work accounting and fresh acceptance. The agenda may return
`refutation-candidate` with the negative proposal and a retained run revision;
rejection resumes ordinary search. It never calls finite search exhaustion
`impossible` on its own.
Modes have the five observation-v1 meanings. `expression` is untrusted Agda
syntax; Agda parses, scopes and checks it with ordinary non-forced `give`
semantics. The returned evidence retains the internal term, type, telescope,
resolved global names and child key; `display` is presentation only.

At most one native request is active. Additional work requests report `busy`;
control requests remain available. An `operation-start` event acknowledges
dispatch before checking, followed by `operation-result` with `outcome` and
`cost`. Control commands emit `control-result`. EOF/close produces `session-end`.
Malformed requests emit `request-rejected`; unvalidated IDs need not be echoed.
Fatal startup or transport errors emit `session-error` and exit nonzero.

Run-operation rejection need not carry the fields of a successful run. Clients
retain its reason/detail before testing successful selection and model pins;
they must not report a missing success envelope as model drift. Unexpected
adapter exceptions close the owner and retain the diagnostic cause. Such an
exception is never a proof-search exhaustion or an accepted candidate.

An operation's rejection distinguishes foreign session, stale epoch/inputs,
unknown/evicted state, unknown goal, kernel rejection/blocking, cancellation,
and internal failure. Only successful transitions issue or reuse a usable child state.
Agda warnings about unresolved goals/metas/constraints remain obligations;
new non-meta warnings, including termination failures, reject the transition.

`accepted-partial` means there are still interaction goals. `accepted-blocked`
means no interaction goals remain, but hidden metas or constraints do.
`apparently-closed` requires all three to be empty. None means `verified`.

## Resource and ownership boundaries

### Native dependency observations

`dependencies` accepts a positive integer or null `work_units` allowance.
It returns `{parent, dependencies}`, where the parent is the exact issued
state key and the inner object uses `agdaprover.symbolic-dependencies.v1`:

- `status`: `observed` or `censored`; the latter is an incomplete traversal,
  not absent dependencies or a logical failure.
- `independence`: always `unknown`; this contract grants no splitting,
  cross-state reuse, discarded obligation or substitution-merging authority.
- `constraint_count`: all awake/sleeping native constraints, conservatively
  treated as a global coupling barrier rather than flattened delayed closures.
- `reachable_instance_metas`: native meta identities seen in reachable types,
  declarations and assignments. This is not all possible future instance work.
- `unknown_reasons`: opaque/blocked/postponed structures found during traversal.
- `goals`: observed interaction/meta IDs, known prerequisite interaction IDs,
  reachable native meta IDs, and reachable declaration count.
- `preferred_goal_order`: stable ascending known-prerequisite count, or original
  order when censored, constrained, instance-dependent or opaque.
- `proof_authority`: false.

Native types/telescopes, local lets, sort annotations, level terms and local
declaration/solved-meta references retain their identities. The traversal uses
Agda's names-and-metas operations; ordinary term folds that skip sort annotations
are not sufficient. Imported interfaces remain pinned and are not recursively
expanded into a full library scan. Local declarations are looked up on demand
through Agda; summary memoization and visited native identities terminate cycles.
The observer is read-only and does not create or assign metas.

`dependency_queries` counts reached goal/meta/declaration reads;
`dependency_nodes` counts visited graph nodes. Both contribute to cumulative
symbolic work, including censored/repeated observations, and physical budgets
still apply. With ordering enabled, a multi-goal planning step borrows at most
the initial macro slice for this observation. It skips the optional pass when
the remaining allowance would leave no room beyond that slice. Incomplete
observations fall back to original ordering; they do not suppress ordinary
proof search. Single-goal plans do not pay for this pass.

Snapshots are parent-branded. Every accepted move still updates one coupled
Agda state, and the next planning step observes that new state. Unselected
goals remain pending and are never promoted into the selection by this heuristic.
Future elaboration can introduce new dependencies; this is intentionally not
an independence proof or a nonspecifying-theorem classifier.

### Exact application reuse

Exact application reuse is task-local and never merges similar goals. Its key
contains the full issued parent/session/epoch key, the interaction ID, and either
the identical untrusted source string or a sealed native proposal identity.
The latter binds to one issued proposal's original syntax, allocation and scope,
not to Agda abstract-expression equality (which ignores some scope information),
a pretty-print, a model feature, or a hash. Separately issued proposals stay
distinct even if their presentations coincide. Parallel proof witnesses are
not identified just because their types match.

The cache retains only accepted transitions with a resident child snapshot.
Source validation and parent ownership checks still happen on every request.
Partial/blocked children retain all obligations; the cache never promotes their
status to closed. Rejected, cancelled, or censored attempts are not negatively
memoized. Reconstruction and replay bypass reuse and check again; final fresh
Agda validation remains mandatory. Evicting or releasing a child removes its cache entry,
and invalidating/closing the epoch drops the entire table. Cache retention is
bounded by the retained accepted children, within the caller's physical budget.

`exact_reuse_queries` and `exact_reuse_hits` are cumulative native counters.
Each lookup charges one `symbolic_actions` unit; only actual checking enters
`checking_attempts`/`accepted_checks`. Requests, source reads and physical time
are still charged on a hit. Disabling reuse skips both lookups and their charges.
This is exact transition reuse, not cross-run caching or a proof of canonical
equivalence between independently created Agda states.

The native ledger counts entered owner requests, checking attempts, accepted and
rejected checks, clause/helper queries, replayed actions, cancellations, input bytes read,
and elapsed monotonic nanoseconds/process CPU picoseconds during owner operations. It is
not an OS-wide resource budget and excludes initial Agda loading and transport
work; an external supervisor must account for the entire worker process.
Every work dispatch has its own monotone receipt count, including requests
rejected before entering the owner. A killed worker cannot provide its final
counts: retain the last snapshot and receipt and mark final work unknown.

Input frames default to 16 MiB. `AGDAPROVER_SYMBOLIC_FRAME_BYTES` changes this
transport envelope. Oversized/unterminated frames close the connection; no
unbounded work queue is created. Native snapshot/trail residency is caller-
managed through explicit eviction/release and process budgets. Replay publishes only
its final handle and retires the resident snapshots of internal intermediate
steps, including on ordinary replay failure. Their native recipes remain while
needed by the returned descendant. Pre-existing caller-owned handles are never
retired implicitly.
Replay recipes strictly capture their small allocation watermarks rather than
lazy projections that would retain evicted checking states. This envelope does not
impose a mathematical proof-size or search-depth limit.

### Explicit state ownership

`release` returns `{"status":"released"}`. The caller relinquishes **all** uses
of that handle, including references in retained runs and variations. Subsequent
requests using it fail with `unknown-state`; release is not a reference decrement
for one of several callers. Root release fails with `cannot-release-root`.
Foreign, stale and unknown keys fail without changing other ownership. Source
drift still invalidates the complete epoch, including evicted states.

Release removes the resident snapshot and exact-application entry. If live
descendants still depend on its immutable replay recipe, that recipe remains
private until the last descendant is relinquished. Each retained branch has
exactly one replay parent; child counts permit transitive collection without
scanning or pruning the search frontier. Siblings and parent transactions are
unaffected. Internal unpublished replay ancestors are collected by the same
rule. Branch identities never get reused. Cancellation rolls back ownership
changes while preserving the physical-work ledger.

`retention` returns `agdaprover.symbolic-retention.v1`, with integer fields
`epoch`, `retained_states` (all branch records, including root and required
ancestry), `resident_states` (records with checking snapshots),
`replay_only_states` (unpublished replay ancestry), `released_ancestors`
(relinquished handles still needed for replay), and `cached_applications`.
It also includes `closed` and `proof_authority: false`. This serialized
observation counts records under the owner lock; it cannot race checking or
serve as an asynchronous cancellation command. Counts are not byte estimates,
live-heap measurements, proof certificates or permission to release a state
still owned by another consumer. Its normal dispatch receipt remains charged.

Runtime sessions fix the loaded options/toolchain and pin the exact bytes and
canonical paths corresponding to Agda's root and imported interface sources.
Checks compare witnesses before and after an operation. Drift clears the branch
table and advances the epoch, even if the old bytes are subsequently restored.
Reloading requires a new session; no unchecked key can resurrect an old branch.
The source tree's declaration bodies are never rewritten by this interface.

## Clause operation

`action` uses the exact existing
[`agdaprover.clause-action.v1` contract](interaction-operations-v1.md): an ordered,
nonempty `variables` batch, `result`, or `ellipsis`. Unknown versions, fields,
mixed intents, empty variable batches, and whitespace-separated subjects inside
one name are rejected before entering Agda. Actual names and admissibility are
resolved by Agda's `makeCase`, not by a local syntax or datatype classifier.

Agda can expose hidden/instance binders instead of splitting them, revise later
subjects after a dependent split, introduce trailing arguments, split record
results into copatterns, and expand ellipses. Its options, without-K restrictions,
scope, and preceding/following clauses remain authoritative. Named splitting
does not make module-, let-, or lambda-bound variables into clause parameters.

`make-clause` success returns `parent`, `goal_id`, and `proposal`; it does **not**
issue a child key. The proposal schema is `agdaprover.symbolic-clauses.v1`, with
`status: "proposed"`, echoed `action`, `variant` (`Function` or `ExtendedLambda`), a
structured `function` identity with a presentation `display`, `clause_count`,
and Agda-rendered `clauses`. `source_range` and `goal_range` are zero-based,
half-open character offsets from Agda's original abstract clause and interaction
point. They are observational ranges, not authorization to replace source.
`applied` and `proof_authority` are both false.

Internally the opaque, parent-branded proposal retains Agda abstract clauses,
case context, and the generation checking state. Rendering is only a view;
clause execution uses native structure with a validated parent and never
reconstitutes semantics from that display. A wire response does not persist
an executable proposal handle. Generation leaves the parent unchanged, including
on failure/cancellation, and charges `checking_attempts` and `clause_queries`.
It does not charge `accepted_checks` or count the generated holes as accepted
subgoals. Replay an evicted parent first and regenerate against its new key.

### Checked clause execution

`apply-clause` accepts the same action schema and returns the ordinary checked
transition (`status`, new `state`, `pending`, native `evidence`, and false
`proof_authority`). The named goal must still be open in the requested branch.
It does not consume or parse the displayed `make-clause` response.

Execution abstracts the goal's dependent context into a native local helper,
using Agda's telescope/type reification, and resolves the selected subjects by
native name identity. Agda generates the corresponding helper clauses and
decides whether the elimination is admissible. This preserves the
parent's global definitions rather than mutating an already checked declaration
or its compiled clauses. The final native helper is checked through non-forced
`give` from the unsplit parent. Nested splits can operate on its new goals.
Dependent field/branch obligations live in Agda's shared child state; they are
not independent text placeholders.

Autonomous clause proposals retain native binding identities in opaque,
session/parent/goal-branded `ClauseMove` values. Printed local names are ranking
features only, not split addresses. User-supplied `apply-clause` commands keep
Agda's own name-resolution behavior and their unchanged wire schema. The
generated catalogue omits result splitting for a known datatype or sort leaf:
there are no fields or trailing arguments to expose in its generalized helper.
Functions, records and unknown/stuck heads retain that alternative.

Hidden-binder exposure is not mistaken for elimination. Pattern hiding and
modality are retained. Captured module or lambda variables may become helper
arguments; scope resolution, coverage and without-K remain Agda's decisions.
Helper clauses may
cover more cases than an original clause filtered by surrounding clauses; they
must themselves pass Agda's coverage/checking. No original source is rewritten.
Retained helper drafts explicitly bind hidden arguments returned by Agda, so
rechecking cannot silently replace their identities before later drafts are
spliced into them.

Speculative helper assignments/definitions/constraints are rolled back before
the final check. Native drafts reserve their retained name and interaction ID
allocation ranges during checking and replay. Generated holes receive distinct
IDs and scopes; references to absent speculative metas are rejected. Only an
accepted transition publishes a child. Each entered clause generation, context
recheck and scaffold check charges the cumulative checking ledger; the two
generations also charge `clause_queries`. Replay rechecks the retained draft,
without regenerating clauses or resetting work.

These session primitives also feed the autonomous native agenda; their direct
results are not authorized source patches. In particular, display
text can mention a hidden parent binder that must first be exposed in source.
Do not paste it blindly or interpret a closed native branch as `verified`.
Independent fresh checking remains mandatory. The opt-in native workflow uses
`export-goals` below; default promotion remains subject to qualification.

## Native goal reconstruction

`reconstruct-goal` addresses an original goal with `state` and `goal_id`, plus
a `descendant` state key in the same session/epoch. The descendant must actually
descend from that parent. Evicted descendants retain native draft ancestry and
can be reconstructed without treating their old heap snapshot as evidence.

Accepted source inputs are retained as scoped native drafts. The operation
assembles solved child expressions using native interaction identities,
preserving helper declarations, scopes, binders and clause structure. It does
not parse display text, fabricate a missing assignment or use another branch's
leaf. One native traversal expands draft dependencies with cycle protection.

Agda checks the assembled draft again from the original parent under the usual
owner/termination/warning rules. The operation returns a new provisional
transition and charges its checking work; it does not mutate either input
branch. Remaining child goals or hidden obligations prevent apparent closure.
Source drift invalidates the epoch. Source export and independent fresh
validation remain separate duties.

`reconstruct-goals` uses the same native ancestry with a nonempty, duplicate-free
array `goal_ids`. Each ID must be an open goal in the original `state`. The
assembled drafts are checked successively in one new branch, so later proofs
retain the substitutions made by earlier definitions. Unknown goals, missing
assignments, foreign/stale references and unrelated descendants are rejected.
On failure none of the intermediate states is published; spent checking work
is retained. Existing parent and descendant branches are unchanged.

Success returns `state`, `status`, `pending`, `proof_authority: false` and
`entries: [{goal_id, evidence}, ...]` in requested order. Each evidence value
belongs to its checked prefix; the top-level state/pending describe the final
coupled branch. Unselected source goals and hidden obligations remain pending.
An apparently closed batch is not independently verified and is not a source
patch. Validate the reconstructed source together, not individual proof terms
against unrelated copies of the original file.

### Native source presentations

`export-goals` uses the same batch/ancestry/rollback contract, and adds `source`
to each entry. Its schema is `agdaprover.symbolic-source.v1`, with
`proof_authority: false`, zero-based half-open `goal_range`, `kind` and `body`.
`kind: expression` replaces only the original hole. `kind: clause` additionally
has `source_range` for the original containing clause.

The renderer detects referenced context bindings absent from the native scope.
It asks Agda's `makeCase` operation to expose them without splitting, then maps
the retained RHS's binding identities to the generated LHS telescope. Hiding,
instance arguments and native helper layout are preserved. No textual
substitution, constructor recognition or library-specific rules are involved.
Exposure and its context check are charged in the session ledger. Rendering
does not mutate input branches or count as independent validation.

When nested native clauses are exported together, Agda's binding-pattern
printer freshens their local spellings against the enclosing scope. This is a
presentation-only traversal: the retained search drafts, native identities and
NNUE ordering inputs are unchanged. The final rendered source must still pass
independent Agda validation.

The source consumer permits direct expression edits and exposed whole-clause
holes with single- or multiline original heads. Agda supplies the LHS-through-RHS
range; lexical guards reject embedded or multi-declaration replacement ranges.
The renderer leaves original `where` declarations outside the edit, preserving
their scopes and comments. Module indentation, trailing comments and neighboring
mutual definitions stay intact. Joint edits across Markdown fences distinguish
prose from actual unfinished Agda goals using full-file lexical context.

Exposure inside extended-lambda branches or nested RHS expressions remains
explicitly refused; direct expression edits still work there. These restrictions
do not grant permission to hoist embedded declarations. Both existing supported
file kinds (`.agda` and `.lagda.md`) use original character coordinates, not UTF-8
byte offsets. Every handoff still needs independent fresh validation; model
bytes and default selection are unchanged.

## Resident search runs

`start-search` creates a native controller without advancing its frontier.
Optional `goal_ids` is a nonempty, duplicate-free list of currently pending
interaction IDs. Omission retains whole-state solving. Empty, duplicate,
negative, noninteger and unknown IDs are rejected; explicit null is not omission.
Selection is caller authority, not an independence claim. Other source goals,
metas and constraints remain in the same checking state. New interaction goals
created by selected moves are selected AND obligations too. Existing unselected
goals are not scheduled, although their constraints may affect checking.

Run results echo `goal_ids` (null for whole-state solving). A selected candidate
means no selected interactions remain; it may still have global obligations.
Every candidate reports the complete `pending` state. Reconstruction and fresh
validation must reject unresolved selected evidence or unsupported dependency
requirements. It is never permissible to equate a selected candidate with a
globally closed or independently verified proof. Whole-state candidate detection
still requires no interactions, open metas or constraints.

`limits` has the same `{ "work_units": positive-integer-or-null }` format as
evidence search. `ranker` is `nnue` or `symbolic`; model/native paths are explicit
nullable paths. Models are loaded once for this run. `focused_search` is boolean
and `exclude_names` is the existing list of forbidden premise names. The optional
`scheduling` object has the first four required fields below and optional
`dependency_ordering`, `progress_ordering`, `retry_work_ordering`, `evidence_depth_reuse`, `coalesce_introductions`,
`target_function_operands`, `recursive_evidence_operands`,
`joint_constructor_propagation` and `multi_subject_clauses` booleans
(defaults shown):

```json
{"structural_delay":2,"macro_delay":8,"initial_macro_work":64,"evidence_macro":true,"dependency_ordering":true,"progress_ordering":true,"retry_work_ordering":true,"evidence_depth_reuse":true,"coalesce_introductions":true,"target_function_operands":true,"recursive_evidence_operands":true,"joint_constructor_propagation":true,"multi_subject_clauses":true}
```

Delays are nonnegative scheduling priorities, not proof-depth restrictions.
The initial macro slice is positive and grows on retry. `evidence_macro` is a
feature flag for the coarse fallback; disabling it restricts the configured
fragment and must not be confused with a general impossibility result.
`dependency_ordering` enables the conservative read described below. It changes
goal order, never the authorized selection or coupled-state semantics.
`progress_ordering` orders branches by spent scheduling cost plus sixteen units per
remaining selected native interaction (a soft estimate of eight inspect/apply pairs,
allowing introductions, elimination and closure). It does not
infer independence, remove obligations, rebate work or prune alternatives.
The estimate is not an admissible proof-cost bound. Stable serial ties, finite
alternative costs and increasing spent cost preserve fallback fairness. One-step
search uses zero remaining-work estimate and keeps its previous ordering.
The cost receipt records `ordering: cost-plus-obligations-v2`; disabling the
switch records `cost-only-v1`. This is an internal native scheduling option,
not a change to Python defaults or the public task's resource envelope.

`retry_work_ordering` adds the exhausted macro attempt's measured work units to
its continuation priority. Its next allowance still grows, but an exponential
increase in work cannot buy repeated near-zero-cost queue turns. Every
continuation retains finite priority and remains available. This is scheduling
weight only: the physical ledger is neither charged twice nor reset. The cost
receipt reports `retry_ordering: spent-work-v1`, or `uniform-v1` for the explicit
false ablation. One-step search has no macro retries and is unaffected.

`evidence_depth_reuse` retains completed iterative depths and unfinished operand
progress for the exact parent/goal. The continuation includes pending candidates,
dependent sibling substitutions and rollback snapshots inside the Agda adapter;
it is neither serializable nor an accepted proof. Source, epoch and parent
residency are checked at each advance. Scorers and response callbacks are not
retained. Model/visibility settings remain fixed by the owning run. A candidate
is checked again from the original parent before publication, then subject to
the usual reconstruction and independent fresh checking.

Native operations are not suspended internally. A catalogue builder or stateful
scope operation that runs out of allowance is replayed from its own starting
snapshot, without refunding any work. The evidence-v2 receipt adds
`resumed_slices`, `replayed_catalogues` and `replayed_scopes`; counters cover only
work in that request. `depth_iterations` counts newly entered iterations, so a
resumed request may have zero iterations with nonzero `current_depth`.
False restarts from depth zero. The agenda receipt preserves the boolean and
adds `evidence_continuation: operand-progress-v1` (true) or `restart-v1` (false).
One-step behavior and direct `solve-evidence` request semantics are unchanged;
the latter starts a new search, discarding any censored internal continuation.

`coalesce_introductions` lets whole search use a generated ordinary lambda to
expose a function binder without also scheduling a result-split helper for the
same sealed parent and goal. The witness is a native, domain-free, unannotated,
non-pattern lambda with one fresh open body, not a printed arrow type. Populated
or compound lambdas alone do not witness this overlap. All subject splits,
record-result splits, mismatched parents/goals and unknown cases remain. This
chooses a binder-introduction route; it does not merge or claim exact equality
of proof states. Subsequent eliminations still go through Agda.

The setting is effective only for whole search with `evidence_macro` enabled;
the direct clause catalogue, explicit user commands and `start-step` are
unchanged. False restores both routes for ablation. The cost receipt includes
the configured boolean, retained across slices. Like the other switches it
rejects null, strings, numbers and containers instead of treating them as
booleans. No resource allowance, model weights or fresh-check policy changes.

`target_function_operands` adds goal-guided higher-order application proposals.
The adapter observes Pi domains using Agda reduction, and finds native binding
and declaration occurrences in the instantiated, reified goal. Only positively
observed callable seeds from the already authorized inventory may fill those
slots. Target occurrence is a heuristic hint, not visibility, type-conversion
or proof authority. All hiding and modality annotations remain on the native
application spine. This includes callables with only hidden/instance arguments,
function-valued projections and functions supplied as values.

Occurrences include both the instantiated source view and Agda's weak-head
view of the target. Authorized callables additionally retain their weak-head
head identities, so transparent aliases can match an implementation exposed
by elaboration. These observations are charged inference queries and follow
Agda's abstraction boundary. They do not add implementation names to the
premise inventory or merge proofs: candidates retain their original scoped
callables and require the same checked transition and fresh validation.

Each proposal from this option fixes one function slot; other slots remain
ordinary obligations or inferred arguments. Existing application prefixes remain available and
the existing head NNUE ordering is retained. False skips the extra observations
and specializations. The strict boolean is recorded in the agenda receipt and
retained across slices. This option applies to the primitive application
catalogue, including one-step search, not the direct coarse `solve-evidence`
operation. In evidence-cost v2, the additive `application_generation_steps`
counter charges each constructed specialized-spine node to both `work_units`
and the session's `symbolic_actions`. Domain observations remain separately
charged as inference queries. Censorship retains the normal typed paused result;
raising the allowance never erases already spent work.

`recursive_evidence_operands` (default true) connects the existing native
recursive-call generator to the application catalogue. Agda infers a proposed
recursive value and its type inside rollback; only closed native syntax is
retained, excluding inference that introduces extended-lambda helper
declarations. Native domain shapes exclude only rigid mismatches, never compare
printed types. A recursive value may fill one consumer slot, optionally paired
with one independently authorized goal-mentioned function in another slot.
It is not an unbounded saturation or enumeration of all operand combinations.

The same option offers a generalized elimination of closed recursive evidence
in an indexed single-constructor datatype. Agda's with-abstraction supplies the
dependent helper type and its context permutation; native value parameters and
indices are operands, while carrier/sort parameters remain fixed. Agda generates
the case branches and they remain ordinary coupled goals. Hidden parameters
are retained in the helper signature. Excluded constructors, unsupported views
and rejected generalizations retain the ordinary catalogue. No identity-type
recognizer or without-K exception is involved. Helper inference and clause
preparation use the existing charged helper/inference/check counters.

Before a composed draft is offered, a charged preflight requires no new
constraints, fully determined types for its interaction operands, and no new
open metas other than those explicit operands. This positive applicability
filter affects only the extra compositions: ordinary application and recursive
alternatives stay available. Rejected probes restore assignments; only fresh
name/interaction allocation watermarks survive. The source-owner provenance
remains sealed, exclusions apply before generation, and the ordinary checked
move still owns termination/productivity and proof reconstruction.

The option is independent of `target_function_operands`, strict-boolean parsed,
recorded in the agenda cost and retained across slices. False skips recursive
operand observations, compositions and generalized elimination; it does not
disable recursive calls.
Like the function-operand option, it applies to the primitive catalogue, not
the direct coarse evidence operation. Existing inference/check counters and
`application_generation_steps` account for all additional work. Both parent
policy-choice lists accompany a composition; this grants no fresh proof credit.

`joint_constructor_propagation` offers target-directed constructor closures for
other selected pending goals with positively observed dependencies on selected
goals, before broad alternatives for the primary goal. It reuses the native
dependency snapshot (`constructor_probe_goals`); missing or censored edges leave
the ordinary schedule intact and do not establish independence.
The adapter introduces the native telescope and proposes visible constructors
with no fields; Agda checks all indices and implicit parameters. These checked
proposals can constrain earlier definitions without assuming that any goals
are independent. Unselected goals never receive these moves. Censored planning
retains the frontier; every observation/check is charged. The cost receipt
records this flag. Disabling it retains primary-goal construction and existing
evidence fallbacks. No whole-goal search is hidden inside this propagation pass.

`multi_subject_clauses` queues one compound elimination of the local variables
whose types have positively observed one-constructor inductive metadata. It
uses the native case-subject ranking order, then Agda's multi-variable case
operation; it does not enumerate subsets or multiply constructor branches.
Every individual subject remains an alternative. Agda still rejects inadmissible
dependent elimination, including violations of `--without-K`. The existing
refinement role can rank the compound move; it is not credited as a choice of
several mutually exclusive single-subject model actions. The cost receipt
records this switch. False omits compound moves from the queue, retaining the
same catalogue checks and all single-subject moves.

When unification solves a source meta indirectly, Agda may retain its interaction
point for source bookkeeping. The native catalogue retrieves Agda's scoped
solution and offers it before ordinary alternatives. Applying it still invokes
the checker and records a native draft; reconstruction and fresh validation are
not bypassed, and merely having zero open metas is not global source completion.

Success returns `status: ready`, `run`, `cost`, `proof_authority: false`.
A run key has exactly `{session, epoch, run, revision}`; all counters are
nonnegative integers. It is distinct from a branch key. Every completed
`advance-search` consumes that revision and returns a new revision if retained.
Old revisions are rejected as `stale-run`; retired handles as `unknown-run`.
Foreign sessions and changed source epochs cannot resume the frontier.

`search-cost` retains its read-only run/revision contract and additionally returns
`frontier_size` and `principal`. The latter is null for no live frontier, otherwise
`{state, priority, depth, pending, proof_authority:false}` for the next scheduled
branch. Queued moves/continuations expose their parent without executing them.
The lookup validates current source pins; it neither consumes a run revision nor
changes agenda ordering. It does charge ordinary owner/source reads.

The application can request these views between slices and use `export-goals`
to reconstruct individually complete original goals. Consumed source holes with
unfinished children do not become completion options. Preview export work is
charged to the same session; there is no unmetered alternative proof search.
The existing `agdaprover.principal-variation.v1` presentation stays provisional.
Its `active_goal` remains null when the native view cannot identify the next
action's source goal; interaction-number order is not used to guess it.
Pause/resume/stop retain the existing application supervisor. Accepting one goal
requires a separate fresh source check, not merely a checked native preview.

`steps` is a nonnegative scheduling quantum; zero advances no search steps.
Each `advance-search` supplies the total work allowance for the run, not an
additional grant. Raising it retains all already spent work.

An independent optional `action_limit` bounds total attempted native moves,
including rejected moves and coarse evidence retries. It accepts a positive
integer or null, not booleans or fractional values. On start, omission/null adds
no action cap. On advance, omission preserves the cap; explicit null removes it;
a positive value replaces the cap without resetting the attempted count. A
denied attempt does not increment it. `limits.work_units` still counts scheduler
steps and native checks independently; neither allowance overrides the other.
The application maps `task.max_candidates` to `action_limit`, not to work units.

Optional `depth_limit` accepts a nonnegative integer or null. Start omission/null
means no depth cap; advance omission preserves it and explicit null removes it.
Depth counts accepted native branch transitions, not expression size or inner
checker work. A candidate at the exact bound can still be exported. A branch
requiring further transitions is parked, while shallower alternatives continue.
If only parked work remains, the run reports `paused: depth-limit-reached`, not
`unsolved`. Changing the limit restores the exact queued priority/serial order.
Blocked work is moved once per limit setting, rather than repeatedly scanned;
parking itself is charged scheduler work. Costs report `depth_limit`, cumulative
`depth_deferred`, and `depth_unit: accepted-native-branch-transition`.
Compound evidence moves count as one transition but still charge all their
internal search/checking work. Native and Python depth/action units are not
interchangeable performance measurements. No implicit depth cap is introduced.

Advancement returns:

- `paused` with `reason: slice-ended|allowance-spent|action-allowance-spent|depth-limit-reached|cancelled` and a new `run`;
- `candidate` with a provisional native `state` and a retained `run` containing
  alternatives, suitable for reconstruction and subsequent fresh validation;
- `failed` with precise `failure` and a retained `run`;
- `unsolved` for an empty configured finite frontier, retiring the run.

Every outcome preserves a cost receipt and has no proof authority. Ordinary
`cancel` interrupts the active advance request; it does not discard the run.
If cancellation happens outside a native operation, the existing key remains
valid; otherwise use the updated key returned in the operation result. Both
retain charged work. Discard is an idle work request; cancel an active advance
first. Session snapshots/replay ancestry have their own explicit eviction/release lifecycle and
are not all freed merely by discarding the frontier.

`search-progress` events are tagged with the **current advance request ID** and
contain a `payload`: existing versioned NNUE traces, generic
`agdaprover.symbolic-agenda-event.v1` events, or
`agdaprover.symbolic-progress.v1` checked-state/pending observations. These are
diagnostic/progress hooks, not source edits or accepted proof certificates.
No retained callback writes events under the old start-request ID.

Costs include scheduler steps, model work and the native session ledger.
The agenda receipt includes a `models` mapping from loaded model role to model
identity, plus coarse `actions_generated`, `actions_attempted` and
`actions_accepted` counters and the nullable `action_limit`. Native evidence macro internals are not falsely
counted as individual agenda moves. Application counters retain the physical
checking receipt separately, including later export/reconstruction checks.
`work_units` charges native checking and in-memory `symbolic_actions` since
this run was started, plus its own scheduler steps. The session's
`checking_attempts` excludes pure focused/rewrite traversal; both components
remain charged across rollback. Other work deliberately performed in the same session during
a pause also consumes that shared-session allowance; do not sum overlapping
run receipts as disjoint costs. OS CPU/RSS/I/O/temporary-storage supervision,
stop escalation and source patch validation remain the application's duty.
Current slices stop between atomic Agda operations, not inside them. Wire
controls alone are not yet full editor or installed-workflow qualification.

## Helper inference

`infer-helper` delegates to Agda's `metaHelperType` using the same environments
and renderer as `Cmd_helper_function`. `application` is an untrusted string
such as `helper p (f q)`; `mode` uses the five observation mode names above.
Agda scopes arguments and computes the abstraction, including dependent
compound arguments, section parameters, and implicit/instance binders.

Success returns `parent`, `goal_id`, and a `proposal` with schema
`agdaprover.symbolic-helper.v1`, `status: "proposed"`, echoed `mode`, and
Agda-rendered `signature`. `applied` and `proof_authority` are false. Internally,
the nominally parent-branded proposal retains the native abstract signature and
its generation state. The displayed signature is not a serialized executable
handle and must not become a text-derived substitute for that native syntax.

No source or parent state changes, no child is issued, and no proof is claimed.
Success and failure charge `checking_attempts` and `helper_queries`, not
`accepted_checks`; invalid state/goal and kernel failures retain the ordinary
session failure semantics. Finite helper construction and autonomous use are
separate operations, not implied by successful type inference.

### Finite helper construction

`solve-helper` uses the inferred native signature to generate the existing finite
fragment: split one explicit operand of a one-constructor datatype or inductive
record, then return one available explicit argument or constructor field. The
supplied application's native spine determines helper inputs; a returned
function does not become extra input to split. Agda generates the clauses, checks
their dependent indices and coverage, and enforces relevance and without-K.
Coinductive splitting, multi-constructor coverage and arbitrary helper-body
synthesis are outside this operation. Ordinary evidence search remains separate.

Generated clauses and signatures remain native syntax. Speculative definitions
are rolled back; allocation high-water marks protect retained names. Complete
proposals pass through the existing evidence-application NNUE decision family
and the same original-parent transition/checking boundary as `solve-evidence`.
The model/native-path options have the same role and artifact checks, and
`limits` uses the same work-unit contract. Preparation queries, scaffold checks,
clause generation and candidate checks are all charged; helper counters are
subsets of inference/checker work, not extra uncharged work or proof credit.

Its result has the same search status, provisional candidate, cost and selected
choice fields as `solve-evidence`. A candidate is not freshly verified by this
native operation. Choosing which application to generalize in a larger run is
an agenda responsibility; `solve-helper` does not invent that task input.

## Evidence operation

`limits` is exactly `{"work_units": positive-integer-or-null}`. It bounds
inference/checking queries and in-memory search work, not proof size or depth. Null leaves the run under
external CPU/memory/I/O and cancellation supervision; depth widens. `ranker` is
`nnue` or `symbolic`. `model_path` is an OR-decision APNNUE artifact path or null;
`native_path` optionally selects the existing ABI3 scoring library. Null model
uses symbolic order and is reported as unavailable, not as learned inference.
The application normally supplies the pinned bundled OR artifact. The response
includes its loaded hash, checked against the application's pinned model.
Within one session, model loading reuses at most one decoded artifact per role.
Every new model-bearing request rereads the bounded file bytes and, for APNNUE1,
its role sidecar. Reuse requires exact byte equality and still enforces the
requested role; a path, timestamp or hash alone is not a reuse witness. Missing,
changed or invalid files do not fall back to cached weights. Existing retained
runs keep their immutable model versions when a later request changes weights.
On exact hits the existing source-byte buffers are retained, not replaced by
the new identical read. The cache ends with the session and never stores proof
evidence or training data.
`primary_model_path` optionally supplies a focused-branch or proof-term APNNUE
for proof search, or a one-step APNNUE for `start-step`. The old
`focused_model_path` field is a compatibility alias; two non-null paths are
rejected. Wrong operation/model roles are rejected before advancing the run.
The evidence-only response retains `focused_model_id` as the primary hash field
and adds `primary_model_role`; agenda costs use a role-to-hash map. Missing or
null means that role retains symbolic order, not that the OR model substitutes
for it. The application normally supplies both bundled artifacts and separately
interprets primary opt-out and explicit OR opt-in before selecting the native
ranking mode. `focused_search` is an
optional boolean, default true; false provides a local ablation without changing
other evidence search. Null is not a boolean and is rejected.

Proof-term and one-step scoring use native syntax to recognize the existing
feature vocabulary. Unrepresented syntax keeps its original slot, supported
alternatives are ranked only within structural tiers, and all alternatives
remain present. These compatibility views do not determine types, name identity,
generation, pruning or proof validity. Model identities and scored item counts
remain checked against the application's role-specific pins.

`exclude_names` lists visible global aliases to exclude after Agda resolution.
The current and inherited source owner's mutual groups are excluded automatically
from ordinary premises. Dedicated recursive proposals are described below;
excluding the owner's visible alias disables those proposals too.
Excluding a record constructor also excludes construction by
a record literal; changing syntax must not bypass exclusions.
Locals, scoped globals, constructors and projected functions are ranked as complete candidate
sets. `search-policy` events bind each ranking trace to the active request;
NNUE decisions never prune candidates or authorize proofs.

Search returns `candidate`, `unsolved`, or `resource-exhausted`. Candidate has
the ordinary provisional transition under `candidate`; the two failures have
null candidate. Rejected/cancelled checker operations return `failure` and
`search_cost`. Search costs are outside rollback and survive cancellation.
`selected_choices` are decision/candidate pairs on the chosen path, not proof
credit. Only fresh validation of the reconstructed result can grant credit;
native traces remain a distinct versioned format, not legacy training examples.

Successful native drafts preserve their Agda abstract syntax and internal
checked evidence. A winner is checked again from the untouched parent before
publishing its child. Prefix projections remain prefix heads; display reification
is not used as a substitute for source expression structure. Native drafts also
retain structured replay ancestry. No per-candidate callback to Python occurs.

The capability list includes `structural-construction-v1` for datatype
constructors, dependent record literals and Agda-checked absurd elimination.
Hidden/instance record fields are inferred in the live branch with subsequent
fields; record-field backtracking retains dependent constraints. Coinductive
clause construction is not implied by this capability. Additive
`record_proposals` and `absurd_proposals` counters in search cost count proposals,
not accepted proofs. Inference and checking still charge `work_units`.

`structural-recursion-v1` adds current-definition calls from Agda-owned clause
context. It preserves native identities, hiding and dependent operands for
direct descendants, function-valued children and reconstructed wrappers. Source
with-functions resolve through Agda's parent metadata. An abstracted-away parent
pattern is unknown descent: typed contextual arguments remain proposals, never
termination evidence. This is not mutual-program synthesis, general corecursion
or autonomous clause scheduling.

Goals inherit their source owner through accepted refinements and helper
transitions, including eviction/replay; existing unrelated goals keep their own
owner (including no owner). A newly declared native lambda helper is assigned
to the source owner's mutual block before Agda's termination checker runs.
This restores the source-equivalent call graph without replacing any checked
global body. A recursive candidate must pass ordinary non-forced `give` and the
owner-group check inside search, allowing rejection to resume other choices.
Every final transition with a known source owner also checks this group. Parent rollback includes all
mutual-group metadata and termination information.

Expected-result application proposals first compare the inferred native result
type with the target using Agda conversion. Their interaction-hole operands
then retain those constraints, even when constructor checking creates fresh
hidden parameters. Original native argument syntax is retained; general forward
applications remain a fallback. Recursive expected-type saturation is one depth step,
while its per-parameter checker work is fully charged.

Before building that skeleton, coarse evidence search uses the same rigid-head
criterion as primitive application generation. It inspects the already inferred
native telescope without normalizing under its binders. Distinct original
context variables, datatype/record heads, sorts and function types can rule out
a fully saturated application. A telescope-bound result variable, alias,
rewrite-enabled head, or blocked/unknown shape retains normal Agda checking.
`Abs` and `NoAbs` preserve their different binding behavior. Forward/partial
application alternatives remain available; no proof or premise is invented.

The additive evidence-cost v2 counters `application_shape_observations` and
`application_shape_rejections` expose this precheck. The goal-head observation
has one charged inference query. Inspecting the result of an already charged
candidate inference is part of that query, not a second inference or a generated
spine. These counters are informational subsets, not additional work units;
`application_generation_steps` retains its specialized-spine meaning. Final
applications still undergo ordinary checking and fresh reconstruction validation.

Search cost adds `recursive_context_queries`, `recursive_proposals` and
`recursive_validation_queries`. The last counts whole candidate admissibility
queries (non-forced assignment plus source-owner termination) and is a subset
of `checker_queries`, not extra proof authority. `work_units` equals
`inference_queries + checker_queries + recursive_context_queries + focused_actions + algebra_actions + application_generation_steps`; native
result-type comparisons count as checker queries. Rejected proposals and
recursive validation work survive rollback. There are no per-term Python
callbacks, datatype-specific rules or model-weight changes.

`copattern-evidence-v1` adds the existing finite coinductive observation and
projection-construction slice. Native rechecked clause patterns must contain a
projection whose owning record Agda identifies as coinductive. This permits a
dedicated, fully applied source-owner proposal without claiming inductive descent
or productivity. Ordinary premises still exclude the owner, explicit exclusions
still apply, and recursive operands cannot recursively expand that owner.
Original and generated projection clauses use this same path. Dependent fields
are checked sequentially, with the prior assignments in the branch; function
fields use ordinary lambda/application search. All complete recursive proposals
still undergo the non-forced assignment and owner/helper-group termination check.
No option such as `--guardedness` is enabled by the engine.

`copattern_proposals` counts this subset of `recursive_proposals`; it is not
an additional work charge or proof credit. Finite projected observations use
the shared application lane. Construction composes `apply-clause` result
splitting with `solve-evidence` on its resulting obligations. Autonomous clause
scheduling and full source export are not implied. This is neither general
coinductive completeness nor permission to case-split a coinductive record.

Evidence-policy traces additionally contain `structural_classification`, using
the existing `agdaprover.structural-classification.v2` object. The pure core owns
its eleven boolean-or-null fields independently of NNUE. The adapter derives
native constructor availability, local-function/result-head matches and direct
or higher-order descent facts in a read-only transaction. Head comparison uses
Agda reduction and binder identities; blocked heads remain unknown. A matching
head is an ordering observation, never a type equality or acceptance claim.

Availability describes this evidence-search inventory: lambda/record/datatype
construction, not future clause scheduling. Absence of such construction is not
uninhabitability. A local function with the matching result head is a promising
elimination candidate, not a certified solvable application. Competition is
derived only when both input facts are known. Dependency, permutation and
relational observations that this slice cannot establish stay null.

The same classification feeds symbolic continuation order and the existing
NNUE feature encoder. Both application and construction continuations remain
available after failure; scores and unknown facts never remove them. The
additive `classification_queries` counter is a subset of `inference_queries`
and charges each composite native metadata query once. It is not an extra
charge in the work-unit sum. Work survives rejected/cancelled classification.

`focused-implication-v1` adds in-memory logical proposals over native-observed,
meta-free types. Visible, nondependent ordinary arrows are recognized by Agda's
Pi structure and free-variable information; other binders retain general search.
Atoms have local native type identities, not pretty-printed names. The adapter
may identify a genuinely constructor-free datatype for empty elimination.
It never treats focused failure as an impossibility certificate.

The pure focused core keeps AND argument products, OR alternatives, positive
memoized witnesses and active-cycle detection. A whole right-introduction
telescope is one invertible phase. No failed, depth-censored or rejected
continuation is cached as logical failure. Only completed drafts invoke Agda;
rejection resumes alternatives and then general evidence search. H7/H8 still
own joint agenda resumption and full source/PV integration.

Focused choices use the existing focused model role and feature family. Traces
are provisional, including when a memoized witness reuses earlier choices.
They do not receive labels for censored or unvisited branches.

Search costs now use `agdaprover.symbolic-evidence-cost.v2`: `focused_actions`
counts in-memory nodes/rules/cache uses in addition to kernel work.
`focused_observation_queries` is a subset of `inference_queries`.
`focused_nodes`, `focused_cache_hits`, `focused_cycles`, and
`focused_candidates` expose the pure search's behavior. All charges survive
kernel rollback and cancellation. Focused work is not reported as checker calls.
The application rejects unknown cost-schema versions rather than silently
interpreting the former query-only work equation.

Expression displays have column-zero relative Agda layout. The native
application path preserves and anchors this layout in a parenthesized
expression; it does not flatten typed let blocks through the legacy formatter.
Fresh ordinary Agda validation remains mandatory after reconstruction.

## Typed algebraic proposals

`typed-algebra-v1` recognizes the current binary commutativity/associativity
fragment from scoped native types, including Agda's exposure of nondependent
binders. Relation and operation heads retain native identity and spines.
Polymorphic parameters are proposal-compatible until Agda checks their actual
application; a shape match is not a proof or a replacement unifier.

Symmetry, transitivity and congruence are supplied evidence too, not properties
silently assumed of an arbitrary binary relation. Concrete edges, rewrites
inside the binary operation, and common outer application contexts produce
explicit native proof expressions. The latter are reified native lambdas with
Agda-owned raising, not string substitution. Meta-blocked or unsupported shapes
retain general evidence search. No datatype, theorem, library or operator name
selects this path.

Distinct witnesses and composed paths with identical endpoints survive caller
rejection. No endpoint-only visited set erases proof-relevant alternatives.
Traversal and composition are charged to `algebra_actions`; their enclosing
depth widens under the existing resource controller. `algebra_candidates`
counts constructed candidates, not accepted proofs, and
`algebra_observation_queries` is a subset of `inference_queries`. These are
additive fields in the evidence cost v2. The session's `symbolic_actions`
combines focused and algebraic actions while `checking_attempts` retains only
native queries/checks. Agenda work allowances include both. Every returned
proof still passes original-parent reconstruction and independent validation.

The process accepts checking pragmas after `--`, parsed by Agda's own option
parser. The application passes its resolved command options explicitly. Library
manifest routing and full editor workflow parity await H8.

## Targeted acceptance

Use tiny successful, rejected, partial and blocked candidates; parent–child–parent
and sibling observations; same-process foreign/expired keys; snapshot eviction
and rechecked replay; root/import edits; cancellation and request-start receipts.
Run only a small seeded sample now. The 10,000-action sample, soak, whole-search
qualification and default promotion remain H10/H11 work.
