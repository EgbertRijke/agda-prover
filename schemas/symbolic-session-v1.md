# Resident symbolic session v1

H2 provides single-owner checking, retained branches, explicit eviction/replay,
source invalidation, and cumulative work. H4 adds the coarse `solve-evidence`
operation; H5.2 adds Agda-native clause proposals. None grants proof verification
authority or edits user files.

## Invariants

- One owner serializes access to its Agda states. Each key binds to a fresh
  session nonce, epoch, and issued branch; a context additionally binds to a
  live interaction in that branch. Wire keys are validated, not trusted.
- The owner uses Agda's library-level operations directly. It has no separate
  editor `CommandState`; Agda's interaction/meta store is part of the saved
  `TCState`. The existing JSON bridge remains unchanged.
- Each candidate starts from the requested full state. Failure, interruption,
  observation, and success all leave the parent available and unchanged.
  A successful proof transition publishes a different child key. Checked native evidence belongs to
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
| `give` | `state`, `goal_id`, `expression` | Child state, native evidence view, obligations |
| `make-clause` | `state`, `goal_id`, `action` | Parent-bound native clause proposal, not a child state |
| `solve-evidence` | `state`, `goal_id`, `limits`, `ranker`, `model_path`, `native_path`, `exclude_names` | Search status, provisional child/evidence, cumulative search cost, selected policy choices |
| `evict` | `state` | Drop child snapshot; preserve replay ancestry |
| `replay` | `state` | Rechecked state key (resident states are returned unchanged) |
| `cost` | none | Current cumulative native-operation counters |
| `cancel` | none | Cancel the active request, or report idle |
| `close` | none | Cancel any active request, then close the session |

Goal IDs must fit Agda's nonnegative machine-sized interaction identifier.
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

An operation's rejection distinguishes foreign session, stale epoch/inputs,
unknown/evicted state, unknown goal, kernel rejection/blocking, cancellation,
and internal failure. Only successful transitions issue a usable new state.
Agda warnings about unresolved goals/metas/constraints remain obligations;
new non-meta warnings, including termination failures, reject the transition.

`accepted-partial` means there are still interaction goals. `accepted-blocked`
means no interaction goals remain, but hidden metas or constraints do.
`apparently-closed` requires all three to be empty. None means `verified`.

## Resource and ownership boundaries

The native ledger counts entered owner requests, checking attempts, accepted and
rejected checks, clause queries, replayed actions, cancellations, input bytes read,
and elapsed monotonic nanoseconds/process CPU picoseconds during owner operations. It is
not an OS-wide resource budget and excludes initial Agda loading and transport
work; an external supervisor must account for the entire worker process.
Every work dispatch has its own monotone receipt count, including requests
rejected before entering the owner. A killed worker cannot provide its final
counts: retain the last snapshot and receipt and mark final work unknown.

Input frames default to 16 MiB. `AGDAPROVER_SYMBOLIC_FRAME_BYTES` changes this
transport envelope. Oversized/unterminated frames close the connection; no
unbounded work queue is created. Native snapshot/trail residency is caller-
managed through eviction and process budgets for now. This envelope does not
impose a mathematical proof-size or search-depth limit.

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

Success returns `parent`, `goal_id`, and `proposal`; it does **not** issue a child
key. The proposal schema is `agdaprover.symbolic-clauses.v1`, with
`status: "proposed"`, echoed `action`, `variant` (`Function` or `ExtendedLambda`), a
structured `function` identity with a presentation `display`, `clause_count`,
and Agda-rendered `clauses`. `source_range` and `goal_range` are zero-based,
half-open character offsets from Agda's original abstract clause and interaction
point. They are observational ranges, not authorization to replace source.
`applied` and `proof_authority` are both false.

Internally the opaque, parent-branded proposal retains Agda abstract clauses,
case context, and the generation checking state. Rendering is only a view;
future clause execution must use the native structure with a validated parent,
not reconstitute semantics from that display. A wire response does not persist
an executable proposal handle. Generation leaves the parent unchanged, including
on failure/cancellation, and charges `checking_attempts` and `clause_queries`.
It does not charge `accepted_checks` or count the generated holes as accepted
subgoals. Replay an evicted parent first and regenerate against its new key.

This operation is the clause primitive, not autonomous clause search. Executing
generated clauses, integrating them into search, reconstructing authorized
patches, and freshly validating them remain separate responsibilities.

## Evidence operation

`limits` is exactly `{"work_units": positive-integer-or-null}`. It bounds
inference/checking queries, not proof size or depth. Null leaves the run under
external CPU/memory/I/O and cancellation supervision; depth widens. `ranker` is
`nnue` or `symbolic`. `model_path` is an OR-decision APNNUE artifact path or null;
`native_path` optionally selects the existing ABI3 scoring library. Null model
uses symbolic order and is reported as unavailable, not as learned inference.
The application normally supplies the pinned bundled OR artifact. The response
includes its loaded hash, checked against the application's pinned model.

`exclude_names` lists visible global aliases to exclude after Agda resolution.
The current mutual group is excluded automatically: recursion remains a later
structural action. Excluding a record constructor also excludes construction by
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

Expression displays have column-zero relative Agda layout. The native
application path preserves and anchors this layout in a parenthesized
expression; it does not flatten typed let blocks through the legacy formatter.
Fresh ordinary Agda validation remains mandatory after reconstruction.

The process accepts checking pragmas after `--`, parsed by Agda's own option
parser. The application passes its resolved command options explicitly. Library
manifest routing and full editor workflow parity await H8.

## Targeted acceptance

Use tiny successful, rejected, partial and blocked candidates; parent–child–parent
and sibling observations; same-process foreign/expired keys; snapshot eviction
and rechecked replay; root/import edits; cancellation and request-start receipts.
Run only a small seeded sample now. The 10,000-action sample, soak, whole-search
qualification and default promotion remain H10/H11 work.
