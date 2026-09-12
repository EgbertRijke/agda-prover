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
| `apply-clause` | `state`, `goal_id`, `action` | Checked native helper/clause child, evidence view and dependent obligations |
| `reconstruct-goal` | `state`, `goal_id`, `descendant` | Assemble native drafts from a descendant, recheck from the original goal's parent, return a provisional checked transition |
| `infer-helper` | `state`, `goal_id`, `mode`, `application` | Parent-bound native helper signature, not a proof transition |
| `solve-helper` | `state`, `goal_id`, `mode`, `application`, `limits`, `ranker`, `model_path`, `native_path` | Finite native helper search with the ordinary provisional candidate/cost result |
| `solve-evidence` | `state`, `goal_id`, `limits`, `ranker`, `model_path`, `native_path`, `exclude_names`; optional `focused_model_path`, `focused_search` | Search status, provisional child/evidence, cumulative search cost, selected policy choices |
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

Execution first asks Agda whether the original action is admissible. It then
abstracts the goal's dependent context into a native local helper, using Agda's
telescope/type reification, and resolves the selected subjects by native name
identity. Agda generates the corresponding helper clauses. This preserves the
parent's global definitions rather than mutating an already checked declaration
or its compiled clauses. The final native helper is checked through non-forced
`give` from the unsplit parent. Nested splits can operate on its new goals.
Dependent field/branch obligations live in Agda's shared child state; they are
not independent text placeholders.

Hidden-binder exposure is not mistaken for elimination. Pattern hiding and
modality are retained, and module-, let-, lambda-bound or without-K-forbidden
subjects remain subject to the original `makeCase` rejection. Helper clauses may
cover more cases than an original clause filtered by surrounding clauses; they
must themselves pass Agda's coverage/checking. No original source is rewritten.

Speculative helper assignments/definitions/constraints are rolled back before
the final check. Native drafts reserve their retained name and interaction ID
allocation ranges during checking and replay. Generated holes receive distinct
IDs and scopes; references to absent speculative metas are rejected. Only an
accepted transition publishes a child. Each entered clause generation, context
recheck and scaffold check charges the cumulative checking ledger; the two
generations also charge `clause_queries`. Replay rechecks the retained draft,
without regenerating clauses or resetting work.

These are session primitives, not autonomous clause search or authorized source
patches. Full proof-plan reconstruction belongs to H8: in particular, display
text can mention a hidden parent binder that must first be exposed in source.
Do not paste it blindly or interpret a closed native branch as `verified`.
Independent fresh checking remains mandatory. Autonomous clause selection and
full workflow integration are separate migration tasks.

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
Source drift invalidates the epoch. General source patches, binder exposure,
joint reconstruction and independent fresh validation remain separate duties.

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
`focused_model_path` optionally supplies the role-checked focused APNNUE, with
its hash returned separately as `focused_model_id`. Missing or null means that
family retains symbolic order, not that the OR model substitutes for it. The
application normally supplies both bundled artifacts. `focused_search` is an
optional boolean, default true; false provides a local ablation without changing
other evidence search. Null is not a boolean and is rejected.

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

Search cost adds `recursive_context_queries`, `recursive_proposals` and
`recursive_validation_queries`. The last counts whole candidate admissibility
queries (non-forced assignment plus source-owner termination) and is a subset
of `checker_queries`, not extra proof authority. `work_units` equals
`inference_queries + checker_queries + recursive_context_queries + focused_actions`; native
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

The process accepts checking pragmas after `--`, parsed by Agda's own option
parser. The application passes its resolved command options explicitly. Library
manifest routing and full editor workflow parity await H8.

## Targeted acceptance

Use tiny successful, rejected, partial and blocked candidates; parent–child–parent
and sibling observations; same-process foreign/expired keys; snapshot eviction
and rechecked replay; root/import edits; cancellation and request-start receipts.
Run only a small seeded sample now. The 10,000-action sample, soak, whole-search
qualification and default promotion remain H10/H11 work.
