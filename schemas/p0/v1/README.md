# P0 result schemas

These Draft 2020-12 schemas describe the closed JSON envelopes emitted by the
proof and one-step commands. `python -m agdaprover.schema_validation` is the
dependency-free standalone validator and additionally enforces terminal-status
invariants such as fresh validation evidence for `verified`.

Optional OR-policy traces can carry
[validated proof-choice credit](../../proof-choice-credit-v1.md), bound to the
final result rather than to merely accepted speculative actions.

Nested case and constructor searches publish their completed-work statistics
once on every exit, including resource and protocol exceptions. Single-goal and
joint controllers retain these counters before polling the remaining budget;
interruption must not erase already performed model, action or checker work.
The optional `on_statistics` callbacks are aggregation-only: they cannot perform
budgeted work or grant proof credit. Counter fields retain their existing units
and schema; historical reports with missing child work are not rewritten.

Introduction reconstruction follows the checked kernel preview, not a guess
from the goal's printed arrows. Agda can introduce an implicitly quantified
function with a constructor expression, inserting the hidden abstraction during
elaboration. Only explicit lambda binders are eligible for clause hoisting;
other previews stay parenthesized at the selected hole, preserving siblings and
remaining obligations. Joint, guided and one-step reconstruction share this
behavior. Such a preview is not an invalid task. Partial reload success is not
proof acceptance; completed source still requires fresh strict validation.

Joint search treats fast implicational inhabitants as proposals, not as proof
authority. It retains a bounded, source-local structural continuation and resumes
it only after the ordinary frontier is exhausted. Rejected elaborations, failed
descendants and fresh-validation rejection cannot silently remove that fallback.
The continuation skips the same approximate search once; changed goals start
normally. Its exact search identity includes that distinction. Pending work shares
the frontier/resource bounds and appears in principal-variation frontier counts.
`focused_fallbacks_deferred` and `focused_fallbacks_resumed` count the continuations;
no extra checker calls or resumed work occur on a successful fast path.

With exact live-scope retrieval enabled, constructor search tries supplied values
before structural builders and evidence composition. A candidate may have ordinary
hidden parameters but no explicit or instance arguments; matching result heads
only propose a checked `give`. Agda determines indices and hidden parameters from
the goal. No new visibility, type-equality authority or proof credit is implied.
Rejection or rejection of an assembled provisional plan retains other search lanes.
The same checked-give implementation handles whole-function reuse, preserving its
existing telemetry. `AGDAPROVER_SCOPED_VALUE_REUSE=0` disables only the new value lane.

Bounded `agdaprover.retrieval-value-widening.v1` records carry scope/index/query
identities, width, new expressions and the shared cumulative query allowance.
`agdaprover.value-attempt.v1` records use `reuse-visible-value`, `agda-give`, the
original scoped declaration type, goal, acceptance and rejection code. The
existing visible-premise OR/NNUE candidates and proof-choice boundary are reused;
no model feature version changes. Actions, proof checks and physical dispatch
remain charged, and fresh validation remains independent.

## Copattern construction

Case search can request kernel-generated result projections through the optional
`ResultSplittingSession` interface. `AGDAPROVER_COPATTERN_SEARCH=0` disables this
lane; other construction and named-variable splitting remain available. Generated
prefix and postfix copattern clauses retain their enclosing scope and indentation.
Assignments are re-elaborated before searching later fields, whose types may
depend on earlier projections.

Within those generated clauses, `CopatternCallSpec` carries the owner and exact
clause-prefix provenance into shared constructor search. It is not a certificate
of coinductivity or productivity. The owner stays excluded from ordinary premise
retrieval; a checked refinement may expose dependent argument obligations, solved
by ordinary search. Recursive owner proposals are disabled while constructing
their own arguments. Supplied local functions can instantiate unknown argument
domains before lambda introduction, using the same checked reuse as other local
values. No type, field or benchmark name determines applicability.

Result projection does not remove the clause's local arguments. When named
arguments remain, the initial copattern-construction attempt uses the existing
finite construction slice, leaving argument-elimination proposals a turn. Their
admissibility is still decided by Agda, not by the presence of a name. If all
case proposals are rejected, construction may use the shared remaining allowance
with the same kernel-generated owner provenance. This fallback neither renews
resources nor exposes the owner as an ordinary premise. Subsequent argument
pattern changes do not manufacture new copattern provenance.

The existing `recursive-call` policy boundary carries `refine-copattern-owner`
candidates with `subject-origin=kernel-copattern-clause`; symbolic ordering remains
available. Bounded `agdaprover.copattern-call.v1` diagnostic rows in
`recursive_actions` record `tag`, `expression`, `inferred_type`, `clause_prefix`
and provisional `accepted`. They do not claim that the whole definition passes
coverage or productivity. Policy choices earn proof credit only after fresh
validation of the reconstructed result.

`result_split_queries` is a subset of `case_queries`, not an additional physical
cost. `copattern_clauses_generated` counts admitted generated clauses and
`copattern_search_enabled` records activation. Owner inference and checked
refinements use the existing recursive-inference/proof counters and shared budget.
Ordinary inductive records also admit result splitting: invalid recursion, missing
guardedness, unresolved fields and unauthorized option changes still cannot yield
`verified`. This initial lane does not cover every existing user copattern,
pattern-lambda/mutual definition, or change of argument patterns.

## Expected-type evidence reuse

Joint scheduling distinguishes a plausible structured builder from a supplied
first argument. Deferring dependency-guided case analysis requires agreement of
the complete observed first-domain type (ignoring whitespace and enclosing
parentheses), not merely its head. Unresolved indices or aliases may therefore
lose that preference; they do not lose any ordinary speculative builder
candidate. This is a conservative ordering hint, not type equality or proof
authority. It adds no checker request, feature version or resource allowance.

Shared constructor search checks ready applications before expanding a structured
goal. Supplied local values and authorized declarations feed the existing typed
evidence generator; only proposals with all explicit arguments supplied and a
matching result-head hint enter this closure lane. Agda checks each complete
expression against the actual goal, inferring hidden indices and propagating
assignments to dependent siblings. This works for both provisional and concrete
targets, independently of record/coinductive construction. A syntactic head match
is a proposal hint, never a type-equality judgment. Unknown inferred types are not
retained as intermediate evidence, and explicit-function specialization is not
added here.

`AGDAPROVER_EXPECTED_EVIDENCE=0` disables the lane. The existing
`evidence-application-v1` NNUE family ranks its alternatives with the distinct
`check-evidence-application` tag; inference proposals keep their original tag.
Scope filtering, symbolic fallback, exact-parent rejection and policy-choice
lineage remain shared. Checks spend the current action/premise budget and count
as `proof_checks` and `premise_queries`, not inference queries. Provisional success
does not cut off alternatives on generator resume or bypass fresh validation.

## Editor search profiles

Editor request v1 accepts an optional `search_profile`: `standard` (default)
or `deep`. This is a search-only option, not valid for `inspect`. Omitted
`max_candidates` resolves to 500 or 8,000 respectively; an explicitly supplied
positive integer always overrides the preset. Other fields retain their existing
meaning. The CLI exposes `--search-profile` and the `--deep` alias. Frontends
resolve the preset into the ordinary TaskSpec budget before search, so task
identity, worker forwarding and accounting use the effective numeric allowance.
No additional trusted path or unbounded resource mode is introduced.
Updated editors omit the profile field for standard searches, retaining
compatibility with older backends. Deep requests require a backend recognizing
the field; they must not silently fall back to the smaller allowance.

Tasks and editor requests may supply an explicit
[project checking configuration](../../project-configuration-v1.md). It carries
the Agda executable, registered libraries and global checking options through
search and validation, including relocated candidate projects.
For registered libraries, `trust_report.checking_environment` binds the
versioned library manifests, source ownership and explicit global options.
The standalone validator checks that witness against the actual isolated
checker command; it does not impose the default `--without-K --exact-split`
flags on libraries configured differently. Results without a library witness
retain the historical standalone-profile requirement. Schema acceptance is
not a replacement for Agda checking, policy enforcement or dataset admission.

## Physical verifier accounting and optional budget

Every initialized search invocation reports `verifier_budget`, using
[verifier-budget-v2.schema.json](verifier-budget-v2.schema.json), with schema
identity `agdaprover.verifier-budget.v2`. Its `limit` is `null` when uncapped;
measurement does not impose a quota. Readers also accept historical capped
[v1 reports](verifier-budget.schema.json) and historical envelopes without a
meter. Absence means unmeasured, not zero. Task identities and the legacy
`verifier_calls` unit are unchanged; never substitute that aggregate for `used`.
Consumers restricted to v1 must be updated before reading new reports. Existing
frozen results are not rewritten or retrospectively given missing measurements.

`max_verifier_calls` is an optional positive integer in `TaskSpec` and search
editor requests. Omission or `null` means no independent call cap. CLI search,
collection and interactive-worker entry points accept `--max-verifier-calls`.
Editor `inspect` rejects this search-only option rather than silently ignoring it.

One credit is reserved immediately before each physical Agda interaction write
or fresh checker launch. Loads, inspections, inference, speculative commands,
rollback/replay, Auto commands and supplemental validation sessions count; one
command returning multiple events is still one credit. Failed writes, checker
launch failures and rejected proofs consume their reserved credit. Commands
rejected locally before dispatch, cancelled before reservation, cached observations,
source/metadata reads, toolchain version probes and process startup handshakes do
not. Their other resource limits still apply. Validation has no free reserve.
The existing `fresh_validations` request unit also includes the independently
launched Agda prefix-syntax helper. This historical quota behavior is retained;
a parser request does not establish proof acceptance.

`used = interaction_commands + fresh_validations`, with `used <= limit` when
capped. `denied_calls`
counts refused dispatch attempts, not verifier work. Consuming the last credit
is allowed; only a subsequent attempted request is denied. A denied run reports
`resource-exhausted`, never `unsolved`, `verified` or `impossible`. The standalone
validator enforces the sum, ceiling and terminal status beyond JSON Schema's
structural checks.

`cost.fresh_validation_runs` counts actual fresh proof-checker process starts,
recorded at launch and retained on cancellation, timeout, resource exhaustion
and rejection. Failed launches and syntax-helper launches are not validation
runs; their reserved requests remain in the physical ledger. Policy/preflight
rejection before dispatch counts as neither. The invocation's final cost is
read from the shared meter, not inferred from successfully returned validation
summaries. This includes supplemental prefix checks exactly once. A nonzero
count is work evidence only: `verified` still requires completed fresh checking.
It can differ from `validation.fresh_validation_runs`, which describes the
returned validation attempt rather than all attempts made during search.

All sessions in one synchronous invocation share the scope. Explicitly nested
scopes charge enclosing quotas too; an uncapped child cannot reset its parent.
Copied Python contexts share atomic counters. New threads/processes do not
automatically inherit Python context: the present interactive worker receives
the configured cap explicitly and establishes its own run scope. A future
parallel scheduler must allocate/share quotas explicitly before claiming this
contract across workers. User-requested `accept-goal` is a separate independently
validated operation, not a joint-solver success or part of its search allowance.

Existing frozen Stage 2 reports retain their historical post-hoc counter contract.
Gate 3 must preregister budgets in these physical units for both prover and Auto;
their numerical limits cannot be compared directly with old aggregate limits.
