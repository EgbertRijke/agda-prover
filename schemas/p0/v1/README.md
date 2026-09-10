# P0 result schemas

These Draft 2020-12 schemas describe the closed JSON envelopes emitted by the
proof and one-step commands. `python -m agdaprover.schema_validation` is the
dependency-free standalone validator and additionally enforces terminal-status
invariants such as fresh validation evidence for `verified`.

Optional OR-policy traces can carry
[validated proof-choice credit](../../proof-choice-credit-v1.md), bound to the
final result rather than to merely accepted speculative actions.

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

## Optional physical verifier budget

An explicitly capped task adds `verifier_budget`, using
[verifier-budget.schema.json](verifier-budget.schema.json), with schema identity
`agdaprover.verifier-budget.v1`. Historical uncapped envelopes omit this field;
their task identities, cost records and legacy `verifier_calls` unit are unchanged.
Readers must not substitute that legacy aggregate for this quota's `used` value.

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

`used = interaction_commands + fresh_validations <= limit`. `denied_calls`
counts refused dispatch attempts, not verifier work. Consuming the last credit
is allowed; only a subsequent attempted request is denied. A denied run reports
`resource-exhausted`, never `unsolved`, `verified` or `impossible`. The standalone
validator enforces the sum, ceiling and terminal status beyond JSON Schema's
structural checks.

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
