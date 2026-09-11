# Policy trace retention v1

The shared OR recorder retains complete `agdaprover.policy-decision.v1` batches
under a caller-configurable `max_bytes` allowance (16 MiB by default). There is
no default candidate-count or decision-count cutoff. An optional positive
`max_decisions` remains available for callers requesting an additional limit.
This changes diagnostic retention, not candidates, ranking or proof acceptance.

## Accounting

Admission charges the compact, sorted-key UTF-8 JSON size of the complete initial
decision, plus space for every candidate's longest supported outcome annotation.
Exploration changes `false` to the shorter `true`; both orders, scores, goal,
candidate payloads and provenance are included. Inputs are snapshotted so later
caller mutation cannot change an admitted record. An oversized batch is omitted
whole; it is never truncated or split into artificial choice sets. A later
smaller batch may still fit. Singleton batches remain non-decisions.

Fresh proof credit requires the existing complete lineage validation. Additional
provenance bytes are charged before publishing any of that proof's new credit.
If the complete annotation cannot fit, none of its credit is published and the
omission is counted; search's checked result remains usable. Captured-byte
accounting is monotone and conservative, not a measurement of Python RSS or an
exact bound on an indented result envelope. Host memory/output limits continue
to apply. Callers may request a larger allowance without changing a schema.

`ORPolicyRouter.metrics().trace_retention` records
`schema_version: agdaprover.policy-trace-retention.v1`, `max_bytes`,
`max_decisions`, `charged_bytes`, and `proof_credits_omitted`. Existing retained
and omitted decision counters remain available. These metrics do not grant
training permission or replace source-bound fresh Agda validation.

## Compatibility

Candidate and decision v1 fields, identities, full order permutations and
censoring meanings are unchanged. Existing training readers already accept
complete larger batches. Historical records remain immutable; their older
producer's retention policy must not be inferred from new metrics. Unknown
candidate/decision versions continue to be rejected. Old absent/omitted choices
cannot be recovered by relabeling old receipts; new execution is required.
