# Validated proof-choice credit

This extends the optional `agdaprover.policy-decision.v1` diagnostic trace.
It does not change proof acceptance, search order or candidate membership.
The trace is exposed by `ProverResult.to_dict(include_attempts=True)`; ordinary
result envelopes need not include it.

## Selection and authority

Each retained OR decision has an exact `decision_id`, and each candidate has a
content-bound `candidate_id`. Proposed proof trees carry pairs of those IDs.
Search snapshots them before descending into child searches; a child's newer
decision cannot receive its parent's outcome. Batched case search carries only
choices whose edits entered the proposed source branch, including choices from
structural subproofs. Lookahead alternatives and abandoned trees do not qualify.

The single-goal `prove` entry point marks `on-validated-proof` only after the
selected reconstruction passes fresh validation and the final resource checks
still permit `verified`. It checks the complete selection before assigning any
positive: every choice must have been explored, must not have been rejected or
unsafe, and must not conflict with another arm of the same decision. Failed
lineage emits a `training-trace` diagnostic, not a changed Agda proof result or
partial positive publication.

Coverage currently includes ordinary constructors, visible-premise refinement,
whole-function reuse, retrieved structure builders and batched case selections.
Not every search path carries credit yet. Joint source-queue choices and other
opaque proof-building paths remain unlabeled; their successful result is not
permission to mark all explored decisions positive. Singleton/omitted trace
batches do not acquire fabricated records.

Unvisited, unfinished and accepted-but-unused alternatives remain
`budget-censored`. An `invalid` label describes the particular attempted Agda
action in its recorded context, not the falsity of a theorem or a declaration.
In particular, timeout/resource exhaustion is not a logical negative.

## Evidence binding

A positively credited decision adds `provenance.validated_result`:

```text
schema_version: "agdaprover.validated-policy-proof.v1"
task_id: the accepted result's task ID
source_sha256: the accepted result's original source hash
patch_sha256: digest of its reconstructed patch
validation_sha256: digest of its fresh validation record
trust_report_sha256: digest of its trust report
```

Digests use SHA-256 over UTF-8 JSON with sorted keys, no ASCII escaping and
compact `,`/`:` separators. Validation must have `checked=true`,
`fresh_process=true`, `timed_out=false` and `exit_status=0`; patch and trust
report must be present. The trust report must also attest a fresh offline
check with integer `checker_exit_status=0`; boolean exit codes are rejected.
This record binds diagnostic credit to the actual
result. It is not an independent proof certificate: replay consumers must
retain the source/configuration, patch and validation/trust records as well.

This runtime mechanism grants no corpus licensing, retention or training
permission. Dataset preparation and training remain outside the product.
