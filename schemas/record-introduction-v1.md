# Optional structural record introduction

`AGDAPROVER_STRUCTURAL_RECORD_INTRO=1` enables a narrow Agda 2.8 capability
with an explicitly configured `AGDAPROVER_AGDA_BRIDGE`. It is off by default,
independent of live retrieval, captured at project open and recorded in the
capability manifest with the native executable hash. A missing adapter is an
explicit unsupported-capability error; it is never built or enabled implicitly.

Agda's ordinary introduction tactic can choose a record's named constructor
even when an importing module exposes only a type alias. Neither the displayed
qualified constructor nor the displayed record type need be nameable there.
The optional observation obtains the actual focused goal type from Agda,
weak-head reduces it in its original context, and asks for that record's fields.
It renders `record { field = ? ; ... }` through Agda's concrete syntax.
It does not scan imported source or add unnameable declarations to retrieval.

All fields, including hidden and instance fields, are retained in declaration
order as explicit obligations. Field types, substitutions, modalities and
coverage remain Agda's responsibility when the literal is refined. A record
with no fields yields `record {}`. A non-record or stuck/opaque type yields no
proposal; no abstract boundary is bypassed to obtain one.

## Observation contract

The marker `agdaprover:record-introduction:v1:` is followed by a closed JSON
request containing only positive integer `output_bytes`. It is carried by the
existing interaction-specific module-contents command. The native bridge checks
the loaded filename and enters the interaction closure under `dontAssignMetas`
and `localStateCommandM`; both successful and failed observations restore state.
The Python gateway validates the exact parent token and open interaction first.

One response is required, with exactly these fields:

```json
{
  "kind": "AgdaProverRecordIntroduction",
  "schema_version": "agdaprover.record-introduction.v1",
  "interaction_id": 0,
  "output_bytes": 4096,
  "status": "record",
  "expression": "record { contents = ? }",
  "required_bytes": null
}
```

`not-record` requires a null expression and null `required_bytes`.
`output-limited` requires a null expression and integer `required_bytes` greater
than the caller's reservation; it becomes resource exhaustion, never an empty
catalogue or logical rejection. Unknown fields/versions, duplicate responses,
Boolean integer fields and mismatched interaction/reservation values fail closed.
Transport and aggregate CPU, memory, I/O, wall-time and cancellation controls
remain unchanged. The observation and subsequent refinement each consume a
physical verifier request in the existing ledger; no allowance is reset.

## Integration and trust

The compatibility gateway consults this observation only after an empty
introduction fails with `agda-not-in-scope`. It submits the resulting literal
through ordinary checked refinement from the same immutable parent. The shared
constructor search consumes the accepted preview and generated obligations
without knowing library, record, field or constructor names. The accepted
literal, not the failed named constructor, is retained in the replay lineage.

An observation never certifies a proof. Failed refinement retains ordinary
failure/fallback behavior; hidden obligations still prevent completion and
reconstructed solutions still require independent fresh Agda validation.
No statement, import, parameter or source scope is changed. Existing named
introductions and disabled-option behavior are unchanged. This is not an
incremental checking/checkpoint implementation or a retrieval-default promotion.
