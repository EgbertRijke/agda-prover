# Independent entry testing

`editor-api` accepts `operation: "test-entries"` in
`agdaprover.editor.request.v1`. The normal source path, SHA-256, request ID,
project configuration, models, and search settings apply. Supply
`goal_position: 1`; position does not select an entry for this operation.
Allowances are per entry, not shared across the whole file.

## Semantics and authority

Agda's parser and declaration grouping enumerate function implementations
in physical source order, including methods and entries in nested modules.
Datatypes, records, imports, signatures, fields, and postulates are context,
not bodies to erase. Anonymous `where` helpers belong to their enclosing
implementation, rather than separate tests. Unsupported implementation forms
stop the run explicitly.

Every attempt starts from the saved original snapshot. Only the selected
implementation is replaced, including all its clauses. Agda's native prefix
boundary selects its checking unit; the private view ends at that unit.
Original preceding declarations and imports are retained without substitution
or omission. Mutual/record groups stay whole. Later clients are not checked
against a proposed replacement: this is independent inhabitation testing,
not whole-file replacement compatibility. Unavailable or unsafe prefix
boundaries stop the run explicitly.

The application controller writes exclusively to its private temporary workspace and calls
the ordinary single-goal prover with the virtual hole's position. Earlier
generated completions never become subsequent tests' premises. Other existing
holes are not selected. Changed source invalidates the run. Temporary files
and child processes are cleaned up on completion, failure, or cancellation.

Only `verified` results with `validation.fresh_process == true` and
`validation.checked == true` produce solutions. This proves inhabitation
of the declared type in the preserved context, not equivalence to the original
implementation. Results are reports, not patches for the original source;
clients must not feed them to normal proof-application handlers.

## Streaming protocol

This operation emits newline-delimited JSON, flushing each progress object.
Other `editor-api` operations retain their single terminal response.
Every progress envelope uses `agdaprover.editor.event.v1` and contains:

| Field | Meaning |
| --- | --- |
| `request_id`, `operation` | Request identity; operation is `test-entries` |
| `source_file`, `source_sha256` | Original snapshot identity |
| `event` | `started`, `entry-started`, or `entry-result` |
| `payload` | Event-specific data below |

`started` carries `total`. Each `entry-started` carries `index` (one-based),
`name`, and `line` (one-based original physical line). Its `entry-result`
repeats these fields and carries `status`, `solution` (text or null), and
`diagnostic`. Prover attempts additionally carry `elapsed_ms`, `cost`, and
`validation`, and `validation_scope: "entry-prefix"`. The validator's own
scope refers to the private checking view, not the original complete file.
Unsupported entries carry `status: "unsupported"` and do not
invoke the prover.

After each verified entry, the next starts. Any unsuccessful result stops
the sequence. A failure during preparation or cancellation can terminate
without an `entry-result`. Already published successes remain in the report.
Malformed, stale, or superseded streams must not be treated as success.

The final object is the existing `agdaprover.editor.response.v1` envelope.
Its `result` uses `agdaprover.entry-tests.v1` and contains `status`
(`completed`, `stopped`, or `cancelled`), `total`, `attempted`, `solved`,
`failed_entry` (entry identity or null), and `diagnostic`. Exit codes are
0 for completed, 2 for stopped, and 130 for cancelled. Invalid editor
requests retain the ordinary editor error response. A file with no testable
entries completes with zero counts.

## Source boundary contract

The version-specific native parser's `--entries FILE` response uses
`agdaprover.source-entries.v1`: `parser_version`, `source_characters`,
`parse_warning_count`, and `entries`. Each entry has `name`, `parts`
(ordered nonoverlapping zero-based half-open character ranges for its
clauses), and `reason` (empty when eligible). The bridge strictly validates
the schema, toolchain version, snapshot, and ranges. The pure presentation
layer constructs the virtual edit; it cannot start a prover or access disk.
