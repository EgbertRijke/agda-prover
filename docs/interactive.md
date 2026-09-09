# Interactive search

Start a joint search with:

```sh
agda-prover interactive MyFile.agda
```

Add `--goal N` to stop at a particular goal. The command accepts one JSON
message per line and returns JSON events. After the `started` event, enter:

```json
{"schema_version":"agdaprover.interactive.command.v1","request_id":"1","command":"principal-variation"}
{"schema_version":"agdaprover.interactive.command.v1","request_id":"2","command":"pause"}
{"schema_version":"agdaprover.interactive.command.v1","request_id":"3","command":"resume"}
{"schema_version":"agdaprover.interactive.command.v1","request_id":"4","command":"status"}
{"schema_version":"agdaprover.interactive.command.v1","request_id":"5","command":"stop"}
```

A principal variation is the current proposed sequence of proof steps, not a
completed proof. Its response lists any available `acceptance_options`. To
accept an individual completed goal, send `accept-goal` with an option's
`goal_id` and the current `variation_id`:

```json
{"schema_version":"agdaprover.interactive.command.v1","request_id":"6","command":"accept-goal","goal_id":0,"variation_id":"COPY_CURRENT_VARIATION_ID_HERE"}
```

Acceptance fresh-validates that declaration and stops the joint run only after
validation succeeds. The returned edit does not solve the remaining goals or
modify your file automatically. Closing standard input stops an unfinished run.
Ordinary search has no implicit wall-time deadline; explicit resource limits
and finite search allowances still apply.
