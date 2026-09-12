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

## Experimental Haskell search

The default engine remains Python while native search is being qualified.
To try a locally installed native symbolic executable:

```sh
agda-prover interactive MyFile.agda --engine haskell --symbolic-core /absolute/path/agdaprover-symbolic
agda-prover step MyFile.agda --engine haskell --symbolic-core /absolute/path/agdaprover-symbolic
```

The same selection works with `prove`, `prove-prefix` and `editor-api`.
`AGDAPROVER_ENGINE` and `AGDAPROVER_SYMBOLIC_CORE` supply launch defaults;
explicit command-line settings take precedence. `auto` currently selects
Python. An explicit native request never falls back after a failed search,
and no compiler or download is started to find the executable.

Native interactive search uses the same pause/resume/stop and accept-goal
messages above. Its between-slice previews are provisional and can change;
each offered goal still needs independent fresh validation when accepted.
Native `step` returns one checked transition, leaving any child goals open,
and fresh-loads its proposed source edit. It is not a theorem-completion claim.

Native search requires Agda 2.8.0. It uses the bundled focused/OR models for
proof search and the bundled one-step/OR models for `step`. `--model` accepts
a proof-term or focused-branch model for proof search, and a one-step model for
`step`; `--action-model` replaces the OR policy. Wrong model roles are rejected.
`--ranker symbolic` disables bundled ranking; an explicitly supplied
`--action-model` still enables that policy, just as for Python proof search.
Native actions outside a model's feature vocabulary retain symbolic ordering;
this is a distinction between action shapes, not libraries or filenames.

Native `--max-depth N` limits accepted transitions along a branch (zero allows
no transitions). Reaching it reports resource exhaustion, never impossibility.
Native and Python depth units differ: a compound native move is one transition,
but all its internal checking/search work is still charged to the physical and
work allowances. This is not a proof-term size bound. Time and depth remain
unset by default; `--deep` increases the action allowance as usual.
`--max-term-size` pertains to Python's small term enumerator, not native syntax
proposals; use native depth, action or physical limits to bound native work.

## Deep search

For larger files or harder goals:

```sh
agda-prover interactive MyFile.agda --deep
agda-prover prove-prefix MyFile.agda --deep --timeout 360
```

`--deep` is shorthand for `--search-profile deep`. It changes the default
whole-run action allowance from 500 to 8,000, giving joint search more room to
reconsider earlier definitions. It uses the same solver, candidate generators, optional
NNUE models and fresh validation. It is not a promise that every goal will solve.
Depth is already unbounded by default; this is a larger effort allowance, not
a different proof system. Memory and other resource defaults are unchanged.

Explicit `--max-candidates`, `--max-verifier-calls`, `--timeout`, `--cpu-seconds`
and other limits remain authoritative. For example, `--deep --max-candidates
12000` requests 12,000 actions. There is no automatic time or memory multiplier
based on file size. Interactive pause, status, principal variations and stop
work unchanged; EOF still stops an unfinished run.

In Emacs, use `C-c C-x C-d` (`agdaprover-prove-deep`). In VS Code, choose
**AgdaProver: Deep Search Through Current Goal or All Goals**, also bound to
`Ctrl+C Ctrl+X Ctrl+D`. Selection is unchanged: through the containing goal,
or every open goal when outside one. Both editors retain their cancel command.

To make deep search the usual preset, configure `agdaprover-search-profile` in
Emacs or `agdaprover.searchProfile` in VS Code. Leave `agdaprover-max-candidates`
at `nil`, or `agdaprover.maxCandidates` at `null`, to use preset defaults.
Existing explicit values (including a previously configured 500) still override
deep search; reset them if you want the preset's larger allowance.
