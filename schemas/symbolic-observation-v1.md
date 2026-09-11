# Symbolic observation protocol v1

Experimental, read-only Haskell boundary. Not the future run/control protocol.
The entrypoint emits one JSON object on stdout, only after Agda has completed
the request. Diagnostics use stderr. No response authorizes a patch.

## Capabilities

`agdaprover.symbolic-capabilities.v1` identifies the package, engine and pinned
Agda/GHC versions; lists supported operations and observation modes; and reports
`search_available: false`, `proof_authority: false`. Unsupported commands are
rejected, not forwarded to a different engine.

## Goal observation

`agdaprover.symbolic-goal.v1` has:

- `status: observed`, the requested `goal_id` and target `mode`;
- `raw_target` and `target`: structural Agda types, not pretty-printed strings;
- `context_mode: raw`, `context`: dependent telescope, oldest binder first;
- `locals_newest_first`: native local IDs and de Bruijn indices;
- `let_bindings`: native IDs, domains, values and binding origins;
- `module`: native module-name parts, not a guessed textual namespace;
- `aliases`: Agda-resolved local/global/overloaded/pattern-synonym identities,
  or an explicit ambiguous/unknown resolution;
- `names`: native name IDs with all observed module/range/display views;
- `open_metas`, `constraint_count`: remaining obligations, not evidence of closure;
- `structural_nodes`: visits in this observation's encoding, not total checker work;
- `reconstruction`: local codec round-trip status, never proof validation;
- `proof_authority: false`.

Types are tagged `type` pairs of sort and term. Terms retain variable/global/
constructor/meta heads and complete `apply`, `proj`, or `iapply` spines; lambdas
and Pis retain `abs` versus `no-abs`. Sorts and levels remain structural. Argument
and domain annotations are preserved independently of display strings. Decimal
integer and floating bit-pattern encodings avoid JSON numeric precision loss.
The exact Agda syntax codec is version-pinned in the adapter, with malformed,
unknown, or unsupported structures rejected rather than guessed.

This is not a portable saved checking state. A native name/meta ID by itself
does not establish identity in another source, environment, session, or branch.
The future resident-state protocol must supply those ownership boundaries.

## Rejection

`agdaprover.symbolic-error.v1`, `status: observation-rejected`, and a `reason`
are returned for malformed requests, missing goals, checker failure, unsupported
structure, or ordinary I/O failure. Checker details remain on stderr. Process
cancellation/crash is handled by the supervising application, not converted into
successful observations. No unsolved/impossibility/verified proof claim is made.
