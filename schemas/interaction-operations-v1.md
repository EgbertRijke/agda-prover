# Agda-owned interaction operations

The Agda 2.8 adapter advertises `make-clause`, `helper-signature`, and `goal-view`
in addition to the existing kernel operations. These are local observations,
not proof certificates or in-place source mutations. All commands share the
session's resource, cancellation, revision and replay boundaries.

## Clause actions

`ClauseAction` is the `agdaprover.clause-action.v1` intent:

```json
{"schema_version":"agdaprover.clause-action.v1","kind":"variables","subjects":["p","q"]}
```

| Kind | Subjects | Agda operation |
| --- | --- | --- |
| `variables` | Nonempty ordered list of individual names | `make_case "p q"` |
| `result` | Empty | `make_case ""` |
| `ellipsis` | Empty | `make_case "."` |

Unknown fields, versions and mixed intents are rejected. `make_clause` requires
an open interaction in the selected state. Agda owns name resolution, dependent
splitting, implicit/instance binder exposure, sequential processing of multiple
variables, trailing argument introduction, copatterns and ellipsis expansion.
Module, lambda and let parameters are not guessed to be eliminable.

Success returns Agda's clauses and variant without applying them. The response
must contain exactly one matching interaction identity. Reconstruction and a
reload are necessary before using the edited context. The legacy single-subject
and result-splitting methods delegate to this same boundary.

Search retains single-subject alternatives alongside a batch of hidden inputs.
Ellipsis clauses can be expanded before other structural actions. A source edit
that merely exposes an argument is not recorded as recursive descent.
`AGDAPROVER_CLAUSE_OPERATIONS=0` disables the new batch/ellipsis scheduling;
`AGDAPROVER_CONTEXT_BINDING=0` disables hidden-input proposals.

## Helper signatures

`helper_signature(state, interaction_id, application, budget, mode=...)` invokes
Agda's `Cmd_helper_function`. Its result is the signature of the proposed helper,
or `None` for an Agda rejection. Arguments can be variables or compound
expressions. Agda determines dependencies, implicit/instance parameters,
with-abstraction and specialization to the surrounding module. No declaration
is installed. A malformed, duplicate or wrong-goal response is a protocol error.

The search's finite helper fragment consumes this signature and proposes local
one-constructor eliminations returning arguments or fields. For an observed
two-edge connection it generalizes the common intermediate before constructing
a helper. This proposes a function; it does not assume transitivity of an
arbitrary relation. Constructor catalogues, inference, coverage checks and final
fresh validation remain authoritative. Unsupported helper shapes keep ordinary
search available. Constructor-choice NNUE ranking orders the actual candidates;
`AGDAPROVER_HELPER_SYNTHESIS=0` provides an ablation. This is not exhaustive
synthesis of every function Agda could type.

## Reduction views

`RewriteMode` has five distinct values: `as-is`, `instantiated`, `head-normal`,
`simplified`, and `normal`. They map exactly to Agda's `Rewrite` modes for goal
views, inference and helper signatures. Alternate views do not replace canonical
state tokens, cached goal contexts or source ranges.

Search uses weak-head views for telescope introduction and copattern-owner
signatures; helper synthesis first preserves the unreduced telescope and requests
full reduction if it cannot find a usable constructor. Relation comparison keeps
fully reduced observations. `AGDAPROVER_REDUCTION_VIEWS=0` restores the previous
always-normalized selection. All five modes remain available through the kernel
interface, irrespective of this scheduling switch.

Agda's *compute* modes are different. `normalize` supports `head-normal`, `normal`
and the existing explicit `ignore-abstract` diagnostic policy. Requesting `as-is`
or `simplified` computation returns `unsupported-capability`; neither is silently
misrepresented as weak-head evaluation. Use a rewrite view for those policies.

## Completion and conformance

Refinement, inference and successful expected-type checking can leave hidden
metavariables. Source-producing case search therefore checks apparently complete
candidates against the parent's residual-obligation counts, as structural tree
search already does. Increased counts or generated goals reject that completion
while preserving the parent and other alternatives. These local counts are not
a proof of closure: only fresh validation authorizes `verified`.

Residual counts use Agda's constraint and metavariable reports directly, rather
than requesting normalized contexts for every other open goal. The two-command
observation is checked against full inspection in conformance tests. Missing,
duplicate or malformed reports fail closed instead of becoming zero counts;
the parent remains replayable and all physical requests remain accounted for.

The conformance tests cover all rewrite modes, helper abstraction, sequential
multi-variable cases, implicit/instance exposure, ellipsis, illegal coordinates,
scope lookup, refinement and hidden obligations. Existing bridge and copattern
tests cover fresh/replayed states, record results, constraints, cancellation and
failure recovery. Malformed expression views must not become successful empty
inferences. All diagnostics and benchmark-specific material stay outside the
runtime package.
