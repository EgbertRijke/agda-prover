# Native implication-refutation certificates v1

The opt-in native controller implements the existing
`pure-implication-over-abstract-types-v1` negative fragment. This is not a
general impossibility decision procedure. Search failure, a censored witness
search, and a classical formula with no counterexample are not certificates.

## Native source boundary

`propose-refutation` is a read-only session operation with exact additional
fields `state`, `goal_id`, `work_units`. The allowance is a positive integer or
null; null leaves physical resource supervision and cancellation in force.
Only the original branch-zero source state is eligible. Usual session, epoch,
goal, source/configuration and cancellation checks apply.

The Agda adapter requires a whole declaration RHS hole with no applied LHS
patterns, local lambda/where body, with-function or extended lambda. Fixed
module parameters are not generalized. It reads the actual complete declaration
type, not the type of a failed descendant. The supported type has leading
ordinary hidden `Set₀` parameters followed by nondependent, ordinary visible
arrows over those parameters. Native universe identity is used; renamings and
definitionally equal presentations do not require spelling rules. Concrete
types, higher/dependent universe parameters, instances, unsupported modalities,
dependent families and unresolved types decline this fragment.

Agda must additionally equate the reconstructed canonical **native type** with
the actual source declaration type, in relevant context and with no postponed
constraints. Classification alone does not authorize changing the statement.
Names become canonical `a0`, `a1`, etc. only for the standalone certificate.
The user’s file and branch are never changed.

## Provisional response

`agdaprover.symbolic-refutation-proposal.v1` includes:

- `parent`: exact original state key; `goal_id`: original interaction identifier.
- `fragment`: the identifier above; `proof_authority`: always false.
- `status`: `not-applicable`, `no-counterexample`, `censored`, or
  `refutation-candidate`.
- `assignments_checked`: valuations actually tested during this invocation.

A candidate additionally includes `owner`, `original_type_display` (audit only),
`canonical_type`, `parameter_count`, `formula`, `valuation`, `recipe`,
`module_filename: "AgdaProverRefutation.agda"`, and `module_source`.

Formula nodes have exactly `{tag: atom, id}` or
`{tag: arrow, domain, codomain}`. Atom IDs refer to the zero-based ordered type
parameters. The valuation is a list of distinct `{atom, value}` entries covering
exactly the formula’s atoms, with Boolean values. Unused type parameters are
specialized to the newly defined empty type without enlarging the valuation.

Closed type nodes are `{tag: empty}`, `{tag: unit}`, or the same binary `arrow`
shape. Recipe nodes have exactly these fields:

| Tag | Other fields | Meaning |
| --- | --- | --- |
| `variable` | `index` | Scoped de Bruijn variable |
| `unit` | none | Constructor of the certificate’s new unit type |
| `lambda` | `domain`, `body` | Typed binding with a closed domain type |
| `apply` | `function`, `argument` | Application |
| `absurd` | `result`, `subject` | Eliminate the certificate’s empty type |

The initial recipe context has one value: the hypothetical complete declaration
instantiated at the valuation’s empty/unit types. These are newly declared
certificate types, not recognized names or assumptions from the user’s file.

## Scheduling and costs

For one selected original source goal, the native agenda gives refutation a
small side slice using `initial_macro_work`, then continues ordinary proof
search. Censored slices double their next allowance. Repeated classification
and valuation work is charged again; this version does not retain an internal
enumeration cursor. There is no fixed atom, assignment, proof-depth or wall cap.
The side task and proof search share the run’s total work/physical envelope.

`advance-search` can return `refutation-candidate` with a `refutation` field and
a retained run revision. Rejection resumes that same ordinary frontier;
acceptance closes it. Multi-goal selections do not infer joint impossibility
from one branch. Direct `solve-evidence` remains a proof-only compatibility API.

The session ledger adds `refutation_queries`, `refutation_assignments`, and
`refutation_candidates`. Queries are included in `checking_attempts`;
assignments in `symbolic_actions`. These are not NNUE scores or ordinary tree
move counts. Rollback, censorship, rejected certificates and cancellation never
refund work. Fresh validation consumes the shared physical verifier allowance.

## Fresh acceptance and replay

The application first validates the recipe’s version, node fields, indices,
valuation coverage and canonical type, independently reproducing the exact
module bytes. This is certificate replay, not Python witness discovery/search.
Replay is iterative and keeps linked scopes so native depth does not acquire a
Python recursion cutoff. A changed statement, substituted goal, injected syntax,
or unbound recipe variable cannot pass this boundary.

The ordinary fresh validator then checks the standalone module under `--safe
--without-K`. It contains only new empty/unit datatypes, empty elimination, and
`refute : (canonical declaration type) → APEmpty`. It imports no library proof
and adds no axiom. The source/input pins are checked again after validation.
Neither native acceptance nor successful recipe replay substitutes for this
independent Agda check.

Only successful fresh validation produces public status `impossible` with
`agdaprover.native-impossibility.v1`. Its method is
`agda-checked-implication-refutation`; it contains the proposal, original source
hash, task identity, native executable hash, generated-module hash, Agda binary
hash/version and checker-output hash. The result also retains the ordinary
validation and trust reports. Its proof term and patch remain null: the
certificate is a refutation of the complete closed type, not a completion to
insert into the goal. It is not a claim that an arbitrary ambient project is
consistent or that every unsupported goal is impossible.

The older Python `agdaprover.impossibility.p0.v2` format is unchanged. Versions
are not interchangeable. Persisted native certificates can replay their recipe
with `application.native_refutation.replay_source`; re-establishing their source
binding requires the pinned original project/native observation and fresh
checking, not trusting a deserialized `parent` key from a previous session.
