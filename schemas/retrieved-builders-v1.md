# Retrieved structured builders v1

`AGDAPROVER_SCOPED_BUILDERS=1` enables a separate progressive admission path
for the existing structured-builder generator. It requires contextual evidence
and an already available, exact-state live scoped retrieval pool. The option
is captured when search starts and is off by default.

Ordinary structural admission prefers small conclusions. That order remains
unchanged, but it no longer determines which retrieved builders this optional
path can try. The builder path visits the original ranked pool at widths
8/32/128/512. It applies the existing generic predicate and specialization:
a matching result head, a ready structured first argument and a later
function-valued argument. Agda determines all actual applicability, implicit
arguments, constraints and generated subgoals. No definition, constructor,
record or benchmark name is recognized specially.

Before an open function argument, this path also proposes a constant function
returning a visible non-function value with a matching codomain head. It keeps
the original open-argument proposal. Each such proposal fills one function
argument; it does not enumerate Cartesian products of all argument choices.
Grouped explicit binders retain their arity; hidden/instance function binders
retain ordinary search. Dependent codomains, relevance and actual argument
types are checked by Agda, not inferred from the shared printed head. Other
callers of the structured-builder generator keep the prior proposal set.

Within each newly exposed batch, unique application expressions enter the
existing `visible-premise` OR interface with tag
`specialize-structured-builder`. The symbolic fallback preserves retrieval
order; an available role-checked NNUE may reorder the same proposals. Metadata
retains original retrieval rank, structural admission rank and the existing
ranking features, and adds `builder-admission=retrieval-order-v1`. These
features describe proposals, not proof evidence.

Each application retains its exact decision and candidate IDs across child
search and parent backtracking. Exploration and rejection are recorded against
those IDs, not the latest decision for a possibly reused expression. Local
builders without an OR decision do not acquire another decision's labels.

Visible local builders retain priority. Duplicate applications are checked
once per invocation in the exact parent and interaction. Widening retains
observations and spends the existing action, premise, wall/CPU and physical
verifier allowances; it never starts a fresh task budget. Branch-local
subgoals use the existing constructor search. A rejection or exhausted local
slice leaves ordinary structural construction available if resources remain.
No result is reused across source revisions, scopes or parent substitutions.

`agdaprover.retrieval-builder-widening.v1` events carry the distinct search
policy `retrieved-structured-builders-v1`, exact scope/index/query identities,
width, new expressions and cumulative premise-query count.
`agdaprover.structured-builder-attempt.v1` records expression, goal target,
kernel acceptance/rejection code and generated-subgoal count. The existing
bounded retrieval and premise logs retain omitted counts. All kernel and model
work remains in the normal cost summaries.

Provisional refinement is not a closed proof: hidden metas and constraints
still pass the existing completion checks, and every `verified` result still
requires fresh policy-compliant Agda validation. This policy adds neither
axioms nor normalization rules. With the option disabled, the prior builder
ordering and accounting remain unchanged. It is not a C3 completion or a
default-promotion claim.
