# Composed-evidence choices

`evidence-application-v1` is an OR decision family, separate from refining
with a bare visible declaration. Its action proposes one complete application
of a supplied or previously inferred function to supplied/inferred arguments in
the exact parent state and interaction. `infer-evidence-application` asks Agda
for its type; `check-evidence-application` checks it against the current expected
type. Both remain speculative and grant neither final proof acceptance nor a
positive training label.

Each decision offers all distinct currently generated, unattempted applications.
The symbolic order is `(depth, expression length, expression)` as before.
Duplicates retain the first proposal in that order. After each observation the
generator runs again: this is a new decision, not another arm of an old batch.
Singletons need no recorded choice or scoring. Trace-size limits omit the whole
decision, never truncate the candidate set used by search.

The existing candidate/decision v1 envelopes and `or-decision-v4` features remain
unchanged for existing families. This family's version identifies its additional
feature contract: the candidate type is the observed function type (not a guessed
application result); metadata records application depth, argument count, derived
function/argument counts and the function's explicit arity. No outcome, private
reference, benchmark name or inferred future type is a ranking feature.

Only a scoped APNNUE3 model explicitly declaring `evidence-application-v1` may
score this family. Legacy unscoped weights keep their original four-family
domain, not an implicit domain including future families. Unknown family versions
are rejected. Other scoped families retain their previous features and behavior.

The pure generator retains typed function/argument inputs. Search keeps their
exact choice dependencies in a parent/interaction-local ledger. A selected
application inherits only those dependencies, plus its own recorded choice.
Consumers attach that lineage to the proof they construct; relation composition
reports its actual seed and operator dependencies, not a text search of its output.
Unused observations and abandoned proofs remain censored. An inference rejection
is invalid; unresolved inferred metas or a resource interruption alone supply no
proof credit.
Fresh validation and the existing source/task/patch-bound proof-credit contract
are still required before any selected dependency becomes positive.

## Source-directed admission

With a live scoped retrieval pool, contextual evidence also considers supplied
consumers whose first explicit input contains the binder governing their result
type. This includes dependent projections without recognizing any record or
field name. Binder annotations may use arbitrary universe aliases. Infix
operands are not treated as result-family heads; these syntactic hints propose
applications and do not certify a projection law or definitional equality.

This view ranges over the already retrieved, authorized pool, not merely its
first direct-proof admission batch. Direct-proof ordering favors a matching
result head, whereas a dependent field's result becomes known only after
applying it to its source. The ordinary pool/order and initial candidates are
preserved. The shared generator requires supplied matching inputs and reuses
observed intermediates; actual application alternatives reach the same NNUE
family and remain subject to the existing inference/action/time budgets.
No additional scope query or reference-body access is permitted.

`AGDAPROVER_SCOPED_EVIDENCE_SOURCES=0` disables this additional admission view;
the default is enabled when the live scoped pool exists. The switch is captured
at search creation. This additional admission is inactive without that pool;
universe-independent signature recognition also benefits legacy callers.
Expiry/cancellation cannot create a new budget or confer acceptance.

Additive diagnostic `agdaprover.evidence-source-admission.v1`, within the bounded
retrieval-widenings records, identifies policy `structured-source-evidence-v1`,
scope/index/query IDs, `retrieved_count`, `new_expressions`, the original
`retained_expressions`, `actions_considered` and `action_limit`. It describes
admission, not a new type observation or positive label. Actual typed candidate
batches and explored choices remain in the ordinary policy trace.

For both prefix and infix relation notation, a function returning a relation is
an applicable function, not an already established relation edge. Arrows inside
parenthesized endpoints remain allowed. This keeps function-valued observations
available to the shared application generator.

## Expected-type checking

The expected-evidence lane offers fully supplied applications before structural
expansion. A matching result head is only a proposal hint; the expected target
may contain unknown indices or already be concrete. Agda checks the application
and infers hidden parameters. Missing explicit arguments are not synthesized by
this lane, and an unresolved inferred result is not stored as intermediate
evidence. Rejection leaves the parent available for other alternatives.

This lane shares the source-directed admission view above. A supplied dependent
consumer may return a family such as `P (front value)`, whose printed head does
not match the expected target before application. The existing structural-input
recognizer and a matching public local source may offer its fully supplied
application anyway. Agda checks the actual result against the expected type;
the generator does not substitute a field's result type or assume a record law.
Private/nonmatching sources and missing explicit arguments supply no candidate.
The ordinary admission order remains unchanged, and NNUE ranks all generated
checking alternatives. The existing source-admission switch disables this
additional flexible-result eligibility as well as the scoped admission view.

These decisions use the same family, typed candidates, structural features,
NNUE router and branch-local proof lineage as inference decisions. The action
tag distinguishes checking from observation without changing existing-family
features or the model format. Work consumes the shared action/checker budgets;
the `AGDAPROVER_EXPECTED_EVIDENCE` switch is captured when search starts.

## Implicit value observations

A term whose remaining parameters are all ordinary implicit binders can be
proposed as an argument to a structured consumer. The generator compares its
result shape but retains the original quantified type and expression. It does
not substitute endpoint names, guess indices, unfold coinductive records or
claim two displayed types are definitionally equal. Explicit and instance
arguments remain outside this value view.

Agda infers each complete consuming application. A matching result head can
also propose checking a whole value against the goal, allowing the expected
type to infer hidden parameters. An unresolved inferred type is never retained
as intermediate evidence; only a successful checked completion followed by
fresh reconstruction validation can receive proof credit. Rejected proposals
and resource exhaustion preserve the original parent and resource allowance.
These proposals use the existing contextual-evidence feature switch, shared
NNUE candidate/feature contract and branch-local dependency ledger.

The joint queue preserves this lineage when a selected constructor proof plan
uses contextual evidence, as specified by the
[proof-choice credit contract](proof-choice-credit-v1.md). This does not instrument
every opaque proof builder: uninstrumented decisions must not be credited
retrospectively from overall success. Training and collection stay outside
AgdaProver.
