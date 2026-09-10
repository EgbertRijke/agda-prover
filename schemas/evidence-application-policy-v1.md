# Composed-evidence choices

`evidence-application-v1` is a new OR decision family, separate from refining
with a bare visible declaration. Its action is to infer one complete application
of a supplied or previously inferred function to supplied/inferred arguments in
the exact parent state and interaction. Inference remains speculative; it grants
neither proof acceptance nor a positive training label.

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
is invalid; unresolved inferred metas or a resource interruption remain censored.
Fresh validation and the existing source/task/patch-bound proof-credit contract
are still required before any selected dependency becomes positive.

This instruments contextual evidence, not every opaque proof builder or the
joint queue. Uninstrumented decisions must not be credited retrospectively from
overall success. Training and collection stay outside the product.
