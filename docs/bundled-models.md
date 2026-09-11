# Bundled NNUE models

AgdaProver includes three small, locally trained inference models. No download,
training environment or development checkout is needed to use them. The models
order candidates; Agda still checks every accepted completion.

The models can rank decisions in any Agda file, including libraries they have
never seen. Their applicability domains describe **kinds of decisions**, not
filenames or libraries. Generalization is the goal; its effectiveness on new
libraries needs separate evaluation.

These are experimental prototype weights. The current library policy continues
the earlier model with agda-unimath experience. Training coverage is still
small; symbolic ordering remains available.

## Contents and provenance

All three use 4,096 sparse inputs, 32 hidden units and seed 1. The unchanged
focused and one-step models trained for 20 epochs at learning rate 0.05. The
current library continuation uses learning rate 0.005; internal validation
selected epoch 1, with patience stopping after epoch 9 of at most 30.
Each file is approximately 513 KiB.
Artifact hashes are pinned in `agdaprover.ranking.bundled` and reported in search
results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Case selection, constructors, composed evidence and visible premises | 276 unimath proof-bound choices, continuing the earlier standard-library model |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices;
budget-censored alternatives are **not** labeled failures. It covers
`case-variable`, `constructor-choice`, `evidence-application-v1` and
`visible-premise`. The latest round contains nine case, three constructor,
nine composed-evidence and 255 premise choices. Other OR families and untrained
reasoning mechanisms retain their existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Current library OR training: `cc04796c1e09ed26abfe0ae4e26fc2ace496d59a92ccbd63c73babbc6afb25eb`
- Current library OR internal validation: `2607eb43113fb0834f89602da00e45bcb600e78f16147496572eee907d34f980`

New experience comes exclusively from agda-unimath revision
`48a91b44e97f6c8a94b7ae3ff0fa7aaa631e9b29`, checked with Agda 2.8.0. The final
training snapshot spans 33 source-module groups; four separate module groups
provide nine internal-validation choices. Shared imported foundations are
declared. Validation selects checkpoints but never updates weights; it is not
an untouched test set or unseen-library evaluation.

Both autonomous completions and reference-guided replay contribute choices from
the shared runtime actions. Reference patterns and sibling clauses are retained
only in supervised replay contexts. Every credited reconstruction receives fresh
Agda checking. Guided replay is not counted as an autonomous theorem solve.
Failed and exhausted attempts remain in the development records. Some signatures
do not uniquely specify their intended definitions: a type-correct completion
and its learning credit do not establish semantic fidelity in those cases.

The lineage continues the earlier 55-choice standard-library model, trained from
revision `810f87395c45a5dc06dc2815f69a1fbc8260e961`, through cumulative unimath
snapshots of 46, 86, 159 and now 276 choices. Earlier weights and attribution
are retained; the current round does not add standard-library examples to its gradients.
Its immediate parent is
`310ed3444c73f5df9e7fafe44fa74c41f1480a10f9ab59cfa83290c40abf36ff`.
Training tools and corpora are not included in AgdaProver.

Current library-policy SHA-256:
`17a7b26ec16a5e8e01a4bc7ef304c3ee9df8a5e644fb6e37670ad237a3344af2`.

## Measured evidence and limitations

Through the actual inference router, recorded-choice agreement is 113/276 on
training data, versus 135/276 for the parent. Internal validation remains 8/9;
its choice loss improves slightly, from 0.481401 to 0.480590. That validation
criterion selected this checkpoint despite worse training agreement. These are
reused internal samples, not an untouched evaluation or a strength-gain claim.

Full and incremental Python inference agree exactly on all 27,757 training
candidates. The optional native 32-bit scorer has errors below three millionths
against Python for both models; two batches per model exceed the evaluator's
score tolerance, but all candidate orders agree. The original discrepancy reports
are retained; the tolerance has not been relaxed.

The six required solver checks pass with the new bundled model: Eckmann–Hilton
in 14.88 seconds, rotating correspondence in 8.63, the natural-number semiring
in 16.01, the list semiring in 16.57, generic recursive families in 2.07 and
W-type destructors/fold/map in 3.18. Actions and checker-call counts match the
parent on all six. These are working-capability checks, not evidence that the
new training improves solving speed.

These are small, premise-heavy samples, not a statistically established gain
in proof strength. Continued training does not guarantee retention of every
earlier behavior. Required solver regressions and held-out searches are separate
checks; mixed informal benchmark results are not evidence of universal improvement
or regression. Fresh Agda validation remains mandatory: the model only orders
candidates. The development repository's `docs/reviews/unimath-bootcamp.md`
records the campaign, actual search outcomes and remaining limitations;
`docs/reviews/d4-case-search-accounting.md` records this continuation. Earlier
ElementaryContractibility and held-out comparisons concern the parent model,
not these new weights.

AgdaProver's authors distribute these weights under GPL-3.0-or-later. The
standard-library and agda-unimath sources retain their MIT licenses and attribution;
see [third-party notices](../THIRD_PARTY_NOTICES.md). No training corpus is
included in AgdaProver.

## Selection and overrides

Proof, joint, interactive and one-step commands use their compatible bundled
models by default. See [model selection v1](../schemas/model-defaults-v1.md) for
the exact role, override, checksum and fallback contract. `--ranker symbolic`
opts out of bundled ranking. Custom models must use the operation's role;
weights trained for one-step refinement cannot rank internal OR decisions.
