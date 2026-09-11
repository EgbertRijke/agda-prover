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
current library continuation uses learning rate 0.005 for one prospectively
chosen epoch. It is an experimental default, not this run's internal-validation
winner. The parent remains that winner; both checkpoints are retained.
Each file is approximately 513 KiB.
Artifact hashes are pinned in `agdaprover.ranking.bundled` and reported in search
results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Case selection, constructors, composed evidence and visible premises | 412 unimath proof-bound choices, continuing the earlier standard-library model |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices;
budget-censored alternatives are **not** labeled failures. It covers
`case-variable`, `constructor-choice`, `evidence-application-v1` and
`visible-premise`. The latest round contains 21 case, six constructor,
fourteen composed-evidence and 371 premise choices. Other OR families and untrained
reasoning mechanisms retain their existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Current library OR training: `939f743c160240e623f1c25d832bc21685ed7f9477e2daca6baa10e3a680bb46`
- Current library OR internal validation: `fcb6110225a209c5fc04d4832a083c00191acf88d30f7faa01b8067ab9f70665`

New experience comes exclusively from agda-unimath revision
`48a91b44e97f6c8a94b7ae3ff0fa7aaa631e9b29`, checked with Agda 2.8.0. The final
training snapshot spans 42 source-module groups; five separate module groups
provide twelve internal-validation choices. Shared imported foundations are
declared. Validation never updates weights; it is not
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
snapshots of 46, 86, 159, 276, 375, 382, 394, 403 and now 412 choices. Earlier weights
and attribution are retained; this round adds no standard-library examples to
its gradients.
Its immediate parent is
`d17f2f0c4ef58e2799c776be606c24636c9696e87b57b8185905dfc523c8d7da`.
Training tools and corpora are not included in AgdaProver.

Current library-policy SHA-256:
`88e4bca8721b61ebac5b169b0e0f2a0c9a0635bc7fd659b9ad761f363a5ddc57`.

## Measured evidence and limitations

Through the actual inference router, recorded-choice agreement is 192/412 on
training data, versus 184/412 for the parent. Internal validation falls from
12/12 to 11/12, and its choice loss rises from 0.634832 to 0.654905. The raw
training evaluator, without the router's structural priority groups, falls from
11/12 to 10/12 on validation. The one-epoch candidate was specified before training;
the parent remains the validation winner. This default publishes the retained
experimental continuation under the prototype's mixed-results policy.
These are reused internal samples, not an untouched evaluation or a strength-gain
claim. Structural priority groups explain why router agreement differs from
the unconstrained training scores.

Full and incremental Python inference agree exactly on all 59,707 training
candidates and 56 internal-validation candidates.

The six required solver checks pass with the new bundled model: Eckmann–Hilton
in 15.40 seconds, rotating correspondence in 8.77, the natural-number semiring
in 16.21, the list semiring in 16.77, generic recursive families in 2.09 and
W-type destructors/fold/map in 3.27. Action and checker counts match the previous
checkpoint on all six. These are working-capability checks, not evidence that
the new training improves solving speed.

These are small, premise-heavy samples, not a statistically established gain
in proof strength. Continued training does not guarantee retention of every
earlier behavior. Required solver regressions and held-out searches are separate
checks; mixed informal benchmark results are not evidence of universal improvement
or regression. Fresh Agda validation remains mandatory: the model only orders
candidates. The development repository's `docs/reviews/unimath-bootcamp.md`
records the campaign, actual search outcomes and remaining limitations;
`docs/reviews/d0-training-import-reuse.md` records this continuation. Earlier
ElementaryContractibility and held-out comparisons concern earlier checkpoints,
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
