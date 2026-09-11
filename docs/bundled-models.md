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
selected epoch 24 of a 30-epoch run. Each file is approximately 513 KiB.
Artifact hashes are pinned in `agdaprover.ranking.bundled` and reported in search
results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Case selection, constructors, composed evidence and visible premises | 159 unimath proof-bound choices, continuing the earlier standard-library model |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices;
budget-censored alternatives are **not** labeled failures. It covers
`case-variable`, `constructor-choice`, `evidence-application-v1` and
`visible-premise`. The latest round contains four case, three constructor and
152 premise choices; composed-evidence coverage is inherited from earlier
training. Other OR families and untrained reasoning mechanisms retain their
existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Current library OR training: `6d47c172f913483343819e6d35296269b2c2a39c738bb8c7cc95848eacaf8e42`
- Current library OR internal validation: `2a40b3570976d02413bb836b24eb775eb0bccc77c62d273823c480a594747a82`

New experience comes exclusively from agda-unimath revision
`48a91b44e97f6c8a94b7ae3ff0fa7aaa631e9b29`, checked with Agda 2.8.0. The final
training snapshot spans 32 source-module groups; three separate module groups
provide three internal-validation choices. Shared imported foundations are
declared. Validation selects checkpoints but never updates weights; it is not
an untouched test set or unseen-library evaluation.

Both autonomous completions and reference-guided replay contribute choices from
the shared runtime actions. Reference patterns and sibling clauses are retained
only in supervised replay contexts. Every credited reconstruction receives fresh
Agda checking. Guided replay is not counted as an autonomous theorem solve.
Failed and exhausted attempts remain in the development records.

The lineage continues the earlier 55-choice standard-library model, trained from
revision `810f87395c45a5dc06dc2815f69a1fbc8260e961`, through cumulative unimath
snapshots of 46, 86 and 159 choices. Earlier weights and attribution are retained;
the current round does not add standard-library examples to its gradients.
Its immediate parent is
`e8ea7a6fdfa6429740b17b2c36078b835f292d3465ba7f2df68478b91c4fc7b2`.
Training tools and corpora are not included in AgdaProver.

Current library-policy SHA-256:
`310ed3444c73f5df9e7fafe44fa74c41f1480a10f9ab59cfa83290c40abf36ff`.

## Measured evidence and limitations

Through the actual inference router, recorded-choice agreement is 94/159 on
training data, versus 20/159 for the previous bundle. Internal validation is
2/3 versus 1/3. A separate seven-choice older-library diagnostic is mixed:
top-ranked agreement falls from 2/7 to 1/7, while average choice loss improves.
Full and incremental inference agree on all recorded candidate batches.

A four-target held-out unimath comparison solves two targets with either model;
the common successes use identical action and checker-call counts. The required
Eckmann–Hilton, rotating correspondence and two semiring checks all pass. These
checks establish working behavior, not an overall strength gain.

One paired ElementaryContractibility run solves all 31 goals with either model.
The continuation takes 282.25 seconds versus 272.21 seconds, with 3,739 versus
3,542 actions and 15,649 versus 15,049 checker calls. This informal benchmark
regresses in this update; the new experience is published as an experimental
continuation, not a claim of across-the-board improvement.

These are small, premise-heavy samples, not a statistically established gain
in proof strength. Continued training does not guarantee retention of every
earlier behavior. Required solver regressions and held-out searches are separate
checks; mixed informal benchmark results are not evidence of universal improvement
or regression. Fresh Agda validation remains mandatory: the model only orders
candidates. The development repository's `docs/reviews/unimath-bootcamp.md`
records the campaign, actual search outcomes and remaining limitations.

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
