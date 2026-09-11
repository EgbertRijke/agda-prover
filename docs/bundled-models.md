# Bundled NNUE models

AgdaProver includes three small, locally trained inference models. No download,
training environment or development checkout is needed to use them. The models
order candidates; Agda still checks every accepted completion.

The models can rank decisions in any Agda file, including libraries they have
never seen. Their applicability domains describe **kinds of decisions**, not
filenames or libraries. Generalization is the goal; its effectiveness on new
libraries needs separate evaluation.

These are experimental prototype weights. The current library policy uses
more training examples and guides more kinds of decisions than its predecessor.
Training coverage is still small; symbolic ordering remains available.

## Contents and provenance

All three use 4,096 sparse inputs, 32 hidden units, seed 1 and learning rate
0.05. The focused and one-step models trained for 20 epochs. The library policy
was selected at epoch 12 by internal validation loss; training stopped at epoch
17 after five epochs without improvement. Each file is approximately 513 KiB.
Artifact hashes are pinned in `agdaprover.ranking.bundled` and reported in search
results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Case selection, constructors, composed evidence and visible premises | 55 proof-bound choices from Agda standard-library reconstruction |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices;
budget-censored alternatives are **not** labeled failures. It covers
`case-variable` (2 training choices), `constructor-choice` (14),
`evidence-application-v1` (15) and `visible-premise` (24). Other OR families and
untrained reasoning mechanisms retain their existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Library OR training: `62d8e0f9e9957cd8c75070763b4268520bddab08fcf6ed9a65cd4a74e6fdaa7d`
- Library OR internal validation: `31c439f17a48d9b3ab90d0388ebfba81e7080c85de19c7b6568d1d3f61ed6cb5`

The library policy was produced by a replayed collection/training generation
from pinned Agda standard-library revision
`810f87395c45a5dc06dc2815f69a1fbc8260e961`. Its seven-choice internal validation
set comes from a separate module and was also used to select the checkpoint;
it is not an untouched test set. Case and evidence training currently comes
from one module, so broad coverage is not established. Failed and exhausted
searches remain in the development records. Training tools and corpora are not
included in AgdaProver.

Current library-policy SHA-256:
`24949aaa1cf674745d3bc50cd0534c215fb61ab0ea2ab335f0af3aa63c9a9811`.

## Measured evidence and limitations

One matched deep-search comparison freshly solved all 31 ElementaryContractibility
goals in 254.13 seconds, versus 261.28 seconds with the previous bundled policy:
2.7% less elapsed time, 507 fewer verifier requests and 204 fewer search actions.
This is an encouraging single observation, not a statistically established
overall improvement or a guarantee for other files.

Internal validation is mixed: top-ranked agreement with recorded proof choices
is 2/7, versus 3/7 for the previous bundle, despite lower choice loss. This is an
experimental default selected with protected-benchmark checks, not a fully
qualified strength release. Fresh Agda validation remains mandatory; the model
only changes candidate ordering. See the development repository's
`docs/reviews/f1-training-generations.md` and
`docs/reviews/elementary-nnue-comparison.md` for reproducibility and provenance.

AgdaProver's authors distribute these weights under GPL-3.0-or-later. The
standard-library training sources retain their MIT license and attribution;
see [third-party notices](../THIRD_PARTY_NOTICES.md). No training corpus is
included in AgdaProver.

## Selection and overrides

Proof, joint, interactive and one-step commands use their compatible bundled
models by default. See [model selection v1](../schemas/model-defaults-v1.md) for
the exact role, override, checksum and fallback contract. `--ranker symbolic`
opts out of bundled ranking. Custom models must use the operation's role;
weights trained for one-step refinement cannot rank internal OR decisions.
