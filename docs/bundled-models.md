# Bundled NNUE models

AgdaProver includes three small, locally trained inference models. No download,
training environment or development checkout is needed to use them. The models
order candidates; Agda still checks every accepted completion.

The models can rank decisions in any Agda file, including libraries they have
never seen. Their applicability domains describe **kinds of decisions**, not
filenames or libraries. Generalization is the goal; its effectiveness on new
libraries needs separate evaluation.

These are experimental prototype weights, not a claim of stronger search.
Their training coverage is small, and the library policy has not demonstrated
a downstream efficiency gain. Symbolic ordering remains available.

## Contents and provenance

All three use 4,096 sparse inputs, 32 hidden units, seed 1, and 20 training
epochs at learning rate 0.05. Each file is approximately 513 KiB. Artifact
hashes are pinned in `agdaprover.ranking.bundled` and reported in search results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Constructor and visible-premise choices | Eight validated choices from Agda standard-library reconstruction |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices; its
eleven censored alternatives were **not** labeled failures. It covers only
`constructor-choice` and `visible-premise`. Other OR families and untrained
reasoning mechanisms retain their existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Library OR: `a37f393402115c9adec533f151ad927cb8ce651c713f3612430b6aba7ae1d21e`

The library experiment uses a target-held-out protocol with explicitly reviewed
shared foundations, not whole-project-held-out generalization. In its eight-task
paired calibration, symbolic and learned search each solved seven tasks with
identical action and verifier counts; the model added inference work. The
28-target preparation included unsuccessful searches, which were retained in
development records. Those records and all training tools remain outside this
product. See the development project's `docs/reviews/e3-shared-policy-calibration.md`
for the frozen experiment, source pins and limitations.

AgdaProver's authors distribute these weights under GPL-3.0-or-later. The
standard-library training sources retain their MIT license and attribution;
see [third-party notices](../THIRD_PARTY_NOTICES.md). No training corpus is
included in the product.

## Selection and overrides

Proof, joint, interactive and one-step commands use their compatible bundled
models by default. See [model selection v1](../schemas/model-defaults-v1.md) for
the exact role, override, checksum and fallback contract. `--ranker symbolic`
opts out of bundled ranking. Custom models must use the operation's role;
weights trained for one-step refinement cannot rank internal OR decisions.
