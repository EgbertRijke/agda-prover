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
chosen epoch. The parent remains this run's internal-validation winner; the
retained epoch is an experimental default, not a qualified strength improvement.
The parent and new checkpoint are both retained.
Each file is approximately 513 KiB.
Artifact hashes are pinned in `agdaprover.ranking.bundled` and reported in search
results.

| Artifact | Trained role | Training evidence |
| --- | --- | --- |
| `focused.apnnue` | Focused-branch policy | One proof-bound comparison from the project's `Ambiguous.agda` fixture |
| `step.apnnue` | One-step refinement | 20 accepted/rejected refinement comparisons from project-owned fixtures |
| `or-policy.apnnue` | Case selection, constructors, composed evidence and visible premises | 459 unimath proof-bound choices, continuing the earlier standard-library model |

The focused model's positive lies on a freshly validated proof, and its negative
branch was exhausted. One-step labels concern accepted refinements, not complete
proofs. The scoped library policy imitates observed proof-path choices;
budget-censored alternatives are **not** labeled failures. It covers
`case-variable`, `constructor-choice`, `evidence-application-v1` and
`visible-premise`. The latest round contains 21 case, six constructor,
33 composed-evidence and 399 premise choices. Other OR families and untrained
reasoning mechanisms retain their existing symbolic behavior.
For ordinary premises and arity-directed construction, structural priority
groups are preserved and NNUE orders alternatives within each group. This
prevents a small model from overriding existing type-directed scheduling.

Training-data SHA-256 identities:

- Focused: `de38b749bc8cdda3d5e888e419bb9fff2ee5db09792ed70ed25ca03397747c78`
- One-step: `edf7d182862dca64276510c0bbaa373d915c50e91b6991951acd2d7688ef9ffa`
- Current library OR training: `32ab8fb336a28b3ffb1873fd1abcaa1d862b65be52192233325523058a23ce7b`
- Current library OR internal validation: `fcb6110225a209c5fc04d4832a083c00191acf88d30f7faa01b8067ab9f70665`

New experience comes exclusively from agda-unimath revision
`48a91b44e97f6c8a94b7ae3ff0fa7aaa631e9b29`, checked with Agda 2.8.0. The final
training snapshot spans 43 source-module groups; five separate module groups
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
snapshots of 46, 86, 159, 276, 375, 382, 394, 403, 412, 430, 449 and now 459 choices. Earlier weights
and attribution are retained; this round adds no standard-library examples to
its gradients.
Its immediate parent is
`0eaa1a78f68df5f4f42e831e28c7cf4bb695f7b596d0de17a633753fcdb5c163`.
Training tools and corpora are not included in AgdaProver.

Current library-policy SHA-256:
`1a603876058617cf6debe0faffc413315792c70161e6374f6417b56a9c0ea4ce`.

## Measured evidence and limitations

Through the actual inference router, recorded-choice agreement is 226/459 on
training data, versus 220/459 for the parent; training imitation loss falls from
2.029416 to 1.903373. Internal-validation agreement falls from 11/12 to 10/12,
while its choice loss rises from 0.601979 to 0.657864. The raw trainer, without
the router's structural priority groups, moves from 10/12 to 9/12 on validation.
The one-epoch candidate was specified before training. This default publishes
the retained experimental continuation under the prototype's mixed-results
policy, while preserving the parent as the validation winner. Improved training
agreement does not establish stronger search.
These are reused internal samples, not an untouched evaluation or a strength-gain
claim. Structural priority groups explain why router agreement differs from
the unconstrained training scores.

Full and incremental Python inference agree exactly on all 69,119 training
candidates and 56 internal-validation candidates.

The six required solver checks pass with the new bundled model: Eckmann–Hilton
in 15.57 seconds, rotating correspondence in 9.15, the natural-number semiring
in 16.28, the list semiring in 16.81, generic recursive families in 2.20 and
W-type destructors/fold/map in 3.45. This release also extends expected-type
checking to supplied dependent fields. These are working-capability checks,
not an isolated parent/candidate comparison or evidence that
the new training improves solving speed.

These are small, premise-heavy samples, not a statistically established gain
in proof strength. Continued training does not guarantee retention of every
earlier behavior. Required solver regressions and held-out searches are separate
checks; mixed informal benchmark results are not evidence of universal improvement
or regression. Fresh Agda validation remains mandatory: the model only orders
candidates. The development repository's `docs/reviews/unimath-bootcamp.md`
records the campaign, actual search outcomes and remaining limitations;
`docs/reviews/d1-expected-source-checking.md` records this continuation. Earlier
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
