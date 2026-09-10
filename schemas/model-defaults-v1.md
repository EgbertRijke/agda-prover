# Bundled model selection v1

The `agdaprover.model-defaults.v1` behavior contract selects local, pinned
inference artifacts at the ranking boundary. It does not change existing
model formats, action features, candidate visibility or proof authority.

Omitting `ranker` in `TaskSpec`, the CLI or editor API now selects `nnue`.
Explicit `symbolic` requests remain supported. Existing persisted requests
should specify their ranker to retain their original behavior.

| Operation | Primary default | Internal OR default |
| --- | --- | --- |
| `prove`, `prove-prefix`, `interactive` | Focused-branch model | Scoped OR policy |
| `step` | One-step refinement model | None |
| `inspect`, `doctor` | None | None |

Unspecified model paths select bundled artifacts. `model`/`--model` overrides
the primary model for that operation. `action_model`/`--action-model` overrides
the OR policy for proof search; step does not use that slot. All models retain
their existing role and feature-schema validation. Custom models never cause a
silent fallback to bundled weights. Each slot is overridden independently.

`symbolic` disables every implicit bundled model. For compatibility, an
explicit OR-policy path remains an opt-in to hybrid symbolic/OR ranking in the
CLI and Python API, even with `ranker=symbolic`. Omit that path for a completely
symbolic run. The editors send no models when symbolic is selected.

Bundled weights must match their pinned SHA-256 and role. Missing, corrupt or
incompatible selected artifacts produce a configuration error, not a proof
failure or a hidden network download. Users can reinstall, override the slot,
or select symbolic ranking. There is no repository-relative development path.

Results and task identities record the actual loaded model hashes in their
existing model-ID fields. Unsupported OR families retain complete symbolic
ordering and the router's explicit fallback accounting. A default model does
not imply trained coverage of every decision, or that ranking improves search.

## Structural priority groups

`ORPolicyRouter.rank` accepts optional `priority_tiers`: one nonnegative integer
per candidate, in nondecreasing symbolic order. With these groups, the order is
`(tier, descending model score, symbolic position)`. Without them, the existing
unrestricted model ranking remains available. No candidate is removed and model
features/formats are unchanged. Missing or malformed model scores retain the
original symbolic order.

Ordinary premise admission preserves its existing type-directed priorities,
excluding the final spelling tie-breaker; NNUE orders equally prioritized
alternatives. Constructor selection preserves any observed preferred-arity
distance, allowing full learned ordering when there is no arity preference.
These rules depend on structure, never source filenames or benchmark names.

The complete batch is still scored and charged. Trace provenance records
`ranking_policy: structural-tiers-v1` and the aligned `priority_tiers`; its
`model_order` is the actual constrained order supplied to search, not an unused
raw-score ordering. Labels remain subject to fresh final proof validation.
