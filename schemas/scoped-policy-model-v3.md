# Scoped NNUE policy models

`agdaprover.nnue.p0.v3` uses the eight-byte magic `APNNUE3\0`, followed by
the existing little-endian header length, JSON header and float32 payload.
Header and payload bounds, weight layout and feature schema remain unchanged.
The magic and header schema must agree. The model ID hashes the whole artifact,
including its applicability domain; no training sidecar is needed for inference.

This format is restricted to role `or-decision-ranking` and feature family
`or-decision-v4`. Its required `policy_families` field is a nonempty JSON array
of unique strings in lexical order, drawn from:

- `case-variable`
- `constructor-choice`
- `recursive-call`
- `visible-premise`

Other families retain the complete symbolic candidate order. The router skips
feature extraction and scoring for them, increments
`unsupported_family_fallbacks` for genuine multi-candidate decisions, and records
`policy_fallback_reason: unsupported-decision-family` with no ranking model ID.
This fallback does not remove candidates or alter kernel validation.

Version 1 and 2 unscoped models retain their existing behavior. They may not
carry `policy_families`: older readers could ignore that field and apply an
inappropriately scoped model. Older readers reject version 3 rather than silently
discarding its applicability restriction. Corrupt, empty, unknown or wrong-role
domains are rejected before inference.

The domain declares intended applicability, not training quality or qualification.
The development trainer derives it from families that contribute to the selected
objective. The default pairwise objective requires actual safe comparison pairs;
a positive with exclusively censored alternatives contributes no pair. The
optional validated-choice imitation objective instead requires a source-bound
validated action choice and learns its categorical selection probability. It
does not label censored alternatives as unsuccessful proofs. Its metadata names
that objective and counts decisions by family, rather than claiming pair counts.
Both objectives use this same format and preserve symbolic ordering outside the
declared domain. Applicability is not model promotion or a performance claim.
