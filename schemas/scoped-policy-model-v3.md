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
The development trainer derives it only from families with actual safe training
pairs. A validated positive with exclusively censored alternatives is retained
as experience but does not qualify that family for scoring.
