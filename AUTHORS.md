# Authors and acknowledgments

Copyright (C) 2026 Egbert Rijke and contributors. Contributors retain copyright
in their contributions. AgdaProver's original code is licensed under
GPL-3.0-or-later; third-party portions retain the notices and terms identified
in [Third-party notices](THIRD_PARTY_NOTICES.md).

- **Egbert Rijke:** project design, development and maintenance.
- **Emily Riehl** (`emilyriehl`): VS Code integration and development setup,
  including Agda2 key-sequence handling. Her retained contributions originated
  in development commit `44bbf852e5a2ef712ac06f7c87826a6316c0e894` before the
  product repository was separated.
- **The Agda authors:** the proof checker and parser APIs, and the upstream
  interaction-loop code adapted by the native bridge. Their original copyright
  and MIT license are preserved in [licenses/Agda-MIT.txt](licenses/Agda-MIT.txt).

NNUE (efficiently updatable neural networks) was introduced by Yu Nasu for shogi
and subsequently developed by the shogi and Stockfish communities. AgdaProver
uses the term to describe its incremental neural evaluation approach. This
acknowledgment does not imply endorsement or model-format compatibility; see
the [NNUE documentation](https://official-stockfish.github.io/docs/nnue-pytorch-wiki/docs/nnue.html).
