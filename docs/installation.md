# Installation details

## Prefix validation

To solve selected goals while later declarations remain unfinished, build the
source-prefix parser. It requires GHC and the Agda 2.8.0 Haskell package, in
addition to the `agda` executable:

```sh
./scripts/build-source-parser
export AGDAPROVER_SOURCE_PARSER="$PWD/native/source-parser/target/agdaprover-source-parser"
```

The build script defaults to the GHC 9.6.7 Cabal package database. Set
`AGDAPROVER_AGDA_PACKAGE_DB` to your compatible package database if it differs.
Source checkouts discover the built parser automatically. Installed wheels need
the environment variable above or `agdaprover-source-parser` on PATH. Search
never builds or downloads it. The parser finds declaration boundaries; Agda
still checks the completed prefix independently.

## Optional acceleration and models

`./scripts/build-native` builds CPU NNUE inference with Rust. Without it, the
same interface uses Python. `--ranker nnue --model PATH` selects a compatible
model; symbolic search needs no weights or training framework.

`./scripts/build-agda-bridge` builds the optional Agda transaction adapter with
GHC. Set `AGDAPROVER_AGDA_BRIDGE` to its executable to opt in. The stock Agda
interaction process remains the default. Fresh proof validation remains
independent of either speculative backend.

With the optional adapter, `AGDAPROVER_SCOPED_RETRIEVAL=1` enables live library
premise retrieval. `AGDAPROVER_LOCAL_ELIMINATOR_READINESS=1` additionally tries
generic eliminators early only when their source is recognized in the current
local context. This can keep imported projections from crowding out local
proofs; unrecognized premises remain available to ordinary search. Both search
options are experimental and off by default. Unset the variables to compare
with the existing search order.

## Emacs checkout configuration

```elisp
(add-to-list 'load-path "/path/to/agda-prover/editor")
(require 'agdaprover)
(setq agdaprover-project-root "/path/to/agda-prover")
(add-hook 'agda2-mode-hook #'agdaprover-mode)
```

The existing `agdaprover` command alias and Python module remain supported.
`agda-prover doctor --offline-audit` reports runtime configuration and checks
for network-capable imports; it is not a complete installation or proof test.
