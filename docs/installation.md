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

`AGDAPROVER_REUSE_ROOT_OVERLAY=1` enables experimental reuse of the checking
process across root-file revisions. It can avoid reloading unchanged library
imports. Reuse requires matching compiler options, dependency bytes and library
routing; other changes rebuild the environment. Every revision still invalidates
old proof-state tokens, and completed proofs still receive fresh validation.
It is off by default; unset the variable to return to ordinary overlay loading.
This does not cache individual declarations or omit checking the revised file.

Also set `AGDAPROVER_REUSE_AUXILIARY_SESSION=1` to keep a separate speculative
worker for successive case lookahead and tentative-clause checks. Combining
the two flags can avoid repeated library startup in those checks. Each probe
loads a new source epoch; errors discard the worker. Final proof validation
never uses it. Both flags are experimental and off by default.

With the optional adapter, `AGDAPROVER_SCOPED_RETRIEVAL=1` enables live library
premise retrieval. `AGDAPROVER_LOCAL_ELIMINATOR_READINESS=1` additionally tries
generic eliminators early only when their source is recognized in the current
local context. This can keep imported projections from crowding out local
proofs; unrecognized premises remain available to ordinary search. Both search
options are experimental and off by default. Unset the variables to compare
with the existing search order.

## Emacs checkout configuration

Use the [README setup](../README.md#setting-up-your-editor) to load the mode
with the checkout's Python environment. See the
[editor configuration guide](editor-configuration.md) for all settings.

The existing `agdaprover` command alias and Python module remain supported.
`agda-prover doctor --offline-audit` reports runtime configuration and checks
for network-capable imports; it is not a complete installation or proof test.

## Projects with registered libraries

Pass `--library-file /path/to/libraries` to select an explicit Agda registration
database. The project's `.agda-lib` declares its dependencies; the database
registers their manifests. Ambient default libraries are not read. `--agda`
selects the compiler, and repeated `--agda-option=--FLAG` arguments replace the
default global options (`--without-K`, `--exact-split`), without replacing each
library's own flags. Use `--no-default-agda-options` for no global options.

In Emacs, set the buffer-local variables `agdaprover-library-file`,
`agdaprover-agda-executable` and `agdaprover-agda-options` as needed. A relative
registry or compiler path resolves against the buffer's default directory; nil
options retain the global defaults, and an empty vector `[]` supplies none.

In VS Code, use `agdaprover.libraryFile`, `agdaprover.agdaExecutable` and
`agdaprover.agdaOptions`. The registry path may be relative to the document's
workspace folder. Null options retain the global defaults; an empty array
supplies no global options. These settings apply to proof search, prefix
search, steps and their fresh validation.
