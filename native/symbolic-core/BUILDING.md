# Build and relocation

The Haskell engine is experimental and explicitly selected with `--engine
haskell`. It is supplied as source, not as a qualified binary release. The
Python engine remains the default. No compiler, package manager or download
is invoked when the solver starts.

## Toolchain

Use GHC 9.6.7 and Agda 2.8.0. Provision Cabal dependencies separately before
running the offline build scripts. Direct dependency versions are specified
in [the Cabal package](agda-prover-symbolic.cabal). For example, with the
specified compiler selected:

```sh
cabal update
cabal install --lib Agda-2.8.0 aeson-2.2.4.1 bytestring-0.11.5.4 \
  blake2-0.3.0.1 cryptohash-sha256-0.11.102.1 random-1.3.1 \
  --index-state=2026-09-01T00:00:00Z --constraint='Agda +use-xdg-data-home'
cabal install Agda-2.8.0 --index-state=2026-09-01T00:00:00Z \
  --constraint='Agda +use-xdg-data-home' --constraint='any.aeson ==2.2.4.1' \
  --constraint='any.random ==1.3.1' --install-method=copy
scripts/build-symbolic-core
scripts/build-source-parser
```

Run these commands from the AgdaProver checkout. An existing custom package
database can be selected with `AGDAPROVER_AGDA_PACKAGE_DB`. The offline build
refuses to rebuild missing Agda/aeson packages implicitly. Keep Cabal's resolved
`plan.json`, compiler version, source revision and executable hashes with each
candidate build; the direct versions alone are not a complete dependency lock.
Different platforms have separate dependency plans and qualification results.

## Runtime components

A native installation needs:

- The AgdaProver Python package and its bundled NNUE models.
- `agdaprover-symbolic`, selected explicitly by path or launch configuration.
- `agdaprover-source-parser`, discoverable by the shared application.
- A separate Agda 2.8.0 executable for preparation and fresh validation.

The optional Rust NNUE scorer is unchanged; reference inference works when it
is unavailable. Editors use the same application interface for either engine.

Both the linked Agda library and the separate checker need the
`use-xdg-data-home` build flag for relocation away from the build machine's
Cabal store. The flag lets Agda install its embedded primitives and other
runtime data into the application's isolated XDG data directory. Do not
redirect lookup to an empty data directory or copy only the primitive module:
Agda owns that runtime layout.

Build tools and source archives are not required during inference. A proper
relocation check copies the executables, installs the wheel outside the
checkout, denies network and access to the developer store/build tree, and
checks proof, prefix and step operations with fresh Agda validation. A successful
local check is not a claim that other platforms or large benchmarks qualify.

## Distribution boundary

This source checkout contains the engine, parser, application, models and
editor interfaces, without development or training infrastructure. Build
directories and private corpus material are not distributable dependencies.

No compiled native release is currently published. Before distributing one,
include the exact linked dependency inventory, its license notices and any
required corresponding source; see [third-party notices](../../THIRD_PARTY_NOTICES.md).
Packaging or a successful kernel check does not promote the default engine.
