# Third-party notices

## Agda 2.8.0

The interaction loop and command reader in `native/agda-bridge/Main.hs` are
adapted from Agda's `Agda.Interaction.AgdaTop`, with JSON output based on
`Agda.Interaction.JSONTop`:

- [AgdaTop.hs](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Interaction/AgdaTop.hs)
- [JSONTop.hs](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Interaction/JSONTop.hs)

Agda is copyright its authors and is licensed under the MIT license. Its
original copyright and license text is preserved in
[licenses/Agda-MIT.txt](licenses/Agda-MIT.txt), copied from the
[Agda 2.8.0 release](https://github.com/agda/agda/blob/v2.8.0/LICENSE).
AgdaProver modifies the interaction loop to support transactional commands.

The record-literal renderer in `native/agda-bridge/RecordIntro.hs` is adapted
from `introRec` in Agda's
[BasicOps.hs](https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Interaction/BasicOps.hs).
It observes the focused goal without assigning metas and retains explicit
obligations for hidden and instance fields.

The native bridge and source parser also link against separately installed Agda
and Haskell dependencies. Distributors of compiled helpers must include the
notices and satisfy the licenses of the dependencies actually included in their
build; this source notice is not a complete binary dependency inventory.

AgdaProver's original code and contributed changes are licensed under
GPL-3.0-or-later; see [LICENSE](LICENSE) and [AUTHORS.md](AUTHORS.md). This does
not remove the upstream MIT notice above or relicense separately obtained Agda
libraries or training corpora.

## Native symbolic feature hashing

The optional Haskell symbolic core links against
[blake2 0.3.0.1](https://hackage.haskell.org/package/blake2-0.3.0.1), by
Lennart Augustsson and its contributors, under the
[Unlicense](licenses/blake2-Unlicense.txt), and
[cryptohash-sha256 0.11.102.1](https://hackage.haskell.org/package/cryptohash-sha256-0.11.102.1),
by Vincent Hanquez and Herbert Valerio Riedel, under the
[BSD 3-clause license](licenses/cryptohash-sha256-BSD-3-Clause.txt).
The BLAKE2 reference C implementation bundled with `blake2` is copyright
2012 Samuel Neves and offers a choice of CC0, OpenSSL, or Apache-2.0;
AgdaProver uses its CC0 option. These libraries provide artifact SHA-256 and
the existing personalized BLAKE2 feature hash; AgdaProver does not modify them.

These are build-time provisions for the experimental helper, not network
dependencies during inference. Binary redistribution must also account for
the complete linked dependency inventory, as described above.

## Agda standard library training sources

The bundled OR-policy weights were trained locally on a small, reviewed subset
of the [Agda standard library](https://github.com/agda/agda-stdlib), licensed
under MIT. Its unmodified copyright and permission notice is preserved in
[licenses/agda-stdlib-MIT.txt](licenses/agda-stdlib-MIT.txt).

The three bundled models are distributed by AgdaProver's authors under
GPL-3.0-or-later. Their roles, data identities and limitations are documented in
[the model card](docs/bundled-models.md). No training corpus or training
infrastructure is included in AgdaProver.

## Agda-unimath training sources

Continued OR-policy training uses a reviewed selection from
[agda-unimath](https://github.com/UniMath/agda-unimath), revision
`48a91b44e97f6c8a94b7ae3ff0fa7aaa631e9b29`, licensed under MIT.
Its unmodified copyright and permission notice is preserved in
[licenses/agda-unimath-MIT.txt](licenses/agda-unimath-MIT.txt).
The earlier standard-library attribution remains applicable to the inherited
model. Training sources and supporting infrastructure are not included in
AgdaProver; only the inference weights are bundled.
