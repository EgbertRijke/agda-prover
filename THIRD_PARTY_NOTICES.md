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
libraries, training corpora or model weights. No third-party model weights or
training corpus are bundled in this product.
