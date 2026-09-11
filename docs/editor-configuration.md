# Editor configuration

For installation and keyboard shortcuts, see the [README](../README.md).
Open Emacs settings with `M-x customize-group RET agdaprover RET`, or search
for `agdaprover` in VS Code's Settings editor.

## Reloading the Emacs mode

After updating your local AgdaProver checkout, press `C-c C-x C-q`, run
`M-x agdaprover-reload`, or select **Reload AgdaProver editor mode** from
the AgdaProver menu. This reloads the mode's `.el` source from the checkout
that supplied the mode, even if an older compiled copy exists. Settings,
custom keybindings, open buffers, and saved search results are preserved;
updated commands are available in every buffer where the mode is enabled.
Finish or cancel AgdaProver runs in all buffers before reloading.

If your current Emacs session predates this command, use `M-x load-file`
and select the updated `editor/agdaprover.el` once. The shortcut is then
available for subsequent updates.

Reloading does not download updates, reload your Agda files, or switch the
configured backend checkout. The next search starts a new backend process
using the configured installation.

## Backend and Agda

The checkout setting identifies **AgdaProver**, not the Agda project you are
proving. Prefer absolute paths for checkout, executable, and model settings.

| Setting | Emacs variable | VS Code setting |
| --- | --- | --- |
| AgdaProver checkout | `agdaprover-project-root` | `agdaprover.projectRoot` |
| Python executable | `agdaprover-python-command` | `agdaprover.pythonCommand` |
| Installed backend executable | — | `agdaprover.executable` |
| Agda compiler | `agdaprover-agda-executable` | `agdaprover.agdaExecutable` |
| Agda library registry | `agdaprover-library-file` | `agdaprover.libraryFile` |
| Global Agda checking options | `agdaprover-agda-options` | `agdaprover.agdaOptions` |

Emacs infers the checkout from `agdaprover.el` and defaults to `python3`.
VS Code discovers a checkout or uses the installed `agdaprover` command on
`PATH`. For a checkout, its default Python setting, `auto`, selects `python3`
on macOS/Linux or `python` on Windows; it does not select the checkout's
virtual environment automatically. Set the Python executable explicitly to
use that environment. `agdaprover.executable`, when set, selects an installed
backend instead of launching Python from the checkout.

The compiler defaults to `agda` on `PATH`. Library and source-file checking
options are preserved; ambient default libraries are not used. Unset global
options (`nil` in Emacs, `null` in VS Code) retain `--without-K` and
`--exact-split`. An empty vector `[]` in Emacs or empty array `[]` in VS Code
supplies no global checking options. See the
[project configuration contract](../schemas/project-configuration-v1.md)
for library registration and path resolution.

## Search effort

| Setting | Emacs variable | VS Code setting |
| --- | --- | --- |
| Search preset | `agdaprover-search-profile` | `agdaprover.searchProfile` |
| Whole-run action allowance | `agdaprover-max-candidates` | `agdaprover.maxCandidates` |
| Term-size setting | `agdaprover-max-term-size` | `agdaprover.maxTermSize` |
| Depth limit | `agdaprover-max-depth` | `agdaprover.maxDepth` |
| Time limit in seconds | `agdaprover-timeout` | `agdaprover.timeoutSeconds` |

The default preset is `standard` (500 actions). Select `deep` for 8,000
actions, keeping the action allowance unset (`nil` / `null`) to use the
preset. An explicit allowance overrides both presets; it counts search
actions, not physical Agda calls. The term-size setting defaults to 8.
Time and depth limits are unset by default. Deep search does not remove
explicit limits or increase the other resource allowances. See
[deep search](interactive.md#deep-search).

## NNUE models

| Setting | Emacs variable | VS Code setting |
| --- | --- | --- |
| Candidate ranking | `agdaprover-ranker` | `agdaprover.ranker` |
| Separate one-step ranking | `agdaprover-step-ranker` | — |
| Proof or focused-branch model | `agdaprover-model-file` | `agdaprover.model` |
| One-step model | `agdaprover-step-model-file` | `agdaprover.stepModel` |
| OR-decision model | `agdaprover-action-model-file` | `agdaprover.actionModel` |

Models are bundled: no model paths are required. Emacs defaults to `auto`
(an alias for `nnue`); its one-step ranker follows the main ranker unless
overridden. VS Code defaults to `nnue`. Select `symbolic` to disable neural
ranking. Unset model paths use the operation's bundled defaults; setting a
path overrides that slot independently.

Proof search and one-step refinement need different model roles. A one-step
model must have the `one-step-refinement-ranking` role; an optional model
for internal search choices must have the `or-decision-ranking` role.
These artifacts are not interchangeable. In the editors, the OR-decision
model accompanies NNUE proof search, not symbolic or one-step search.
Custom paths must be readable and compatible; invalid overrides are reported,
not silently replaced. See [bundled model coverage](bundled-models.md) and the
[selection contract](../schemas/model-defaults-v1.md).

## Applying results

| Setting | Emacs variable | VS Code setting |
| --- | --- | --- |
| Completed-proof application policy | `agdaprover-apply-policy` | — |
| Companion reload command | — | `agdaprover.reloadCommand` |

Emacs defaults to `ask` before applying completed proofs. Select `always`
to apply automatically, or `never` to retain results for manual application.
One-step refinements apply automatically, independently of this setting.
VS Code applies and saves successful edits automatically. Both editors
reject results for a changed source snapshot.

VS Code's reload setting defaults to `auto`, which detects an available
Agda extension's load-file command. Select `none` to disable reloading,
or supply a companion extension's command ID. See the
[VS Code guide](../editor/vscode/README.md).
