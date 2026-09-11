# AgdaProver

AgdaProver fills holes in Agda code by searching for definitions and proofs.
It helps with routine proof steps, case splits, and related goals that need to
be solved together. Completed proofs are independently checked by Agda. It runs
locally, using bundled NNUE models to guide proof search. No model setup or
download is required.

The strength of AgdaProver is measured by [ProverStrength](https://egbertrijke.github.io/ProverStrength/).

The AgdaProver project was initiated and is maintained by Egbert Rijke. The
codebase is implemented by GPT-5.6 (early development) and GPT-6.

## Installation

AgdaProver requires Python 3.11+ and Agda 2.8.0.
The commands below use macOS/Linux paths.

```sh
git clone https://github.com/EgbertRijke/agda-prover.git
cd agda-prover
python3 -m venv .venv
.venv/bin/python -m pip install .
```

For testing entries or solving part of a file while later goals remain open,
also install the [prefix parser](docs/installation.md). Ordinary `.agda` and Markdown-literate
`.lagda.md` files are supported.

## Setting up your editor

**Emacs (27.1+):** If needed, configure Agda mode with
`agda --emacs-mode setup` ([instructions](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html#administering-the-agda-mode)).
Add this to your Emacs initialization file, replacing the checkout path:

```elisp
(with-eval-after-load 'agda2-mode
  (add-to-list 'load-path "/absolute/path/to/agda-prover/editor/")
  (require 'agdaprover)
  (setq agdaprover-python-command
        "/absolute/path/to/agda-prover/.venv/bin/python")
  (add-hook 'agda2-mode-hook #'agdaprover-mode))
```

Restart Emacs and load your Agda file with `C-c C-l`. The mode line should
show `AgdaP`; enable it manually with `M-x agdaprover-mode` if needed.

**VS Code (1.90+):** Open and trust the checkout, select **Run AgdaProver
Extension**, and press `F5`. In the Extension Development Host, open and
trust your Agda project, then run **AgdaProver: Check Setup**. No npm
installation or build step is needed. If you already have a `.vsix` package,
use **Extensions: Install from VSIX** instead.

The adapter works alongside Agda language extensions. If backend discovery
fails, set `agdaprover.projectRoot` to this checkout. To use the Python
environment installed above, set `agdaprover.pythonCommand` to
`/absolute/path/to/agda-prover/.venv/bin/python`. See the
[VS Code setup guide](editor/vscode/README.md).

## Using AgdaProver

Solve and deep search select all open goals through the cursor's goal,
or every open goal when the cursor is outside a goal. One-step commands
act on the current goal and may leave new subgoals.

| Function | Emacs | VS Code |
| --- | --- | --- |
| Solve | `C-c C-x C-p` | `Ctrl+C Ctrl+X Ctrl+P` |
| Deep search | `C-c C-x C-d` | `Ctrl+C Ctrl+X Ctrl+D` |
| Apply one refinement step | `C-c C-x C-s` | `Ctrl+C Ctrl+X Ctrl+S` |
| Test entries independently | `C-c C-x C-t` | — |
| Cancel | `C-c C-x C-k` | `Ctrl+C Ctrl+X Ctrl+K` |
| Reload editor mode | `C-c C-x C-q` | — |
| Apply last verified proof | `C-c C-x C-v` | — |
| Show last result | `M-x agdaprover-show-last-result` | — |
| Solve current goal symbolically | `M-x agdaprover-prove-goal-symbolic` | — |
| Solve current goal with NNUE | `M-x agdaprover-prove-goal-nnue` | — |
| Take one step with NNUE | `M-x agdaprover-step-goal-nnue` | — |
| Check setup | — | **AgdaProver: Check Setup** |

VS Code uses **Control** even on macOS; its commands are also available
under **AgdaProver** in the Command Palette. Emacs has an **AgdaProver** menu.
In VS Code, Solve is **AgdaProver: Prove Through Current Goal or All Goals**.

After updating AgdaProver on disk, use `C-c C-x C-q` (or
`M-x agdaprover-reload`) to load the updated Emacs mode without restarting.
Finish or cancel active AgdaProver runs first. See
[reloading the Emacs mode](docs/editor-configuration.md#reloading-the-emacs-mode)
for first-time activation in an older session.

To test a saved file, press `C-c C-x C-t` in Emacs. AgdaProver virtually
replaces one definition at a time with a hole, reports its solution, and
checks it in its original preceding context. The next test uses the original
file again, discarding the solver's replacement. The report updates live
and stops at the first unsuccessful entry. Your file stays unchanged; no
solutions are applied. See [entry testing](docs/editor-configuration.md#testing-entries).

Normal solve commands save before searching and reject stale edits. Emacs asks
before applying completed proofs; `agdaprover-apply-policy` controls this behavior.
One-step refinements apply automatically. VS Code applies and saves successful
edits automatically, then reloads through an available companion extension.
Cancel stops the current buffer's search in Emacs or the active operation in
VS Code.

Deep search allows 8,000 actions instead of 500, without adding a time or
depth cap. Explicit limits override the preset. To make it the default, set
`agdaprover-search-profile` (Emacs) or `agdaprover.searchProfile` (VS Code) to
`deep`, leaving `agdaprover-max-candidates` / `agdaprover.maxCandidates` unset
(`nil` / `null`). See [deep-search settings](docs/interactive.md#deep-search).

Open Emacs settings with `M-x customize-group RET agdaprover RET`, or use
VS Code's AgdaProver settings. The
[editor configuration guide](docs/editor-configuration.md) lists all options.

NNUE ranking is enabled by default. Select `symbolic` for `agdaprover-ranker`
(Emacs) or `agdaprover.ranker` (VS Code) to opt out. The models are small
experimental prototypes and apply across Agda files. Decision kinds without
trained weights keep symbolic ordering. See [model coverage and provenance](docs/bundled-models.md).

## Try an example

[Eckmann–Hilton](examples/EckmannHilton.agda) has 12 open goals ending in
commutativity of two-dimensional loops. No external Agda library or NNUE
model is needed.

Open it in your editor, load it with `C-c C-l` in Emacs, and place the cursor
outside every goal. Use Solve to search for a completion. Alternatively, from
the checkout:

```sh
.venv/bin/agda-prover prove-prefix examples/EckmannHilton.agda
```

Wheel installations include the example under
`share/agda-prover/examples/` in the installation prefix; copy it before editing.

## Use it from the command line

From the checkout:

```sh
.venv/bin/agda-prover inspect MyFile.agda
.venv/bin/agda-prover prove MyFile.agda --goal 0
.venv/bin/agda-prover prove-prefix MyFile.agda
.venv/bin/agda-prover prove-prefix MyFile.agda --deep
.venv/bin/agda-prover step MyFile.agda --goal 0
.venv/bin/agda-prover prove-prefix MyFile.agda --ranker symbolic
```

Commands return JSON results and proposed edits without overwriting your
source. Add `--timeout 60` for a one-minute limit. Use
`--library-file path/to/libraries` for registered dependencies, `--agda` to
select a compiler, and `--agda-option=--FLAG` for global checking options.
Both editors and the CLI preserve library and file-specific options and
ignore ambient default libraries; see the
[configuration contract](schemas/project-configuration-v1.md).

Use `--model PATH` to replace the bundled proof/focused model (or the one-step
model for `step`), and `--action-model PATH` to replace the internal OR policy.
The slots have distinct roles; see [model selection](schemas/model-defaults-v1.md).

The [interactive command](docs/interactive.md) supports progress inspection,
pause, resume, stop, and accepting individual completed goals.

## What to expect

- Useful automation, not guaranteed proofs. Difficult goals may need helper
  lemmas, more explicit definitions, or manual work.
- `verified` means the selected completion passed fresh Agda checking. It does
  not mean every remaining goal in the file is solved.
- `unsolved` or `resource-exhausted` does not mean the statement is false.
- No conversion of prose into Agda, no assumption-free proof of statements that
  require extra axioms, and no guarantee of completing an arbitrary library.

## License

AgdaProver is free software under the GNU General Public License, version 3 or
(at your option) any later version (`GPL-3.0-or-later`). It comes without any
warranty. See [LICENSE](LICENSE), [authors and acknowledgments](AUTHORS.md), and
[third-party notices](THIRD_PARTY_NOTICES.md).
