# AgdaProver

AgdaProver fills holes in Agda code by searching for definitions and proofs.
It helps with routine proof steps, case splits, and related goals that need to
be solved together. Completed proofs are independently checked by Agda. It runs
locally. Optional NNUE models guide proof search; no model is required to get
started.

The AgdaProver project was initiated and is maintained by Egbert Rijke. The code-base is implemented by GPT-5.6 (early development) and GPT-6.

## Installation

Requires Python 3.11+ and Agda 2.8.0.

```sh
git clone git@github.com:EgbertRijke/agda-prover.git
cd agda-prover
python3 -m venv .venv
.venv/bin/python -m pip install .
```

For solving part of a file while later goals remain open, also install the
[prefix parser](docs/installation.md). Ordinary `.agda` and Markdown-literate
`.lagda.md` files are supported.

## Setting up Editor Extensions for AgdaProver

**Emacs (27.1+):** first install AgdaProver as described under
[Installation](#installation) and configure Agda's Emacs mode. Add the following to your
Emacs initialization file, replacing `/absolute/path/to/agda-prover/` with
the location of this checkout:

```elisp
(with-eval-after-load 'agda2-mode
  (add-to-list 'load-path "/absolute/path/to/agda-prover/editor/")
  (require 'agdaprover)
  (setq agdaprover-python-command
        "/absolute/path/to/agda-prover/.venv/bin/python")
  (add-hook 'agda2-mode-hook #'agdaprover-mode))
```

Restart Emacs, open an `.agda` or `.lagda.md` file in Agda mode, and load it
with `C-c C-l`. The mode line should show `AgdaP`. For an already-open Agda
buffer, enable the integration with `M-x agdaprover-mode`.

**VS Code (1.90+):** first install AgdaProver as described under
[Installation](#installation). To run the extension directly from this checkout:

1. Open the AgdaProver repository root in VS Code and trust the workspace.
2. Select **Run AgdaProver Extension** in the Run and Debug view and press
   `F5`.
3. In the new Extension Development Host window, open your Agda project,
   trust its workspace, and open an `.agda` or `.lagda.md` file.
4. Run **AgdaProver: Check Setup** from the Command Palette.

This development setup requires no npm dependencies or build step. To install
a packaged extension in your normal VS Code window instead, use
**Extensions: Install from VSIX** and select an AgdaProver `.vsix` package.

The extension automatically looks for an AgdaProver checkout, then falls back
to the installed `agdaprover` command on `PATH`. If discovery fails, set
`agdaprover.projectRoot` to the checkout's absolute path or
`agdaprover.executable` to the installed backend executable. For the virtual
environment installation above, that executable is
`/absolute/path/to/agda-prover/.venv/bin/agdaprover`.

The adapter works alongside Agda language extensions; no particular companion
extension is required. See the [VS Code setup guide](editor/vscode/README.md)
for further configuration.

## Using AgdaProver

| Function                                 | Emacs                                | VS Code                     | Behavior                                                                                                                  |
| ---------------------------------------- | ------------------------------------ | --------------------------- | ------------------------------------------------------------------------------------------------------------------------- |
| Solve                                    | `C-c C-x C-p`                        | `Ctrl+C Ctrl+X Ctrl+P`      | Solve all open goals through the goal at the cursor, or all open goals in the file when the cursor is outside every goal. |
| Deep search                              | `C-c C-x C-d`                        | `Ctrl+C Ctrl+X Ctrl+D`      | Solve the same selection with a larger search allowance.                                                                  |
| Take one step                            | `C-c C-x C-s`                        | `Ctrl+C Ctrl+X Ctrl+S`      | Choose and apply one Agda-accepted refinement at the current goal; this may leave new subgoals.                           |
| Cancel                                   | `C-c C-x C-k`                        | `Ctrl+C Ctrl+X Ctrl+K`      | Cancel the current buffer's search in Emacs, or the active AgdaProver operation in VS Code.                               |
| Apply the last verified proof            | `C-c C-x C-v`                        | —                           | Apply a previously returned proof if its source snapshot is still current.                                                |
| Show the last result                     | `M-x agdaprover-show-last-result`    | —                           | Display the most recent result buffer.                                                                                    |
| Solve only the current goal symbolically | `M-x agdaprover-prove-goal-symbolic` | —                           | Search for a complete proof of the current goal using symbolic ranking.                                                   |
| Solve only the current goal with NNUE    | `M-x agdaprover-prove-goal-nnue`     | —                           | Search for a complete proof of the current goal using the configured NNUE proof model.                                    |
| Take one step with NNUE                  | `M-x agdaprover-step-goal-nnue`      | —                           | Apply a refinement using the configured one-step NNUE model.                                                              |
| Check setup                              | —                                    | **AgdaProver: Check Setup** | Check backend availability and companion reload configuration.                                                            |

The VS Code shortcuts use **Control**, including on macOS. Its Command Palette
also provides **AgdaProver: Prove Through Current Goal or All Goals**,
**AgdaProver: Deep Search Through Current Goal or All Goals**,
**AgdaProver: Take One Step**, and **AgdaProver: Cancel**.
Solve and step are also available from the editor title and context menus;
the AgdaProver status-bar button starts Solve. Emacs provides an
**AgdaProver** menu. Its `C-c C-x C-n` binding is reserved and performs no
search.

Both editors save the source before searching and reject stale results before
applying edits. **Emacs asks before applying completed proofs by default**:
set `agdaprover-apply-policy` to `always` to apply automatically, or `never`
to retain results for manual application. One-step refinements apply
automatically, independently of this policy. **VS Code automatically applies
and saves successful edits**, then invokes a detected companion extension's
load-file command when available.

Deep search raises the default whole-run allowance from 500 to 8,000 search
actions. It can take longer and does not guarantee a completion. Neither
preset imposes a time or depth limit; explicit resource limits remain active.
The command-line equivalent is
`agda-prover prove-prefix MyFile.agda --deep`.

Configure Emacs through `M-x customize-group RET agdaprover RET`, and VS Code
through its AgdaProver settings:

| Setting                            | Emacs variable                 | VS Code setting             |
| ---------------------------------- | ------------------------------ | --------------------------- |
| AgdaProver checkout                | `agdaprover-project-root`      | `agdaprover.projectRoot`    |
| Python executable                  | `agdaprover-python-command`    | `agdaprover.pythonCommand`  |
| Installed backend executable       | —                              | `agdaprover.executable`     |
| Agda compiler                      | `agdaprover-agda-executable`   | `agdaprover.agdaExecutable` |
| Agda library database              | `agdaprover-library-file`      | `agdaprover.libraryFile`    |
| Global Agda checking options       | `agdaprover-agda-options`      | `agdaprover.agdaOptions`    |
| Search preset                      | `agdaprover-search-profile`    | `agdaprover.searchProfile`  |
| Whole-run action allowance         | `agdaprover-max-candidates`    | `agdaprover.maxCandidates`  |
| Term-size limit                    | `agdaprover-max-term-size`     | `agdaprover.maxTermSize`    |
| Depth limit                        | `agdaprover-max-depth`         | `agdaprover.maxDepth`       |
| Time limit in seconds              | `agdaprover-timeout`           | `agdaprover.timeoutSeconds` |
| Candidate ranking                  | `agdaprover-ranker`            | `agdaprover.ranker`         |
| Separate one-step ranking          | `agdaprover-step-ranker`       | —                           |
| Proof or focused-branch NNUE model | `agdaprover-model-file`        | `agdaprover.model`          |
| One-step NNUE model                | `agdaprover-step-model-file`   | `agdaprover.stepModel`      |
| OR-decision NNUE model             | `agdaprover-action-model-file` | `agdaprover.actionModel`    |
| Completed-proof application policy | `agdaprover-apply-policy`      | —                           |
| Companion reload command           | —                              | `agdaprover.reloadCommand`  |

To make deep search the default, select `deep` as the search preset and leave
the action allowance unset (`nil` in Emacs, `null` in VS Code). An explicit
action allowance overrides either preset. See
[deep-search settings](docs/interactive.md#deep-search).

No NNUE model is required. Emacs defaults to `auto` ranking, using NNUE when
the relevant model is readable and symbolic ranking otherwise; its step
ranker follows the main ranker unless overridden. VS Code defaults to
`symbolic`. Proof, one-step, and OR-decision models have distinct roles and
are not interchangeable.

Library and source-file options are preserved; ambient default libraries are
not used. Unset global checking options retain `--without-K` and
`--exact-split`; use an empty vector `[]` in Emacs or an empty array `[]` in
VS Code to supply no global checking options. See the
[configuration contract](schemas/project-configuration-v1.md).

## Try an example

[Eckmann–Hilton](examples/EckmannHilton.agda) is a self-contained example with
12 open goals, ending in commutativity of two-dimensional loops. No external
Agda library or NNUE model is needed.

In Emacs, open the file, load it with `C-c C-l`, place the cursor outside any
goal, and press `C-c C-x C-p` to solve the whole file. From this checkout:

```sh
.venv/bin/agda-prover prove-prefix examples/EckmannHilton.agda
```

The command returns a freshly checked completion without overwriting the example.
Wheel installations also include the file under
`share/agda-prover/examples/` inside the installation prefix; copy it to a
working directory before editing it.

## Use it from the command line

For a project with registered dependencies, pass your Agda library database:

```sh
agda-prover prove-prefix path/to/Module.agda --library-file path/to/libraries
```

Library and file-specific options are preserved. `--agda` selects a compiler;
`--agda-option=--FLAG` supplies global checking options. Ambient default libraries
are not used. See the [configuration contract](schemas/project-configuration-v1.md).

```sh
.venv/bin/agda-prover inspect MyFile.agda
.venv/bin/agda-prover prove MyFile.agda --goal 0
.venv/bin/agda-prover prove-prefix MyFile.agda
.venv/bin/agda-prover step MyFile.agda --goal 0
```

Commands return JSON results and proposed edits; they do not overwrite your
source. Add `--timeout 60` to limit a search to one minute. The
[interactive command](docs/interactive.md) supports progress inspection,
pause, resume, stop, and accepting an individual completed goal.

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
