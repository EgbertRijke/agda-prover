# AgdaProver

AgdaProver fills holes in Agda code by searching for definitions and proofs.
It helps with routine proof steps, case splits, and related goals that need to
be solved together. Completed proofs are independently checked by Agda.

It runs locally, without an online service or LLM. Optional NNUE models guide
proof search; no model is required to get started.

## Install

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

## Use it in your editor

**Emacs:** add this checkout's `editor/` directory to `load-path`, require
`agdaprover`, and enable `agdaprover-mode` alongside Agda mode.
Press `C-c C-x C-p` to solve through the goal at the cursor. Outside a goal,
the same command selects all open goals in the file. `C-c C-x C-s` proposes
one step; `C-c C-x C-k` cancels the run.

**VS Code:** follow the [extension setup](editor/vscode/README.md).
The adapter works alongside Agda language extensions.

Editor integrations check that your source has not changed before applying a
returned edit.

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
