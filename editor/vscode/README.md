# AgdaProver for VS Code

This extension is a thin, local client of `agdaprover editor-api`. It recognizes
ordinary `.agda` and Markdown-literate `.lagda.md` files by filename, so it does
not depend on or compete with a particular Agda language extension. It works
alongside interactive extensions including Agda2, Agda Mode, Agda Mode Fork,
and Avea, and alongside syntax-only Agda extensions. When an interactive
companion is present, AgdaProver automatically invokes its load-file command
after applying a verified edit.

## Setup and first proof

Install Python 3.11+ and Agda 2.8.0, then follow the product
[installation instructions](../../README.md#install). Open the product checkout
in VS Code, trust the workspace, and press F5 using the committed **Run AgdaProver
Extension** launch profile. The extension host opens with this adapter enabled;
it does not disable any companion Agda extension. No npm dependencies or build
step are needed for this source checkout. A packaged VSIX can instead be
installed through **Extensions: Install from VSIX**.

Open an `.agda` or `.lagda.md` file, place the cursor inside a hole, and invoke
**AgdaProver: Prove Through Current Goal or All Goals** from the command palette or use the proof
keybinding below. Outside a hole the same command selects all open goals.
If the backend cannot be found, check that the installed `agdaprover` command is
on VS Code's PATH or set `agdaprover.projectRoot` to the product checkout. A
development workspace containing its `agda-prover/` submodule is also recognized.
For prefix-parser requirements, see the product installation instructions.

The standard bindings are `Ctrl+C Ctrl+X Ctrl+P` (prove),
`Ctrl+C Ctrl+X Ctrl+S` (step), and `Ctrl+C Ctrl+X Ctrl+K` (cancel). They work as
direct VS Code chords with Agda Mode and without a companion extension. With
Agda2, AgdaProver also participates in its stateful extended-key sequence and
clears that state after dispatch. Agda Mode Fork, Avea, and syntax-only Agda
extensions remain supported; none is disabled or declared unwanted.

When installed separately from the repository, the extension first looks for
an AgdaProver checkout near the source, workspace, extension, or
`AGDAPROVER_PROJECT_ROOT`, then falls back to an installed `agdaprover` command
on `PATH`. Set `agdaprover.projectRoot` or `agdaprover.executable` only when
automatic discovery is not appropriate. A custom Agda extension can integrate
without an AgdaProver change by contributing a command titled `Load`, `Load
Agda`, or `Load file`; set `agdaprover.reloadCommand` to its command ID if
automatic metadata discovery is ambiguous, or to `none` to disable reload.

Proof-prefix selection stops at the goal containing the cursor; outside every
goal it selects every open goal in the file. Searches have no implicit
wall-time limit; set `agdaprover.timeoutSeconds` for a hard deadline. The client
saves before search, hashes the snapshot, rejects stale results, applies only
versioned reconstruction edits, saves again, and never starts a shell.

NNUE roles have separate settings: `agdaprover.model` is the proof or
focused-branch model, `agdaprover.stepModel` is the one-step model, and the
optional `agdaprover.actionModel` must be an OR-decision model. The extension
never substitutes one role's artifact for another.

Run the dependency-free adapter tests with:

```console
npm --prefix editor/vscode run check
npm --prefix editor/vscode test
```
