# Explicit project checking configuration

`TaskSpec.project_configuration` and the optional `project_configuration` field
of `agdaprover.editor.request.v1` use this object:

```json
{
  "schema_version": "agdaprover.project-configuration.v1",
  "executable": "agda",
  "library_file": "/absolute/path/to/libraries",
  "options": ["--without-K", "--exact-split"]
}
```

All four keys are required when the object is supplied. Unknown keys/versions
and malformed fields are rejected. `library_file` may be null; it is an Agda
registration database, not an `.agda-lib` manifest. Root manifests declare the
dependencies that must be registered there. Relative filesystem paths are
resolved at the request boundary; no ambient/default library list is read.

Omission retains the existing P0 configuration and task-identity shape for
non-library tasks. An explicit `options` array replaces the default global
options; an empty array supplies none. Library flags and source OPTIONS pragmas
retain their own scope. Process, output and library-routing flags do not belong
in this field. Agda decides whether a checking option is supported, and the
fresh-validation policy still forbids unfinished or unsafe proof acceptance.

The CLI exposes `--agda`, `--library-file` and repeatable
`--agda-option=--FLAG` on inspect, prove, prove-prefix, step and interactive.
If no `--agda-option` is supplied, the global defaults remain `--without-K`
and `--exact-split`. `--no-default-agda-options` supplies an explicitly empty
array and cannot be combined with `--agda-option`.
Configured injected session factories must accept the optional
`project_configuration` keyword; unconfigured legacy factories are unchanged.

Temporary search workspaces carry a rebound configuration with their isolated
registry. Case lookahead, guided search, structural reconstruction, fresh
validation and supplemental prefix checks use that same boundary. They must not
reuse the original registry to resolve a relocated project. Interactive workers
receive the configuration explicitly; accepting a principal variation performs
a new configured validation, not acceptance of cached evidence.

Configured/library-bound search identities include pinned source/configuration
inputs. Single-goal and configured joint completions recheck their original
input snapshots before and after validation; a changed library/source/executable
cannot silently retain the old search identity. Fresh checks retain the original
module names and physical source coordinates, with no changes to the user's file.

Library-bound P0 trust reports additionally contain
`agdaprover.checking-environment.v1`: the root module, global command options,
registered library names, relative include paths, relocated-manifest hashes,
and imported source hashes with their library owners. Prefix comparison uses
this witness to distinguish semantic changes from temporary registry path
changes. The root's body may differ and an independent prefix may omit imports;
retained imports, manifests, compiler and options must agree. Actual checker
commands and artifact hashes remain in the report, including registry artifacts.

This is configuration propagation, not incremental typechecking or permission
to reuse cached proofs. Every `verified` result still requires fresh Agda.
