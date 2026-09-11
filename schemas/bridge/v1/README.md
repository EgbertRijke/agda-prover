# Stage 1 bridge schemas

These Draft 2020-12 schemas freeze the first public, version-neutral kernel
boundary. Runtime decoding is dependency-free and rejects unknown major
versions and unknown fields. The operation schema is a closed 20-variant sum:
one request and one result for each operation. Runtime decoding in
`agdaprover.bridge.operations` applies the same exact-field rule and verifies
identity-bearing checksums. Proof states and diagnostics have standalone
schemas because they are persisted in traces and evidence bundles.

Project routing and observational module scopes share a balanced source-header
scanner. Parameterized and multiline root headers retain their qualified module
name; Unicode and hyphenated name components use the same spelling contract in
module identities and import resolution. Comments, literate prose and module
applications cannot supply a root declaration. This is source routing, not
authority to accept a declaration: Agda still checks the original module.

The compatibility `agdaprover.module-scope.v1` source view retains each module
parameter's names, hiding, rendered binder and written type annotation. An empty
`type` means the annotation was omitted, for example `{a} (A : Set a)`; it does
not assert any inferred type. Actual types come from the kernel goal context.
Existing annotated-parameter and module-identity wire shapes are unchanged.

## Automatic introduction recovery

The P0 compatibility adapter handles an Agda 2.8 automatic introduction whose
preview is only `?` by retrying once with a capture-free explicit telescope.
Some dependent pattern binders trigger this response even for valid function
goals. The retry starts from the original parent; it cannot inherit the
unrenderable attempt's interaction metas. Its checked expression, child token
and replay lineage stay together. Unsupported or still-unrenderable output is
an unavailable action (`agda-intro-no-progress`), not an invalid input file.

This applies to speculative refinement and committed search actions, including
one-step/editor use. Ordinary introductions are unchanged. All actual kernel
requests, restoration and replay remain charged; resource exhaustion propagates
and fresh reconstruction validation is still required for completion. The raw
Stage 1 protocol and its state/diagnostic schemas are unchanged.

## Existing goal assignments

The optional solver-facing `InstantiatedGoalSession.instantiated_goal(state,
goal_id=...)` observes a term already assigned by Agda to a registered interaction.
Agda 2.8's `Cmd_solveOne AsIs` reifies that assignment in the interaction's own
scope; it does not run Agda Auto, propose an expression, remove the interaction,
or commit a search transition. An explicit empty response returns `None`.
Missing, duplicate, malformed or wrong-interaction responses are protocol errors.

Immutable state/source checks, physical request quotas and existing process
budgets apply. Failed observations invalidate the active marker before reuse.
Assigned terms may still contain nested metas or scope blanks: this observation
is not a complete-proof certificate. A caller must give the observed term through
an ordinary checked action, retain unresolved obligations, and freshly validate
any reconstructed completion. No search ordering or editor default changes;
this is an internal Python capability, not a new serialized bridge-v1 operation.

## Process completion and resource sampling

An operating-system resource sample can disappear just before a checker's exit
status becomes waitable. When polling has not collected that exit, the shared
supervisor allows one completion wait of at most 10 ms, clipped to the existing
absolute deadline. It does not retry unmonitored search or extend the task budget.
Cancellation and parent resource limits are checked again after the wait.

A child that remains unmeasurable and running is still rejected with
`resource-sampling-unavailable`. A reaped child's final CPU usage is retained and
charged; successful collection of an exit status does not imply a successful
Agda check. The validator must still inspect that status and perform the ordinary
fresh-validation and policy checks. No request, result or diagnostic wire schema
changes.

## Pinned library environments

`OpenProjectRequest.library_file` selects an explicit registry; dependency
resolution does not consult the user's default library database. The resolver
retains library flags and each source's nearest library ownership. Environment
identity distinguishes global command options from an equal option in only the
root library. Changed source, manifest or registry contents invalidate a live
environment.

Speculative and fresh-check overlays share one materializer. They contain only
the resolved source closure, its manifests and an isolated registry. Module
structure, relative source paths and source bytes remain unchanged; manifest
include paths are relocated without erasing flag boundaries or malformed fields.
Absolute in-root include paths and escaped spaces are supported. Interfaces and
ambient default libraries are not copied or consulted. Configuration artifacts
are included in storage accounting and fresh-check artifact hashes.

For a library-backed source, batch validation starts in the copied candidate's
directory, with include and candidate paths relative to that directory. Agda's
working-directory library discovery therefore stays below the relocated
manifest even when the task's temporary directory lies inside the original
library. Named and unnamed libraries retain their own flags; no synthetic
manifest or disabled library checking is needed. Sources without a library
continue to use `--no-libraries` from the overlay root.

The optional Agda 2.8 adapter accepts either the historical
`--no-libraries --ignore-interfaces --interaction-json` startup profile or
`--no-default-libraries --library-file=ABSOLUTE_PATH --ignore-interfaces
--interaction-json`. The latter registry must exist. Both profiles are set
before source parsing; unknown, duplicated or incomplete startup settings fail
closed. Rebuild the optional adapter to use the explicit-library profile.
Relocated project resets restart the worker when its registry path changes;
this cost is counted, not hidden as incremental reuse.

The opt-in `AGDAPROVER_REUSE_ROOT_OVERLAY=1` experiment may retain the existing
physical overlay for a root-only revision. It first materializes the complete
replacement independently and checks compiler/options, source ownership,
module/include topology, registry routing, manifests and dependency bytes.
The previous overlay's pinned artifacts must still match their hashes. A miss
uses ordinary replacement; detected staging damage is an error, not a reuse miss.
After staging cleanup and resource/cancellation checks, a single atomic rename
publishes the new root. Failed publication preserves the previous epoch.
Successful reset clears every old state token regardless of reuse. The next
Agda load rechecks the root and owns import-cache validity; no user-provided
`.agdai` files or provisional metas become reusable proof evidence. Fresh validation
still materializes an independent environment. `root_overlay_reuses` on the
session counts successful reuse publications; existing process/load/I/O costs
remain charged. This is not a declaration-checkpoint API or a new v1 operation.

The optional solver-facing `ProjectRevisionSession.load_project(source,
configuration)` capability explicitly rebinds project inputs and starts a new
epoch, even for an unchanged source path. The compatibility gateway implements
it through the existing project reset; its ordinary `load_module` API remains
unchanged. Compiler changes are rejected by the kernel. This is an internal
Python capability, not an addition to the serialized bridge-v1 protocol.

`AGDAPROVER_REUSE_AUXILIARY_SESSION=1` retains at most one auxiliary worker per
case-search invocation. Lookahead and provisional clause probes remain serial
and separate from the primary search session. Each lease must load its own
independently prepared project configuration before queries. Probe exceptions
discard the worker; cleanup errors cannot mask a resource refusal or
cancellation. Legacy injected sessions without project rebinding retain their
throwaway lifecycle. The absolute deadline and physical resource accounting
are not renewed. Callers may remove their temporary source copies after the
lease: the kernel owns its independently materialized overlay. With the root
reuse flag enabled, matching imports can remain warm across these probes;
without it, rebinding still uses ordinary overlay replacement. Fresh validation
is outside this facility. Neither speculative results nor old state tokens
become independently reusable proof evidence.

Fresh validation never treats `--allow-unsolved-metas` or
`--allow-incomplete-matches` as proof acceptance. Other checking waivers are
rejected unless explicitly allowed by the policy. This applies to command,
library and source options, not just the edited declaration.

This low-level library contract does not yet expose project configuration
through every public search/editor entry point or qualify every Agda version.
