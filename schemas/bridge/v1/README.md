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

The optional Agda 2.8 adapter accepts either the historical
`--no-libraries --ignore-interfaces --interaction-json` startup profile or
`--no-default-libraries --library-file=ABSOLUTE_PATH --ignore-interfaces
--interaction-json`. The latter registry must exist. Both profiles are set
before source parsing; unknown, duplicated or incomplete startup settings fail
closed. Rebuild the optional adapter to use the explicit-library profile.
Relocated project resets restart the worker when its registry path changes;
this cost is counted, not hidden as incremental reuse.

Fresh validation never treats `--allow-unsolved-metas` or
`--allow-incomplete-matches` as proof acceptance. Other checking waivers are
rejected unless explicitly allowed by the policy. This applies to command,
library and source options, not just the edited declaration.

This low-level library contract does not yet expose project configuration
through every public search/editor entry point or qualify every Agda version.
