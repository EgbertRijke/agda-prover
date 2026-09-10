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
