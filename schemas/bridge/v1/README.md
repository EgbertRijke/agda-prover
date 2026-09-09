# Stage 1 bridge schemas

These Draft 2020-12 schemas freeze the first public, version-neutral kernel
boundary. Runtime decoding is dependency-free and rejects unknown major
versions and unknown fields. The operation schema is a closed 20-variant sum:
one request and one result for each operation. Runtime decoding in
`agdaprover.bridge.operations` applies the same exact-field rule and verifies
identity-bearing checksums. Proof states and diagnostics have standalone
schemas because they are persisted in traces and evidence bundles.
