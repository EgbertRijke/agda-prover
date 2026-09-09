# Streaming JSON input v1

`codec_json.load_chunks(chunks)` accepts an iterable of UTF-8 byte chunks and
returns the same JSON value as `codec_json.loads` for a complete valid document.
Empty chunks, split UTF-8 code points and tokens split at arbitrary boundaries
are supported. There is no limit on nesting, document size or scalar size beyond
the caller's physical resource allowance. This API does not own or close the
input source.

The shared iterative grammar rejects duplicate object keys, nonfinite numbers,
trailing commas, extra values, invalid escapes and incomplete documents. UTF-8
must be valid. Invalid JSON raises `ValueError`; in-memory `loads` retains its
`JSONDecodeError` diagnostics, while streaming errors report a source character
offset without retaining the entire document for an error message.

Decoded containers are exact, not a partial or filtered observation. The input
reader retains only its current decoded chunk and any scalar spanning chunks,
in addition to the result and explicit nesting stack. Large scalars are scanned
once before native scalar decoding, avoiding repeated prefix reparsing.
Traversal and refill poll the existing resource envelope. I/O charging belongs
to the source owner, not to the pure codec. Cancellation/resource exhaustion
propagates without a partial result or a renewed allowance.

File-opening policy, descriptor cleanup and byte charging remain the source
owner's responsibility. Canonical encodings, persisted content identities,
schemas and solver ranking policies are unchanged; no typed validation or
proof check is bypassed.
