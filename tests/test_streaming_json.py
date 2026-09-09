"""Chunk boundaries cannot change JSON values, trust checks or resource limits."""

from __future__ import annotations

import json
import random
import tracemalloc
import unittest
from itertools import chain, repeat
from unittest.mock import patch

from agdaprover import codec_json


def chunks(payload: bytes, width: int):
    for offset in range(0, len(payload), width):
        yield payload[offset : offset + width]


class StreamingJsonTests(unittest.TestCase):
    def test_every_boundary_in_strings_escapes_numbers_and_unicode(self):
        values = [
            None,
            True,
            False,
            0,
            -10,
            3.125,
            -0.0,
            1e-80,
            1e80,
            'λ😀\n"\\\t',
            [[], {}],
            {"λ": ["😀", '\\"', "\r\n", True, None, -1e-20]},
        ]
        for value in values:
            payload = json.dumps(value, ensure_ascii=False, indent=2).encode()
            for offset in range(len(payload) + 1):
                with self.subTest(value=value, offset=offset):
                    self.assertEqual(
                        codec_json.load_chunks(
                            (b"", payload[:offset], b"", payload[offset:], b"")
                        ),
                        value,
                    )
            self.assertEqual(codec_json.load_chunks(chunks(payload, 1)), value)
        self.assertEqual(
            codec_json.load_chunks(chunks(b'"\\ud83d\\ude00\\u03bb"', 1)), "😀λ"
        )

    def test_randomized_documents_match_in_memory_decoder(self):
        rng = random.Random(381)

        def value(depth=0):
            scalar = rng.choice(
                (None, True, False, rng.randrange(-999, 999), "λ😀\\x\t\n")
            )
            if depth == 6 or rng.random() < 0.5:
                return scalar
            if rng.random() < 0.5:
                return [value(depth + 1) for _ in range(rng.randrange(5))]
            return {str(i): value(depth + 1) for i in range(rng.randrange(5))}

        for _ in range(150):
            expected = value()
            payload = json.dumps(expected, ensure_ascii=False).encode()
            result = codec_json.load_chunks(chunks(payload, rng.randrange(1, 37)))
            self.assertEqual(result, codec_json.loads(payload))
            self.assertEqual(result, expected)

    def test_deep_wide_and_empty_documents(self):
        payload = ("[" * 5000 + '"λ😀"' + "]" * 5000).encode()
        result = codec_json.load_chunks(chunks(payload, 17))
        self.assertEqual(codec_json.dumps(result, compact=True).encode(), payload)
        expected = list(range(10000))
        self.assertEqual(
            codec_json.load_chunks(chunks(json.dumps(expected).encode(), 257)), expected
        )
        for source in ((), (b"",), (b" \n", b"\r\t")):
            with self.assertRaises(ValueError):
                codec_json.load_chunks(source)

    def test_spanning_scalar_is_decoded_once_not_once_per_prefix(self):
        expected = "x" * 100000 + "😀" + '\\"' * 1000
        payload = json.dumps(expected, ensure_ascii=False).encode()
        decoder = json.JSONDecoder()
        with patch.object(codec_json, "_DECODER", wraps=decoder) as counted:
            self.assertEqual(codec_json.load_chunks(chunks(payload, 19)), expected)
            self.assertEqual(counted.raw_decode.call_count, 1)

    def test_malformed_grammar_is_rejected_at_every_boundary(self):
        for payload in (
            b"[",
            b"[1,]",
            b'{"a":1,}',
            b'{"a" 1}',
            b"[}",
            b"1 2",
            b"[1 2]",
            b'{"a":1,"a":2}',
            b"NaN",
            b"Infinity",
            b"1e9999",
            b"01",
            b"1e",
            b"truefalse",
            b'"bad\\q"',
            b'"bad\n"',
            b'"\\u0z00"',
            b'"abc\\',
            b'"abc',
            b"[true false]",
            b"{}{}",
        ):
            for offset in range(len(payload) + 1):
                with self.subTest(payload=payload, offset=offset):
                    with self.assertRaises(ValueError):
                        codec_json.load_chunks((payload[:offset], payload[offset:]))

    def test_utf8_and_chunk_types_remain_strict(self):
        for payload in (b'"\xff"', b'"\xf0\x9f', b'"\xed\xa0\x80"'):
            with self.assertRaises(UnicodeError):
                codec_json.load_chunks(chunks(payload, 1))
        for chunk in (None, "text", 1, bytearray(b"null")):
            with self.assertRaises(TypeError):
                codec_json.load_chunks((chunk,))
        for payload in (None, 1, bytearray(b"null"), []):
            with self.assertRaises(TypeError):
                codec_json.loads(payload)

    def test_cancellation_and_source_failures_propagate_without_draining(self):
        observed = []

        def source():
            while True:
                observed.append(len(observed))
                yield b" " * 100

        def stop():
            if len(observed) == 3:
                raise RuntimeError("cancelled")

        with patch.object(codec_json, "checkpoint", side_effect=stop):
            with self.assertRaisesRegex(RuntimeError, "cancelled"):
                codec_json.load_chunks(source())
        self.assertEqual(len(observed), 3)

        def broken():
            yield b"["
            raise OSError("input failed")

        with self.assertRaisesRegex(OSError, "input failed"):
            codec_json.load_chunks(broken())

    def test_in_memory_error_keeps_full_document_and_character_offset(self):
        payload = '["λ",\n1 2]'
        with self.assertRaises(json.JSONDecodeError) as raised:
            codec_json.loads(payload)
        self.assertEqual(raised.exception.doc, payload)
        self.assertEqual(raised.exception.pos, payload.index("2"))
        with self.assertRaisesRegex(ValueError, "source character 9"):
            codec_json.load_chunks((b" " * 8, b"[}"))

    def test_large_wire_with_small_value_does_not_retain_consumed_chunks(self):
        # 64 MiB on the wire, ending in a four-byte character. A whole-input
        # Unicode string would need up to 256 MiB despite the tiny JSON value.
        source = chain(repeat(b" " * 65536, 1024), ('"😀"'.encode(),))
        tracemalloc.start()
        try:
            self.assertEqual(codec_json.load_chunks(source), "😀")
            _current, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertLess(peak, 2 * 1024**2)
