"""Record construction does not require a nameable constructor or type head."""

from __future__ import annotations

import os
import tempfile
import unittest
from contextlib import contextmanager
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaBridgeError, AgdaSession
from agdaprover.bridge.contracts import (
    BridgeBudget,
    BridgeError,
    BridgeFailure,
    InteractionId,
)
from agdaprover.bridge.operations import OpenProjectRequest
from agdaprover.bridge.record_introduction import KIND, SCHEMA, decode, request_payload
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter, RawEvent
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix

NATIVE = (
    Path(__file__).resolve().parents[1]
    / "native/agda-bridge/target/agdaprover-agda-bridge-2.8"
)
HEADER = "{-# OPTIONS --safe --without-K #-}\n"
CARRIER = (
    HEADER
    + """module Carrier where
record Package (A : Set) : Set where
  constructor wrap
  field contents : A
record Dependent (A : Set) (B : A → Set) : Set where
  constructor bundle
  field
    first : A
    second : B first
record Hidden : Set₁ where
  constructor hide
  field
    {Carrier} : Set
    value : Carrier
record WithInstance (A : Set) : Set where
  constructor infer
  field
    {{element}} : A
    witness : A
data Flag : Set where
  off on : Flag
"""
)
SURFACE = (
    HEADER
    + """module Surface where
open import Carrier using (Package; Dependent; Hidden; WithInstance; Flag)
Bundle : Set → Set
Bundle = Package
Family : (A : Set) → (A → Set) → Set
Family = Dependent
Concealed : Set₁
Concealed = Hidden
Choice : Set
Choice = Flag
InstanceBundle : Set → Set
InstanceBundle = WithInstance
abstract
  Opaque : Set → Set
  Opaque = Package
"""
)
SIMPLE = (
    HEADER
    + """module Client where
open import Surface
module _ {A : Set} (a : A) where
  assemble : Bundle A
  assemble = {!!}
"""
)


def wire(**changes):
    return {
        "kind": KIND,
        "schema_version": SCHEMA,
        "interaction_id": 0,
        "output_bytes": 4096,
        "status": "record",
        "expression": "record { contents = ? }",
        "required_bytes": None,
        **changes,
    }


class RecordIntroductionProtocolTests(unittest.TestCase):
    def test_closed_response_and_request_identity(self):
        self.assertEqual(
            decode(wire(), goal_id=0, output_bytes=4096).expression,
            "record { contents = ? }",
        )
        for key, value in (
            ("kind", "other"),
            ("schema_version", "v0"),
            ("interaction_id", True),
            ("interaction_id", 1),
            ("output_bytes", True),
            ("output_bytes", 2048),
            ("status", "verified"),
            ("expression", ""),
            ("expression", "x\0y"),
            ("expression", 7),
            ("required_bytes", 0),
            ("extra", 0),
        ):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                decode(wire(**{key: value}), goal_id=0, output_bytes=4096)
        for reservation in (True, 0, -1, "4096"):
            with self.assertRaises(ValueError):
                request_payload(reservation)
        with self.assertRaises(ValueError):
            decode(wire(), goal_id=True, output_bytes=4096)

    def test_missing_record_and_resource_refusal_are_distinct(self):
        absent = decode(
            wire(status="not-record", expression=None), goal_id=0, output_bytes=4096
        )
        limited = decode(
            wire(status="output-limited", expression=None, required_bytes=5000),
            goal_id=0,
            output_bytes=4096,
        )
        self.assertIsNone(absent.expression)
        self.assertIsNone(absent.required_bytes)
        self.assertEqual(limited.required_bytes, 5000)
        for required in (True, 4096, None):
            with self.assertRaises(ValueError):
                decode(
                    wire(
                        status="output-limited",
                        expression=None,
                        required_bytes=required,
                    ),
                    goal_id=0,
                    output_bytes=4096,
                )


@contextmanager
def fixture(source=SIMPLE, *, enabled=True):
    with (
        tempfile.TemporaryDirectory() as directory,
        patch.dict(
            os.environ,
            {
                "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                "AGDAPROVER_STRUCTURAL_RECORD_INTRO": "1" if enabled else "0",
                "AGDAPROVER_SCOPED_RETRIEVAL": "0",
                "AGDAPROVER_SCOPED_DEPENDENCIES": "0",
                "AGDAPROVER_SCOPED_QUERY_VIEWS": "0",
                "AGDAPROVER_SCOPED_TYPE_SPINE_HEADS": "0",
                "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "0",
            },
        ),
    ):
        root = Path(directory)
        (root / "Carrier.agda").write_text(CARRIER)
        (root / "Surface.agda").write_text(SURFACE)
        path = root / "Client.agda"
        path.write_text(source)
        yield path
        if path.read_text() != source:
            raise AssertionError("search changed the user's file")


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_RECORD_INTRO") == "1" and NATIVE.is_file(),
    "explicit native record introduction test required",
)
class NativeRecordIntroductionTests(unittest.TestCase):
    def test_instance_fields_remain_solvable_obligations(self):
        with fixture(SIMPLE.replace("Bundle A", "InstanceBundle A")) as path:
            result = prove_joint_prefix(
                TaskSpec(
                    path,
                    goal_id=0,
                    max_candidates=120,
                    max_verifier_calls=1000,
                    timeout_seconds=15,
                )
            )
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertTrue(result.validation["fresh_process"])

    def test_record_literal_is_retained_in_branch_replay(self):
        with fixture() as path, AgdaSession(timeout_seconds=20) as session:
            goal = session.inspect_goal(session.load_module(path)[0])
            parent = session.current_state()
            introduced = session.commit_proof_action(
                parent, kind="refine", goal_id=goal.goal_id, expression=""
            )
            self.assertTrue(introduced.accepted)
            self.assertIn("record", introduced.preview)
            (field,) = introduced.generated_goals
            completed = session.commit_proof_action(
                introduced.child_state,
                kind="give",
                goal_id=field.goal_id,
                expression="a",
            )
            self.assertTrue(completed.accepted)
            self.assertEqual(len(session.inspect_state(parent)), 1)
            self.assertEqual(
                session.internal_obligation_counts(completed.child_state), (0, 0)
            )
            self.assertEqual(session.inspect_state(completed.child_state), ())

    def test_nameable_constructor_does_not_use_the_fallback(self):
        source = SIMPLE.replace(
            "open import Surface", "open import Carrier\nopen import Surface"
        )
        with fixture(source) as path, AgdaSession(timeout_seconds=20) as session:
            goal = session.inspect_goal(session.load_module(path)[0])
            with patch.object(
                ConformingKernelSession,
                "search_record_introduction",
                side_effect=AssertionError("unexpected fallback"),
            ):
                result = session.commit_proof_action(
                    session.current_state(),
                    kind="refine",
                    goal_id=goal.goal_id,
                    expression="",
                )
            self.assertTrue(result.accepted)

    def test_alias_fallback_is_opt_in_and_freshly_verified(self):
        for enabled in (False, True):
            with self.subTest(enabled=enabled), fixture(enabled=enabled) as path:
                result = prove_joint_prefix(
                    TaskSpec(
                        path,
                        goal_id=0,
                        max_candidates=120,
                        max_verifier_calls=1000,
                        timeout_seconds=15,
                    )
                )
                self.assertEqual(
                    result.status,
                    "verified" if enabled else "unsolved",
                    result.diagnostics,
                )
                if enabled:
                    self.assertTrue(result.validation["fresh_process"])
                    self.assertTrue(result.validation["checked"])
                    self.assertEqual(
                        result.trust_report["admitted_axioms_and_primitives"], []
                    )
                    self.assertGreater(result.to_dict()["verifier_budget"]["used"], 0)

    def test_dependent_fields_use_the_preceding_substitution(self):
        source = (
            HEADER
            + """module Client where
open import Surface
module _ {A : Set} {B : A → Set} (a : A) (b : B a) where
  assemble : Family A B
  assemble = {!!}
"""
        )
        with fixture(source) as path:
            result = prove_joint_prefix(
                TaskSpec(
                    path,
                    goal_id=0,
                    max_candidates=120,
                    max_verifier_calls=1000,
                    timeout_seconds=15,
                )
            )
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertTrue(result.validation["fresh_process"])

    def test_query_is_observational_and_preserves_hidden_obligations(self):
        source = (
            HEADER
            + """module Client where
open import Surface
first : Concealed
first = {!!}
second : Choice
second = {!!}
third : Opaque Choice
third = {!!}
"""
        )
        with fixture(source) as path, ConformingKernelSession() as session:
            budget = BridgeBudget(wall_seconds=20, cpu_seconds=20)
            opened = session.open_project(OpenProjectRequest(path), budget)
            self.assertIn("record-introduction", opened.capabilities.operations)
            self.assertIn("+record-introduction-v1:", opened.capabilities.adapter)
            parent = session.load_module(
                opened.project, opened.root_module, opened.source_revision, budget
            ).transition.child_state
            before = session.inspect_goals(parent, budget).state.to_dict()
            literal = session.search_record_introduction(
                parent, InteractionId(0), budget
            )
            self.assertIn("Carrier = ?", literal)
            self.assertIn("value = ?", literal)
            for point in (1, 2):
                self.assertIsNone(
                    session.search_record_introduction(
                        parent, InteractionId(point), budget
                    )
                )
            self.assertEqual(
                session.search_record_introduction(parent, InteractionId(0), budget),
                literal,
            )
            after = session.inspect_goals(parent, budget).state.to_dict()
            for key in (
                "goals",
                "metas",
                "constraints",
                "proof_dag",
                "structural_hash",
            ):
                self.assertEqual(before[key], after[key])
            _command, response = session.transport.command(
                session._source_for(parent.module_id),
                Agda28Adapter().module_contents(0, request_payload(1)),
                transactional=True,
            )
            (refusal,) = [e.value for e in response.events if e.kind == KIND]
            self.assertGreater(
                decode(refusal, goal_id=0, output_bytes=1).required_bytes, 1
            )
            for events, failure in (
                ((), BridgeFailure.PROTOCOL_FAILURE),
                (
                    (
                        RawEvent(
                            KIND,
                            {
                                **refusal,
                                "output_bytes": budget.output_bytes,
                                "required_bytes": budget.output_bytes + 1,
                            },
                        ),
                    ),
                    BridgeFailure.RESOURCE_EXHAUSTED,
                ),
                (response.events * 2, BridgeFailure.PROTOCOL_FAILURE),
            ):
                with patch.object(
                    session.transport,
                    "command",
                    return_value=(_command, replace(response, events=events)),
                ):
                    with self.assertRaises(BridgeError) as rejected:
                        session.search_record_introduction(
                            parent, InteractionId(0), budget
                        )
                    self.assertEqual(rejected.exception.failure, failure)
            self.assertEqual(
                session.search_record_introduction(parent, InteractionId(0), budget),
                literal,
            )
            with self.assertRaises(BridgeError) as invalid:
                session.search_record_introduction(parent, InteractionId(99), budget)
            self.assertEqual(invalid.exception.diagnostic.code, "record-goal-not-open")

    def test_enabled_without_adapter_is_explicitly_unsupported(self):
        with (
            fixture() as path,
            patch.dict(os.environ, {"AGDAPROVER_DISABLE_AGDA_BRIDGE": "1"}),
        ):
            with (
                self.assertRaises(AgdaBridgeError) as caught,
                AgdaSession(timeout_seconds=10) as session,
            ):
                session.load_module(path)
            self.assertIn("record", str(caught.exception).lower())
