"""Explicit native capacity canaries; no library corpus or solver special cases."""

from __future__ import annotations

import os
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import (
    BridgeBudget,
    BridgeError,
    BridgeFailure,
    InteractionId,
)
from agdaprover.bridge.live_scope import (
    DEPENDENCY_MARKER,
    DEPENDENCY_SCHEMA,
    MARKER,
    RESOURCE_SCHEMA,
    SCHEMA,
    decode_resource_limit,
    exclusions_payload,
)
from agdaprover.bridge.operations import OpenProjectRequest, TermInput
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter, DecodedResponse, RawEvent
from agdaprover.validation import validate_candidate

NATIVE = (
    Path(__file__).resolve().parents[1]
    / "native/agda-bridge/target/agdaprover-agda-bridge-2.8"
)
HEADER = """{-# OPTIONS --safe --without-K #-}
module ScopeCapacity where
data U : Set where
  u : U
"""
GOAL = "goal : U\ngoal = {!!}\n"


@contextmanager
def source_session(
    source,
    *,
    output_bytes=32 * 1024 * 1024,
    dependencies=False,
    query_views=False,
    type_family=False,
    type_heads=False,
):
    with (
        tempfile.TemporaryDirectory() as directory,
        patch.dict(
            os.environ,
            {
                "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                "AGDAPROVER_SCOPED_DEPENDENCIES": "1" if dependencies else "0",
                "AGDAPROVER_SCOPED_QUERY_VIEWS": "1" if query_views else "0",
                "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "1" if type_family else "0",
                "AGDAPROVER_SCOPED_TYPE_SPINE_HEADS": "1" if type_heads else "0",
            },
        ),
    ):
        path = Path(directory) / "ScopeCapacity.agda"
        path.write_text(source)
        budget = BridgeBudget(
            wall_seconds=90,
            cpu_seconds=90,
            output_bytes=output_bytes,
            memory_bytes=2 * 1024 * 1024 * 1024,
        )
        session = ConformingKernelSession()
        try:
            opened = session.open_project(OpenProjectRequest(path), budget)
            loaded = session.load_module(
                opened.project,
                opened.root_module,
                opened.source_revision,
                budget,
            )
            yield path, session, budget, loaded.transition.child_state
        finally:
            closed = session.close()
            if closed.orphan_processes:
                raise AssertionError("live scope leaked an owned process")


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_SCOPE_CAPACITY") == "1" and NATIVE.is_file(),
    "explicit native live-scope capacity test required",
)
class NativeScopeCapacityTests(unittest.TestCase):
    def assert_parent_and_fresh_proof(self, path, session, budget, parent):
        self.assertEqual(
            session.inspect_goals(parent, budget).state.structural_hash,
            parent.structural_hash,
        )
        self.assertTrue(
            session.infer(
                parent, TermInput("u"), budget, interaction_id=InteractionId(0)
            ).accepted
        )
        with AgdaSession(timeout_seconds=10) as checker:
            (goal,) = checker.load_module(path)
        validation, trust = validate_candidate(path, goal, "u", timeout_seconds=10)
        self.assertTrue(validation["checked"], validation)
        self.assertTrue(validation["fresh_process"])
        self.assertEqual(trust["admitted_axioms_and_primitives"], [])

    def test_complete_scope_and_exclusions_beyond_old_cardinalities(self):
        source = HEADER + "".join(f"d{i} : U\nd{i} = u\n" for i in range(5001)) + GOAL
        excluded = frozenset(
            ["goal", "d1", *(f"unused{i}" for i in range(5001)), "λ" * 65537]
        )
        with source_session(source, dependencies=True) as (
            path,
            session,
            budget,
            parent,
        ):
            scope = session.search_scoped_retrieval(
                parent, InteractionId(0), budget, excluded_names=excluded
            )
            aliases = {a for p in scope.allowed.premises for a in p.aliases}
            self.assertGreater(len(scope.allowed.premises), 5000)
            self.assertTrue({f"d{i}" for i in range(5001) if i != 1} <= aliases)
            self.assertFalse(
                {"d1", "ScopeCapacity.d1", "goal", "ScopeCapacity.goal"} & aliases
            )
            self.assertEqual(
                len(scope.dependencies.rhs_references), len(scope.allowed.premises)
            )
            self.assert_parent_and_fresh_proof(path, session, budget, parent)
            self.assertEqual(path.read_text(), source)

    def test_large_normalized_type_and_nodes_use_declared_output_reservation(self):
        source = (
            HEADER
            + """data Pair (A B : Set) : Set where
  pair : A → B → Pair A B
T0 : Set
T0 = U
"""
            + "".join(
                f"T{i} : Set\nT{i} = Pair T{i - 1} T{i - 1}\n" for i in range(1, 18)
            )
            + "large : T17 → T17\nlarge x = x\n"
            + GOAL
        )
        with source_session(source) as (path, session, budget, parent):
            # Exercise native refusal, not a mock or Agda type rejection. The
            # transport's enclosing allowance is larger than this raw request.
            command = Agda28Adapter().module_contents(
                0,
                exclusions_payload(
                    frozenset(("goal",)),
                    output_bytes=1024,
                ),
            )
            _, response = session.transport.command(
                session._source_for(parent.module_id), command, transactional=True
            )
            (refusal,) = [
                e.value for e in response.events if e.kind == "AgdaProverScopeResource"
            ]
            self.assertGreater(
                decode_resource_limit(
                    refusal, goal_id=0, output_bytes=1024, include_dependencies=False
                ),
                1024,
            )
            self.assertFalse(any(e.kind == "AgdaProverScope" for e in response.events))
            scope = session.search_scoped_retrieval(
                parent, InteractionId(0), budget, excluded_names=frozenset(("goal",))
            )
            self.assertGreater(scope.structure_nodes, 250000)
            self.assertGreater(len(dict(scope.declarations())["large"]), 65536)
            self.assert_parent_and_fresh_proof(path, session, budget, parent)

    def test_resource_refusal_maps_to_resource_exhausted_and_preserves_parent(self):
        source = HEADER + "".join(f"d{i} : U\nd{i} = u\n" for i in range(80)) + GOAL
        for dependencies in (False, True):
            with source_session(
                source, output_bytes=8192, dependencies=dependencies
            ) as (path, session, budget, parent):
                with self.assertRaises(BridgeError) as error:
                    session.search_scoped_retrieval(parent, InteractionId(0), budget)
                self.assertEqual(
                    error.exception.failure, BridgeFailure.RESOURCE_EXHAUSTED
                )
                self.assertEqual(
                    error.exception.diagnostic.code, "live-scope-output-budget"
                )
                refusal = {
                    "kind": "AgdaProverScopeResource",
                    "schema_version": RESOURCE_SCHEMA,
                    "request_schema": DEPENDENCY_SCHEMA if dependencies else SCHEMA,
                    "interaction_id": 0,
                    "resource": "output-bytes",
                    "limit": budget.output_bytes,
                    "observed_lower_bound": budget.output_bytes + 1,
                }
                event = RawEvent("AgdaProverScopeResource", refusal)
                for events in (
                    (event, event),
                    (event, RawEvent("AgdaProverScope", {})),
                    (RawEvent(event.kind, {**refusal, "limit": 1}),),
                ):
                    with (
                        patch.object(
                            session.transport,
                            "command",
                            return_value=(None, DecodedResponse(events, "0" * 64, 0)),
                        ),
                        self.assertRaises(BridgeError) as malformed,
                    ):
                        session.search_scoped_retrieval(
                            parent, InteractionId(0), budget
                        )
                    self.assertEqual(
                        malformed.exception.failure, BridgeFailure.PROTOCOL_FAILURE
                    )
                self.assert_parent_and_fresh_proof(path, session, budget, parent)

    def test_complete_utf8_output_can_exceed_the_former_16_mib_ceiling(self):
        # Exclusions are echoed as provenance, not silently discarded because
        # they match no declaration. This stresses framing without adding a
        # giant mathematical type or consulting a reference proof.
        excluded = frozenset(("λ" * (8 * 1024 * 1024 + 1),))
        with source_session(HEADER + GOAL) as (path, session, budget, parent):
            before = session.transport.cost.bytes_read
            scope = session.search_scoped_retrieval(
                parent, InteractionId(0), budget, excluded_names=excluded
            )
            self.assertGreater(
                session.transport.cost.bytes_read - before, 16 * 1024 * 1024
            )
            self.assertIn("u", dict(scope.declarations()))
            self.assert_parent_and_fresh_proof(path, session, budget, parent)

    def test_native_rejects_malformed_requests_without_publishing_a_scope(self):
        source = HEADER + GOAL
        with source_session(source) as (path, session, budget, parent):
            for marker in (MARKER, DEPENDENCY_MARKER):
                for payload in (
                    "[]",
                    '{"excluded_names":[],"output_bytes":true}',
                    '{"excluded_names":[],"output_bytes":0}',
                    '{"excluded_names":["z","a"],"output_bytes":1024}',
                    '{"excluded_names":["a","a"],"output_bytes":1024}',
                    '{"excluded_names":[""],"output_bytes":1024}',
                    '{"excluded_names":["x\\u0000y"],"output_bytes":1024}',
                    '{"excluded_names":[],"output_bytes":1024,"extra":0}',
                ):
                    _, response = session.transport.command(
                        session._source_for(parent.module_id),
                        Agda28Adapter().module_contents(0, marker + payload),
                        transactional=True,
                    )
                    error = Agda28Adapter().error_payload(response)
                    self.assertIsNotNone(error)
                    self.assertIn("invalid-scope-request", str(error))
                    self.assertFalse(
                        any(
                            e.kind.startswith("AgdaProverScope")
                            for e in response.events
                        )
                    )
            self.assert_parent_and_fresh_proof(path, session, budget, parent)
