"""Product-only contracts for the optional native scope boundary."""

from __future__ import annotations

import copy
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import (
    EnvironmentId,
    ModuleId,
    SourceRevision,
    StateToken,
)
from agdaprover.bridge.live_scope import (
    DEPENDENCY_MARKER,
    DEPENDENCY_POLICY,
    DEPENDENCY_SCHEMA,
    FEATURE_POLICY,
    MARKER,
    RESOURCE_SCHEMA,
    SCHEMA,
    TYPE_VIEW_POLICY,
    decode_resource_limit,
    decode_scope,
    exclusions_payload,
)
from agdaprover.validation import validate_candidate

TOKEN = StateToken(
    EnvironmentId("a" * 64),
    SourceRevision("b" * 64),
    ModuleId("Test", "Test.agda"),
    1,
    1,
    "c" * 64,
)


def wire(dependencies=False):
    features = {"result_head": "global:1:0", "symbols": ["1:0"], "arity": 0}
    value = {
        "kind": "AgdaProverScope",
        "schema_version": DEPENDENCY_SCHEMA if dependencies else SCHEMA,
        "feature_policy": FEATURE_POLICY,
        "type_view_policy": TYPE_VIEW_POLICY,
        "interaction_id": 0,
        "excluded_names": [],
        "omitted_aliases": {"ambiguous": ["clash"], "unnameable": ["_"]},
        "target": features,
        "declarations": [
            {"id": "1:1", "aliases": ["Left.clash"], "type": "U", "features": features}
        ],
        "structure_nodes": 2,
        "output_bytes": 8_388_608,
    }
    if dependencies:
        value.update(dependency_policy=DEPENDENCY_POLICY, dependency_nodes=0)
        value["declarations"][0]["rhs_dependencies"] = None
    return value


def read(value, dependencies=False):
    return decode_scope(
        value,
        state=TOKEN,
        goal_id=0,
        excluded_names=frozenset(),
        adapter_sha256="d" * 64,
        output_bytes=8_388_608,
        include_dependencies=dependencies,
    )


class NameableScopeContracts(unittest.TestCase):
    def test_omissions_are_not_ranking_features_but_bind_observation_identity(self):
        for dependencies in (False, True):
            first = read(wire(dependencies), dependencies)
            changed = wire(dependencies)
            changed["omitted_aliases"] = {"ambiguous": [], "unnameable": []}
            second = read(changed, dependencies)
            self.assertNotEqual(first.allowed.scope_id, second.allowed.scope_id)
            self.assertEqual(first.allowed.premises, second.allowed.premises)
            self.assertEqual(first.query.features, second.query.features)
            self.assertEqual(first.query.tokens, second.query.tokens)
            self.assertEqual(first.type_views, second.type_views)

    def test_malformed_or_overlapping_omissions_fail_before_hashing(self):
        for dependencies in (False, True):
            for omissions in (
                None,
                [],
                {},
                {"extra": []},
                {"ambiguous": None, "unnameable": []},
                *(
                    {"ambiguous": [], "unnameable": row}
                    for row in (
                        [None],
                        [[]],
                        [""],
                        ["x\0y"],
                        ["_", "_"],
                        ["z", "a"],
                        ["Left.clash"],
                    )
                ),
                {"ambiguous": ["_"], "unnameable": ["_"]},
            ):
                changed = wire(dependencies)
                changed["omitted_aliases"] = omissions
                with self.subTest(dependencies=dependencies, omissions=omissions):
                    with patch(
                        "agdaprover.bridge.live_scope.stable_hash",
                        side_effect=AssertionError("hashed invalid omission"),
                    ):
                        with self.assertRaises(ValueError):
                            read(changed, dependencies)

    def test_current_wire_requires_nameability_evidence_and_exact_version(self):
        for dependencies in (False, True):
            value = wire(dependencies)
            missing = copy.deepcopy(value)
            del missing["omitted_aliases"]
            with self.assertRaises(ValueError):
                read(missing, dependencies)
            for version in (
                "agdaprover.live-scope.v2",
                "agdaprover.live-scope.v3",
                "agdaprover.live-scope.v4",
                "agdaprover.live-scope.v5",
                "unknown",
                None,
                [],
            ):
                with self.assertRaises(ValueError):
                    read({**value, "schema_version": version}, dependencies)

    def test_output_reservation_is_required_and_exact(self):
        for dependencies in (False, True):
            value = wire(dependencies)
            del value["output_bytes"]
            with self.assertRaises(ValueError):
                read(value, dependencies)
            for limit in (True, 0, -1, 8_388_609, "8388608", None):
                with self.assertRaises(ValueError):
                    read({**value, "output_bytes": limit}, dependencies)
            for limit in (True, 0, -1, 1.5, None):
                with self.assertRaises(ValueError):
                    exclusions_payload(frozenset(), output_bytes=limit)

    def test_large_exclusions_are_valid_and_serialized_without_truncation(self):
        excluded = frozenset([*(f"unused{i}" for i in range(5001)), "λ" * 65537])
        for dependencies, marker in ((False, MARKER), (True, DEPENDENCY_MARKER)):
            payload = exclusions_payload(
                excluded,
                output_bytes=32 * 1024 * 1024,
                include_dependencies=dependencies,
            )
            self.assertTrue(payload.startswith(marker))
            self.assertEqual(
                json.loads(payload[len(marker) :]),
                {
                    "excluded_names": sorted(excluded),
                    "output_bytes": 32 * 1024 * 1024,
                },
            )

    def test_resource_refusal_is_closed_and_bound_to_request(self):
        for dependencies in (False, True):
            value = {
                "kind": "AgdaProverScopeResource",
                "schema_version": RESOURCE_SCHEMA,
                "request_schema": DEPENDENCY_SCHEMA if dependencies else SCHEMA,
                "interaction_id": 3,
                "resource": "output-bytes",
                "limit": 1000,
                "observed_lower_bound": 1001,
            }

            def decode(data, dependencies=dependencies):
                return decode_resource_limit(
                    data,
                    goal_id=3,
                    output_bytes=1000,
                    include_dependencies=dependencies,
                )

            self.assertEqual(decode(value), 1001)
            for field in value:
                changed = dict(value)
                del changed[field]
                with self.assertRaises(ValueError):
                    decode(changed)
            for field, wrong in (
                ("kind", "AgdaProverScope"),
                ("schema_version", "unknown"),
                ("request_schema", "old"),
                ("interaction_id", 4),
                ("interaction_id", True),
                ("resource", "nodes"),
                ("limit", 1001),
                ("limit", True),
                ("observed_lower_bound", 1000),
                ("observed_lower_bound", True),
                ("declarations", []),
            ):
                with (
                    self.subTest(field=field, wrong=wrong),
                    self.assertRaises(ValueError),
                ):
                    decode({**value, field: wrong})


SOURCE = """{-# OPTIONS --safe --without-K #-}
module ScopeNames where
data U : Set where
  u : U
_ : U
_ = u
_ : U
_ = u
module Left where
  clash : U
  clash = u
  data D : Set where
    same : D
module Right where
  clash : U
  clash = u
  data D : Set where
    same : D
open Left
open Right
_⊙_ : U → U → U
x ⊙ y = x
module _ (A : Set) where
  named : A → A
  named x = x
goal : U
goal = {!!}
"""
NATIVE = (
    Path(__file__).resolve().parents[1]
    / "native/agda-bridge/target/agdaprover-agda-bridge-2.8"
)


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_SCOPE") == "1" and NATIVE.is_file(),
    "explicit native live-scope test required",
)
class NativeNameableScopeContracts(unittest.TestCase):
    def test_generated_import_paths_do_not_grant_source_scope(self):
        payload = """{-# OPTIONS --safe --without-K #-}
module Payload (X : Set) where
identity : X → X
identity x = x
hidden : X → X
hidden x = x
_◇_ : X → X → X
x ◇ y = x
#marker : X → X
#marker x = x
"""
        for directive, expected, proof in (
            (
                "open import Payload Flag using (identity; _◇_; #marker)",
                {"identity", "_◇_", "#marker"},
                "identity",
            ),
            (
                "import Payload Flag as Active using (identity; _◇_; #marker)",
                {"Active.identity", "Active._◇_", "Active.#marker"},
                "Active.identity",
            ),
        ):
            source = f"""{{-# OPTIONS --safe --without-K #-}}
module ScopeNames where
data Flag : Set where
  off on : Flag
{directive}
goal : Flag → Flag
goal = {{!!}}
"""
            for dependencies in (False, True):
                with (
                    self.subTest(directive=directive, dependencies=dependencies),
                    tempfile.TemporaryDirectory() as directory,
                    patch.dict(
                        os.environ,
                        {
                            "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                            "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                            "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                            "AGDAPROVER_SCOPED_DEPENDENCIES": str(int(dependencies)),
                        },
                    ),
                ):
                    root = Path(directory)
                    path = root / "ScopeNames.agda"
                    path.write_text(source)
                    (root / "Payload.agda").write_text(payload)
                    with AgdaSession(timeout_seconds=10) as session:
                        (goal,) = session.load_module(path)
                        state = session.current_state()
                        scope = session.scoped_retrieval(
                            state,
                            goal_id=goal.goal_id,
                            excluded_names=frozenset(("goal",)),
                        )
                        self.assertIsNotNone(scope)
                        aliases = {a for p in scope.allowed.premises for a in p.aliases}
                        self.assertTrue(expected <= aliases, aliases)
                        self.assertFalse(
                            any(a.startswith(".#") for a in aliases), aliases
                        )
                        self.assertFalse(
                            any(a.endswith("hidden") for a in aliases), aliases
                        )
                        self.assertIsNotNone(
                            session.infer_type(
                                state, goal_id=goal.goal_id, expression=proof
                            )
                        )
                        self.assertEqual(session.current_state(), state)
                    checked, trust = validate_candidate(
                        path, goal, proof, timeout_seconds=10
                    )
                    self.assertTrue(checked["checked"], checked)
                    self.assertTrue(checked["fresh_process"])
                    self.assertEqual(trust["admitted_axioms_and_primitives"], [])
                    self.assertEqual(path.read_text(), source)
                    self.assertEqual((root / "Payload.agda").read_text(), payload)

    def test_legal_names_overloads_and_fresh_validation_survive_omissions(self):
        for dependencies in (False, True):
            with (
                tempfile.TemporaryDirectory() as directory,
                patch.dict(
                    os.environ,
                    {
                        "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                        "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                        "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                        "AGDAPROVER_SCOPED_DEPENDENCIES": "1" if dependencies else "0",
                    },
                ),
            ):
                path = Path(directory) / "ScopeNames.agda"
                path.write_text(SOURCE)
                with AgdaSession(timeout_seconds=10) as session:
                    (goal,) = session.load_module(path)
                    state = session.current_state()
                    scope = session.scoped_retrieval(
                        state, goal_id=goal.goal_id, excluded_names=frozenset(("goal",))
                    )
                    self.assertIsNotNone(scope)
                    aliases = [a for p in scope.allowed.premises for a in p.aliases]
                    self.assertTrue(
                        {"Left.clash", "Right.clash", "_⊙_", "named"} <= set(aliases)
                    )
                    self.assertEqual(aliases.count("same"), 2)
                    self.assertFalse({"_", "clash", "D", "goal"} & set(aliases))
                    self.assertEqual(scope.dependencies is not None, dependencies)
                    self.assertEqual(session.current_state(), state)
                    excluded = session.scoped_retrieval(
                        state,
                        goal_id=goal.goal_id,
                        excluded_names=frozenset(("goal", "clash")),
                    )
                    self.assertFalse(
                        any(
                            a.endswith(".clash")
                            for p in excluded.allowed.premises
                            for a in p.aliases
                        )
                    )
                    self.assertEqual(session.current_state(), state)
                checked, trust = validate_candidate(
                    path, goal, "Left.clash", timeout_seconds=10
                )
                self.assertTrue(checked["checked"], checked)
                self.assertTrue(checked["fresh_process"])
                self.assertEqual(trust["admitted_axioms_and_primitives"], [])
                self.assertEqual(path.read_text(), SOURCE)


if __name__ == "__main__":
    unittest.main()
