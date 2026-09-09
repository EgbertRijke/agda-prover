"""Product-only contracts for the optional native scope boundary."""

from __future__ import annotations

import copy
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
    DEPENDENCY_POLICY,
    DEPENDENCY_SCHEMA,
    FEATURE_POLICY,
    SCHEMA,
    TYPE_VIEW_POLICY,
    decode_scope,
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
                "unknown",
                None,
                [],
            ):
                with self.assertRaises(ValueError):
                    read({**value, "schema_version": version}, dependencies)


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
