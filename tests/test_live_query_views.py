"""Closed protocol and real Agda canaries for optional query normalization."""

from __future__ import annotations

import copy
import os
import unittest

from test_live_scope_capacity import HEADER, NATIVE, source_session
from test_live_scope_protocol import TOKEN, wire

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import InteractionId
from agdaprover.bridge.live_scope import (
    DEPENDENCY_QUERY_VIEWS_MARKER,
    QUERY_VIEWS_MARKER,
    decode_resource_limit,
    decode_scope,
    exclusions_payload,
    scope_schema,
)
from agdaprover.bridge.operations import TermInput
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter
from agdaprover.retrieval import QUERY_NORMALIZATION_POLICY
from agdaprover.validation import validate_candidate


def normalized_wire(dependencies=False):
    value = wire(dependencies)
    value["schema_version"] = scope_schema(dependencies, True)
    value["structure_nodes"] += 2
    value["normalized_query"] = {
        "policy": QUERY_NORMALIZATION_POLICY,
        "features": {
            "result_head": "local:0",
            "symbols": ["1:1", "hidden"],
            "arity": 2,
        },
        "structure_nodes": 2,
        "conversion_checked": True,
    }
    return value


def read(value, dependencies=False, requested=True):
    return decode_scope(
        value,
        state=TOKEN,
        goal_id=0,
        excluded_names=frozenset(),
        adapter_sha256="d" * 64,
        output_bytes=8_388_608,
        include_dependencies=dependencies,
        normalize_query=requested,
    )


class QueryViewProtocolTests(unittest.TestCase):
    def test_exact_capability_and_allowed_tokens(self):
        for deps, marker in (
            (False, QUERY_VIEWS_MARKER),
            (True, DEPENDENCY_QUERY_VIEWS_MARKER),
        ):
            value = normalized_wire(deps)
            scope = read(value, deps)
            self.assertEqual(scope.query.normalized.features.result_head, "local:0")
            self.assertEqual(scope.query.normalized.features.arity, 2)
            self.assertEqual(scope.query.normalized.tokens, ("clash", "left"))
            self.assertEqual(scope.query.tokens, ())
            self.assertEqual(scope.query.features.symbols, ("1:0",))
            self.assertTrue(
                exclusions_payload(
                    frozenset(),
                    output_bytes=8192,
                    include_dependencies=deps,
                    normalize_query=True,
                ).startswith(marker)
            )
            with self.assertRaises(ValueError):
                read(value, deps, requested=False)
            with self.assertRaises(ValueError):
                read(wire(deps), deps)
            changed = copy.deepcopy(value)
            changed["normalized_query"]["features"]["arity"] += 1
            self.assertNotEqual(read(changed, deps).query_id, scope.query_id)

    def test_partial_unchecked_or_malformed_views_fail_closed(self):
        original = normalized_wire()
        for key in original["normalized_query"]:
            value = copy.deepcopy(original)
            del value["normalized_query"][key]
            with self.assertRaises(ValueError):
                read(value)
        for key, wrong in (
            ("policy", "partial"),
            ("conversion_checked", False),
            ("conversion_checked", 1),
            ("structure_nodes", True),
            ("structure_nodes", 0),
            ("structure_nodes", 9999),
            ("features", {}),
        ):
            value = copy.deepcopy(original)
            value["normalized_query"][key] = wrong
            with self.assertRaises(ValueError):
                read(value)
        with self.assertRaises(ValueError):
            exclusions_payload(frozenset(), output_bytes=8192, normalize_query=1)


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_QUERY_VIEWS") == "1" and NATIVE.is_file(),
    "explicit native query-view tests required",
)
class NativeQueryViewTests(unittest.TestCase):
    def test_resource_refusal_does_not_publish_partial_views_or_change_parent(self):
        source = (
            HEADER
            + "".join(f"d{i} : U\nd{i} = u\n" for i in range(40))
            + "goal : U\ngoal = {!!}\n"
        )
        for deps in (False, True):
            with source_session(source, dependencies=deps, query_views=True) as (
                _path,
                session,
                budget,
                parent,
            ):
                payload = exclusions_payload(
                    frozenset(("goal",)),
                    output_bytes=512,
                    include_dependencies=deps,
                    normalize_query=True,
                )
                _, response = session.transport.command(
                    session._source_for(parent.module_id),
                    Agda28Adapter().module_contents(0, payload),
                    transactional=True,
                )
                (refusal,) = [
                    e.value
                    for e in response.events
                    if e.kind == "AgdaProverScopeResource"
                ]
                self.assertGreater(
                    decode_resource_limit(
                        refusal,
                        goal_id=0,
                        output_bytes=512,
                        include_dependencies=deps,
                        normalize_query=True,
                    ),
                    512,
                )
                self.assertFalse(
                    any(e.kind == "AgdaProverScope" for e in response.events)
                )
                with self.assertRaises(ValueError):
                    decode_resource_limit(
                        refusal, goal_id=0, output_bytes=512, include_dependencies=deps
                    )
                self.assertEqual(
                    session.inspect_goals(parent, budget).state.structural_hash,
                    parent.structural_hash,
                )
                complete = session.search_scoped_retrieval(
                    parent,
                    InteractionId(0),
                    budget,
                    excluded_names=frozenset(("goal",)),
                )
                self.assertIsNotNone(complete.query.normalized)

    def test_abstract_definitions_and_unresolved_metas_are_not_opened_or_assigned(self):
        source = (
            HEADER
            + """abstract
  Opaque : Set
  Opaque = U
opaque-goal : Opaque
opaque-goal = {!!}
T : Set
T = {!!}
meta-goal : T
meta-goal = {!!}
"""
        )
        with source_session(source, query_views=True) as (
            _path,
            session,
            budget,
            parent,
        ):
            before = session.inspect_goals(parent, budget).state
            scope = session.search_scoped_retrieval(
                parent,
                InteractionId(0),
                budget,
                excluded_names=frozenset(("opaque-goal", "T", "meta-goal")),
            )
            opaque = next(
                p.declaration_id
                for p in scope.allowed.premises
                if "Opaque" in p.aliases
            )
            self.assertEqual(
                scope.query.normalized.features.result_head, "global:" + opaque
            )
            unresolved = session.search_scoped_retrieval(
                parent,
                InteractionId(2),
                budget,
                excluded_names=frozenset(("opaque-goal", "T", "meta-goal")),
            )
            self.assertIsNone(unresolved.query.normalized.features.result_head)
            self.assertEqual(session.inspect_goals(parent, budget).state, before)

    def test_nested_alias_ranking_and_fresh_proof_in_both_graph_modes(self):
        source = (
            HEADER
            + """Alias : Set
Alias = U
data Box (A : Set) : Set where
  wrap : A → Box A
ready : Box U
ready = wrap u
"""
            + "".join(f"d{i} : Box Alias → Box Alias\nd{i} x = x\n" for i in range(30))
            + "goal : Box Alias\ngoal = {!!}\n"
        )
        for dependencies in (False, True):
            with source_session(
                source, dependencies=dependencies, query_views=True
            ) as (path, session, budget, parent):
                scope = session.search_scoped_retrieval(
                    parent,
                    InteractionId(0),
                    budget,
                    excluded_names=frozenset(("goal",)),
                )
                members = {
                    alias: p.declaration_id
                    for p in scope.allowed.premises
                    for alias in p.aliases
                }
                self.assertIn(members["Alias"], scope.query.features.symbols)
                self.assertNotIn(
                    members["Alias"], scope.query.normalized.features.symbols
                )
                self.assertIn(members["U"], scope.query.normalized.features.symbols)
                result = scope.index().retrieve(scope.query, limit=64)
                item = next(
                    i
                    for i in result.items
                    if i.premise.declaration_id == members["ready"]
                )
                self.assertEqual(item.query_view, "normalized")
                self.assertNotIn("goal", members)
                self.assertEqual(
                    session.inspect_goals(parent, budget).state.structural_hash,
                    parent.structural_hash,
                )
                self.assertTrue(
                    session.infer(
                        parent,
                        TermInput("ready"),
                        budget,
                        interaction_id=InteractionId(0),
                    ).accepted
                )
                self.assertEqual(path.read_text(), source)
                with AgdaSession(timeout_seconds=10) as checker:
                    (goal,) = checker.load_module(path)
                validation, _trust = validate_candidate(
                    path, goal, "ready", timeout_seconds=10
                )
                self.assertTrue(validation["checked"], validation)
                self.assertTrue(validation["fresh_process"])

    def test_open_telescope_coordinates_are_not_closed_binder_indices(self):
        source = (
            HEADER
            + """Apply : {A : Set} → (A → Set) → A → Set
Apply P x = P x
module _ (A : Set) (P : A → Set) (x : A) where
  goal : Apply P x
  goal = {!!}
"""
        )
        with source_session(source, query_views=True) as (
            _path,
            session,
            budget,
            parent,
        ):
            scope = session.search_scoped_retrieval(
                parent, InteractionId(0), budget, excluded_names=frozenset(("goal",))
            )
            self.assertEqual(scope.query.normalized.features.result_head, "local:1")
            self.assertEqual(scope.query.normalized.features.arity, 0)
            self.assertEqual(
                session.inspect_goals(parent, budget).state.structural_hash,
                parent.structural_hash,
            )


if __name__ == "__main__":
    unittest.main()
