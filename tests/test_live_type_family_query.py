"""Closed wire contract and opt-in, real-kernel typed-reduction canaries."""

from __future__ import annotations

import copy
import json
import os
import unittest
from unittest.mock import patch

from test_live_scope_capacity import HEADER, NATIVE, source_session
from test_live_scope_protocol import TOKEN, wire

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import BridgeBudget, BridgeError, InteractionId
from agdaprover.bridge.live_scope import (
    decode_resource_limit,
    decode_scope,
    exclusions_payload,
    scope_schema,
)
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter
from agdaprover.retrieval import TYPE_FAMILY_QUERY_POLICY
from agdaprover.validation import validate_candidate


def family_wire(deps=False):
    value = wire(deps)
    value["schema_version"] = scope_schema(deps, False, True)
    value["structure_nodes"] += 3
    value["type_family_query"] = {
        "policy": TYPE_FAMILY_QUERY_POLICY,
        "status": "checked",
        "features": {
            "result_head": "global:1:0",
            "arity": 0,
            "symbols": ["1:1", "hidden"],
        },
        "structure_nodes": 3,
        "conversion_checked": True,
        "term_visits": 4,
        "type_position_reductions": 2,
    }
    return value


def read(value, deps=False, requested=True):
    return decode_scope(
        value,
        state=TOKEN,
        goal_id=0,
        excluded_names=frozenset(),
        adapter_sha256="d" * 64,
        output_bytes=8_388_608,
        include_dependencies=deps,
        type_family_query=requested,
    )


class TypeFamilyProtocolTests(unittest.TestCase):
    def test_exact_capabilities_and_allowed_tokens(self):
        for deps in (False, True):
            value = family_wire(deps)
            scope = read(value, deps)
            self.assertEqual(scope.query.type_family.tokens, ("clash", "left"))
            self.assertEqual(scope.query.type_family.term_visits, 4)
            self.assertIsNone(scope.query.normalized)
            self.assertTrue(
                exclusions_payload(
                    frozenset(),
                    output_bytes=512,
                    include_dependencies=deps,
                    type_family_query=True,
                ).startswith(f"agdaprover:scoped-retrieval:v{11 if deps else 10}:")
            )
            with self.assertRaises(ValueError):
                read(value, deps, requested=False)
            with self.assertRaises(ValueError):
                read(wire(deps), deps)
            with self.assertRaises(ValueError):
                exclusions_payload(
                    frozenset(),
                    output_bytes=512,
                    normalize_query=True,
                    type_family_query=True,
                )
            for status in ("kernel-rejected", "output-limited"):
                missing = copy.deepcopy(value)
                missing["type_family_query"].update(
                    status=status,
                    features=None,
                    conversion_checked=status == "output-limited",
                    structure_nodes=3 if status == "output-limited" else 0,
                )
                raw_scope = read(missing, deps)
                self.assertEqual(raw_scope.allowed.premises, scope.allowed.premises)
                self.assertEqual(
                    raw_scope.index()
                    .retrieve(raw_scope.query)
                    .type_family_classification,
                    status,
                )

    def test_malformed_or_unchecked_evidence_fails_closed(self):
        original = family_wire()
        for field in original["type_family_query"]:
            value = copy.deepcopy(original)
            del value["type_family_query"][field]
            with self.assertRaises(ValueError):
                read(value)
        for key, wrong in (
            ("status", "partial"),
            ("status", []),
            ("conversion_checked", False),
            ("conversion_checked", 1),
            ("features", None),
            ("features", {}),
            ("structure_nodes", True),
            ("structure_nodes", 0),
            ("structure_nodes", 999),
            ("term_visits", True),
            ("type_position_reductions", 5),
            ("policy", "agda-normalise-query-type-v1"),
        ):
            value = copy.deepcopy(original)
            value["type_family_query"][key] = wrong
            with self.assertRaises(ValueError):
                read(value)

    def test_invalid_combination_rejected_before_project_io(self):
        for scope, normalization in (("0", "0"), ("1", "1")):
            with patch.dict(
                os.environ,
                {
                    "AGDAPROVER_SCOPED_RETRIEVAL": scope,
                    "AGDAPROVER_SCOPED_QUERY_VIEWS": normalization,
                    "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "1",
                },
            ):
                session = ConformingKernelSession()
                with self.assertRaises(BridgeError) as caught:
                    session.open_project(None, BridgeBudget(wall_seconds=1))
                self.assertEqual(
                    caught.exception.diagnostic.code,
                    "type-family-query-requires-exclusive-live-scope",
                )
                session.close()


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_TYPE_FAMILY_QUERY") == "1" and NATIVE.is_file(),
    "explicit native type-family tests required",
)
class NativeTypeFamilyTests(unittest.TestCase):
    def observe(self, session, parent, budget, goal=0, excluded=("goal",)):
        return session.search_scoped_retrieval(
            parent, InteractionId(goal), budget, excluded_names=frozenset(excluded)
        )

    def test_nested_alias_recovers_premise_and_fresh_proof(self):
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
        for deps in (False, True):
            with source_session(source, type_family=True, dependencies=deps) as (
                path,
                session,
                budget,
                parent,
            ):
                scoped = self.observe(session, parent, budget)
                result = scoped.index().retrieve(scoped.query, limit=64)
                ready = next(i for i in result.items if "ready" in i.premise.aliases)
                self.assertEqual(
                    result.type_family_classification, "stable-head-and-arity"
                )
                self.assertEqual(ready.query_view, "type-family")
                self.assertEqual(result.query_views_scored, 2)
                self.assertGreater(scoped.query.type_family.term_visits, 0)
                self.assertEqual(
                    session.inspect_goals(parent, budget).state.structural_hash,
                    parent.structural_hash,
                )
                self.assertEqual(path.read_text(), source)
                with AgdaSession(timeout_seconds=10) as checker:
                    (goal,) = checker.load_module(path)
                validation, _ = validate_candidate(
                    path, goal, "ready", timeout_seconds=10
                )
                self.assertTrue(validation["checked"], validation)
                self.assertTrue(validation["fresh_process"])

    def test_function_valued_types_values_opacity_relevance_and_renaming(self):
        for renamed in (False, True):
            for irrelevant in (False, True):
                source = (
                    HEADER
                    + """named-value : U
named-value = u
named-function : U → U
named-function x = x
Alias : Set → Set
Alias A = A
Family : Set → Set
Family A = Alias A
abstract
  Secret : Set
  Secret = U
data Envelope (F : Set → Set) (A : Set) (v : U) (g : U → U) : Set₁ where
  pack : Envelope F A v g
module _ (A : Set) (a : A) where
  GOAL : (b : Alias A) → Envelope Family Secret named-value named-function
  goal = {!!}
""".replace("GOAL", ".goal" if irrelevant else "goal")
                )
                names = {
                    n: "renamed-" + n if renamed else n
                    for n in (
                        "Alias",
                        "Family",
                        "Secret",
                        "named-value",
                        "named-function",
                    )
                }
                for old, new in names.items():
                    source = source.replace(old, new)
                with source_session(source, type_family=True) as (
                    _path,
                    session,
                    budget,
                    parent,
                ):
                    scope = self.observe(session, parent, budget)
                    aliases = {
                        a: p.declaration_id
                        for p in scope.allowed.premises
                        for a in p.aliases
                    }
                    alternate = scope.query.type_family
                    self.assertEqual(alternate.status, "checked")
                    self.assertEqual(
                        scope.index().retrieve(scope.query).type_family_classification,
                        "stable-head-and-arity",
                    )
                    for name in ("Alias", "Family"):
                        self.assertIn(
                            aliases[names[name]], scope.query.features.symbols
                        )
                        self.assertNotIn(
                            aliases[names[name]], alternate.features.symbols
                        )
                    for name in ("Secret", "named-value", "named-function"):
                        self.assertIn(aliases[names[name]], alternate.features.symbols)
                    self.assertEqual(
                        session.inspect_goals(parent, budget).state.structural_hash,
                        parent.structural_hash,
                    )

    def test_changed_local_head_and_unsolved_metas_preserve_raw_and_parent(self):
        source = (
            HEADER
            + """Apply : {A : Set} → (A → Set) → A → Set
Apply P x = P x
module _ (A : Set) (P : A → Set) (x : A) where
  goal : Apply P x
  goal = {!!}
T : Set
T = {!!}
meta-goal : T
meta-goal = {!!}
"""
        )
        with source_session(source, type_family=True) as (
            _path,
            session,
            budget,
            parent,
        ):
            before = session.inspect_goals(parent, budget).state
            scope = self.observe(
                session, parent, budget, excluded=("goal", "T", "meta-goal")
            )
            self.assertEqual(scope.query.type_family.features.result_head, "local:1")
            result = scope.index().retrieve(scope.query)
            self.assertEqual(result.type_family_classification, "changed-head")
            self.assertEqual(result.query_views_scored, 1)
            unresolved = self.observe(
                session, parent, budget, goal=2, excluded=("goal", "T", "meta-goal")
            )
            self.assertIn(
                unresolved.index()
                .retrieve(unresolved.query)
                .type_family_classification,
                ("unknown-head", "kernel-rejected"),
            )
            self.assertEqual(session.inspect_goals(parent, budget).state, before)

    def test_optional_output_overflow_keeps_complete_raw_scope_and_work(self):
        source = HEADER + "data Pair (A B : Set) : Set where\n  pair : Pair A B\n"
        source += "".join(f"data T{i} : Set where\n  t{i} : T{i}\n" for i in range(40))
        nested = "U"
        for i in range(40):
            nested = f"Pair T{i} ({nested})"
        source += f"Alias : Set\nAlias = {nested}\ngoal : Pair U Alias\ngoal = {{!!}}\n"
        for deps in (False, True):
            with source_session(source, type_family=True, dependencies=deps) as (
                _path,
                session,
                budget,
                parent,
            ):

                def request(limit, deps=deps):
                    payload = exclusions_payload(
                        frozenset(("goal",)),
                        output_bytes=limit,
                        include_dependencies=deps,
                        type_family_query=True,
                    )
                    _, response = session.transport.command(
                        session._source_for(parent.module_id),
                        Agda28Adapter().module_contents(0, payload),
                        transactional=True,
                    )
                    return [
                        e.value
                        for e in response.events
                        if e.kind in {"AgdaProverScope", "AgdaProverScopeResource"}
                    ]

                (full,) = request(budget.output_bytes)
                self.assertEqual(full["type_family_query"]["status"], "checked")
                limit = (
                    len(
                        json.dumps(
                            full, ensure_ascii=False, separators=(",", ":")
                        ).encode()
                    )
                    - 100
                )
                (fallback,) = request(limit)
                self.assertEqual(fallback["kind"], "AgdaProverScope")
                self.assertEqual(
                    fallback["type_family_query"]["status"], "output-limited"
                )
                self.assertEqual(fallback["declarations"], full["declarations"])
                self.assertEqual(
                    fallback["type_family_query"]["term_visits"],
                    full["type_family_query"]["term_visits"],
                )
                decoded = decode_scope(
                    fallback,
                    state=parent,
                    goal_id=0,
                    excluded_names=frozenset(("goal",)),
                    adapter_sha256=session._scope_adapter_hash,
                    output_bytes=limit,
                    include_dependencies=deps,
                    type_family_query=True,
                )
                self.assertEqual(
                    decoded.index().retrieve(decoded.query).type_family_classification,
                    "output-limited",
                )
                (refusal,) = request(512)
                self.assertGreater(
                    decode_resource_limit(
                        refusal,
                        goal_id=0,
                        output_bytes=512,
                        include_dependencies=deps,
                        type_family_query=True,
                    ),
                    512,
                )
                self.assertEqual(
                    session.inspect_goals(parent, budget).state.structural_hash,
                    parent.structural_hash,
                )


if __name__ == "__main__":
    unittest.main()
