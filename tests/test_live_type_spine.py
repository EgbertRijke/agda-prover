"""Contextual type heads are checked features, not proof or scope authority."""

from __future__ import annotations

import copy
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from test_live_scope_capacity import NATIVE, source_session
from test_live_scope_protocol import TOKEN, wire

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import BridgeBudget, BridgeError, InteractionId
from agdaprover.bridge.live_scope import (
    DEPENDENCY_TYPE_HEADS_SCHEMA,
    TYPE_HEADS_POLICY,
    TYPE_HEADS_SCHEMA,
    decode_resource_limit,
    decode_scope,
    exclusions_payload,
)
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter
from agdaprover.contracts import TaskSpec
from agdaprover.search import prove
from agdaprover.validation import validate_candidate


def snapshot(dependencies=False):
    value = wire(dependencies)
    value["schema_version"] = (
        DEPENDENCY_TYPE_HEADS_SCHEMA if dependencies else TYPE_HEADS_SCHEMA
    )
    value["feature_policy"] = TYPE_HEADS_POLICY
    witness = {
        "status": "checked",
        "head_reductions": 1,
        "conversion_checked": True,
        "raw_result_head": "global:1:9",
        "raw_arity": 0,
    }
    value["type_spine"] = witness
    value["declarations"][0]["type_spine"] = copy.deepcopy(witness)
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
        type_spine_heads=True,
    )


class TypeSpineProtocolTests(unittest.TestCase):
    def test_invalid_session_mode_fails_before_project_io(self):
        for scope, query, family in (("0", "0", "0"), ("1", "1", "0"), ("1", "0", "1")):
            with patch.dict(
                os.environ,
                {
                    "AGDAPROVER_SCOPED_RETRIEVAL": scope,
                    "AGDAPROVER_SCOPED_QUERY_VIEWS": query,
                    "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": family,
                    "AGDAPROVER_SCOPED_TYPE_SPINE_HEADS": "1",
                },
            ):
                session = ConformingKernelSession()
                try:
                    with self.assertRaises(BridgeError) as caught:
                        session.open_project(None, BridgeBudget(wall_seconds=1))
                    self.assertEqual(
                        caught.exception.diagnostic.code,
                        "type-spine-heads-require-exclusive-live-scope",
                    )
                finally:
                    session.close()

    def test_explicit_capability_and_identity(self):
        for dependencies in (False, True):
            value = snapshot(dependencies)
            scoped = read(value, dependencies)
            self.assertEqual(scoped.query.features, scoped.allowed.premises[0].features)
            changed = copy.deepcopy(value)
            changed["type_spine"]["raw_result_head"] = "global:1:8"
            self.assertNotEqual(scoped.index_id, read(changed, dependencies).index_id)
            payload = exclusions_payload(
                frozenset(),
                output_bytes=4096,
                include_dependencies=dependencies,
                type_spine_heads=True,
            )
            self.assertTrue(
                payload.startswith(
                    f"agdaprover:scoped-retrieval:v{13 if dependencies else 12}:"
                )
            )
            for query in ("normalize_query", "type_family_query"):
                with self.assertRaises(ValueError):
                    exclusions_payload(
                        frozenset(),
                        output_bytes=4096,
                        type_spine_heads=True,
                        **{query: True},
                    )
            with self.assertRaises(ValueError):
                decode_scope(
                    value,
                    state=TOKEN,
                    goal_id=0,
                    excluded_names=frozenset(),
                    adapter_sha256="d" * 64,
                    output_bytes=8_388_608,
                    include_dependencies=dependencies,
                )

    def test_rejected_optional_view_must_preserve_raw_features(self):
        value = snapshot()
        value["type_spine"].update(
            status="kernel-rejected",
            conversion_checked=False,
            head_reductions=0,
            raw_result_head=value["target"]["result_head"],
        )
        read(value)
        for field, replacement in (
            ("raw_arity", 1),
            ("raw_result_head", "global:1:8"),
            ("conversion_checked", True),
            ("head_reductions", True),
            ("status", []),
        ):
            changed = copy.deepcopy(value)
            changed["type_spine"][field] = replacement
            with self.subTest(field=field), self.assertRaises(ValueError):
                read(changed)

    def test_coverage_work_and_schema_fail_closed(self):
        for location in ("goal", "premise"):
            for mutation in (
                "missing",
                "extra",
                "negative",
                "coverage",
                "arity",
                "head",
                "policy",
                "version",
                "count",
            ):
                value = snapshot()
                owner = value if location == "goal" else value["declarations"][0]
                witness = owner["type_spine"]
                if mutation == "missing":
                    del owner["type_spine"]
                elif mutation == "extra":
                    witness["invented"] = True
                elif mutation == "negative":
                    witness["head_reductions"] = -1
                elif mutation == "coverage":
                    witness["head_reductions"] = 2
                elif mutation == "arity":
                    witness["raw_arity"] = True
                elif mutation == "head":
                    witness["raw_result_head"] = []
                elif mutation == "policy":
                    value["feature_policy"] = "unknown"
                elif mutation == "version":
                    value["schema_version"] = "agdaprover.live-scope.v6"
                else:
                    value["structure_nodes"] = 1
                with (
                    self.subTest(location=location, mutation=mutation),
                    self.assertRaises(ValueError),
                ):
                    read(value)
        for flag in (1, None, "yes"):
            with self.assertRaises(ValueError):
                exclusions_payload(
                    frozenset(), output_bytes=4096, type_spine_heads=flag
                )


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_TYPE_HEADS") == "1" and NATIVE.is_file(),
    "explicit native type-head profile required",
)
class NativeTypeSpineTests(unittest.TestCase):
    def test_alias_recognition_improves_autonomous_search_at_the_same_budget(self):
        for family, alias, witness in (
            ("Family", "Alias", "z-useful"),
            ("Predicate", "Claim", "supplied"),
        ):
            source = f"""{{-# OPTIONS --safe --without-K #-}}
module SearchSample where
data Flag : Set where off on : Flag
data Unit : Set where star : Unit
abstract
  {family} : Flag → Set
  {family} _ = Unit
{alias} : Flag → Set
{alias} = {family}
abstract
  {witness} : {alias} on
  {witness} = star
"""
            source += "".join(
                f"  a{i:02} : {family} on → {family} off\n  a{i:02} _ = star\n"
                for i in range(32)
            )
            source += f"target : {family} on\ntarget = {{!!}}\n"
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "SearchSample.agda"
                path.write_text(source)
                results = []
                for heads in (False, True):
                    with patch.dict(
                        os.environ,
                        {
                            "AGDAPROVER_AGDA_BRIDGE": str(NATIVE),
                            "AGDAPROVER_DISABLE_AGDA_BRIDGE": "0",
                            "AGDAPROVER_SCOPED_RETRIEVAL": "1",
                            "AGDAPROVER_SCOPED_DEPENDENCIES": "0",
                            "AGDAPROVER_SCOPED_QUERY_VIEWS": "0",
                            "AGDAPROVER_SCOPED_TYPE_FAMILY_QUERY": "0",
                            "AGDAPROVER_SCOPED_TYPE_SPINE_HEADS": "1" if heads else "0",
                        },
                    ):
                        result = prove(
                            TaskSpec(
                                path,
                                max_candidates=24,
                                max_verifier_calls=64,
                                timeout_seconds=15,
                            )
                        )
                    results.append(result)
                    self.assertEqual(path.read_text(), source)
                raw, reduced = results
                self.assertEqual(raw.status, "resource-exhausted", raw.diagnostics)
                self.assertEqual(raw.verifier_budget["used"], 64)
                self.assertGreater(raw.verifier_budget["denied_calls"], 0)
                self.assertGreater(raw.cost.actions_expanded, 0)
                self.assertEqual(
                    raw.cost.actions_expanded,
                    raw.search_stats["constructors"]["actions_considered"],
                )
                self.assertEqual(reduced.status, "verified", reduced.diagnostics)
                self.assertTrue(reduced.validation["fresh_process"])
                self.assertIn(witness, reduced.proof_term)
                self.assertLess(reduced.verifier_calls, raw.verifier_calls)
                self.assertLess(
                    reduced.verifier_budget["used"], raw.verifier_budget["used"]
                )
                self.assertLess(
                    reduced.cost.actions_expanded, raw.cost.actions_expanded
                )
                self.assertGreater(
                    reduced.search_stats["constructors"][
                        "scoped_retrieval_type_spine_queries"
                    ],
                    0,
                )

    def test_same_head_without_losing_raw_symbols_or_module_parameters(self):
        for family, lemma in (("Claim", "given"), ("predicate", "available")):
            source = f"""{{-# OPTIONS --safe --without-K #-}}
module ScopeCapacity (A : Set) where
open import Agda.Builtin.Equality
keep : A → A
keep x = x
{family} : A → Set
{family} x = keep x ≡ keep x
{lemma} : (x : A) → {family} x
{lemma} x = refl
goal : (x : A) → keep x ≡ keep x
goal = {{!!}}
future : A → A
future x = x
"""
            results = []
            for heads in (False, True):
                with source_session(source, type_heads=heads, dependencies=True) as (
                    path,
                    session,
                    budget,
                    parent,
                ):
                    observed = session.search_scoped_retrieval(
                        parent,
                        InteractionId(0),
                        budget,
                        excluded_names=frozenset(("goal",)),
                    )
                    self.assertIsNotNone(observed)
                    rows = {a: p for p in observed.allowed.premises for a in p.aliases}
                    self.assertNotIn("goal", rows)
                    self.assertNotIn("future", rows)
                    premise = rows[lemma]
                    results.append((observed.query.features, premise.features))
                    self.assertEqual(
                        session.inspect_goals(parent, budget).state.structural_hash,
                        parent.structural_hash,
                    )
                    if heads:
                        self.assertEqual(
                            premise.features.result_head,
                            observed.query.features.result_head,
                        )
                        self.assertEqual(premise.features.arity, 1)
                        self.assertIn(
                            rows[family].declaration_id, premise.features.symbols
                        )
                        self.assertIn(
                            rows["keep"].declaration_id, observed.query.features.symbols
                        )
                        with AgdaSession(timeout_seconds=10) as checker:
                            (goal,) = checker.load_module(path)
                        validation, _ = validate_candidate(
                            path, goal, lemma, timeout_seconds=10
                        )
                        self.assertTrue(validation["checked"], validation)
                        self.assertTrue(validation["fresh_process"])
                    self.assertEqual(path.read_text(), source)
            self.assertNotEqual(results[0][0].result_head, results[0][1].result_head)
            self.assertEqual(results[0][0].symbols, results[1][0].symbols)
            self.assertEqual(results[0][1].symbols, results[1][1].symbols)

    def test_complete_output_refusal_and_parent_reuse(self):
        source = """{-# OPTIONS --safe --without-K #-}
module ScopeCapacity where
data U : Set where u : U
goal : U
goal = {!!}
"""
        with source_session(source, type_heads=True) as (_, session, budget, parent):
            command = Agda28Adapter().module_contents(
                0,
                exclusions_payload(frozenset(), output_bytes=1, type_spine_heads=True),
            )
            _, response = session.transport.command(
                session._source_for(parent.module_id), command, transactional=True
            )
            (refusal,) = [
                e.value for e in response.events if e.kind == "AgdaProverScopeResource"
            ]
            self.assertGreater(
                decode_resource_limit(
                    refusal,
                    goal_id=0,
                    output_bytes=1,
                    include_dependencies=False,
                    type_spine_heads=True,
                ),
                1,
            )
            self.assertEqual(
                session.inspect_goals(parent, budget).state.structural_hash,
                parent.structural_hash,
            )
            self.assertIsNotNone(
                session.search_scoped_retrieval(
                    parent,
                    InteractionId(0),
                    budget,
                    excluded_names=frozenset(("goal",)),
                )
            )
