"""Complete scope type views agree with Agda's ordinary per-entry renderer."""

from __future__ import annotations

import os
import unittest
from textwrap import indent

from test_live_scope_capacity import NATIVE, source_session

from agdaprover.bridge.contracts import InteractionId
from agdaprover.bridge.live_scope import exclusions_payload
from agdaprover.bridge.operations import ActionInput
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter

DEFINITIONS = """data U : Set where u : U
data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B
infixr 5 _,_
pattern both x y = x , y
record Box (A : Set) : Set where
  constructor box
  field
    value : A
open Box
poly : {ℓ : Level} {X : Set ℓ} → X → X
poly x = x
irrelevant : {X : Set} → .X → U
irrelevant _ = u
Alias : Set → Set
Alias X = Pair X U
boxed : {X : Set} → X → Box X
boxed = box
abstract
  Sealed : Set
  Sealed = U
  witness : Sealed
  witness = u
module Parameter (X : Set) where
  identity : X → X
  identity x = x
module Instance = Parameter U
open Instance renaming (identity to chosen)
"""

SOURCE = (
    "{-# OPTIONS --safe --without-K #-}\nmodule ScopeCapacity where\n"
    "open import Agda.Primitive using (Level; _⊔_)\nmodule Catalogue where\n"
    + indent(DEFINITIONS, "  ")
    + "open Catalogue\n"
)


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_SCOPE_RENDERING") == "1" and NATIVE.is_file(),
    "explicit native scope-rendering profile required",
)
class ScopeTypeRenderingTests(unittest.TestCase):
    def test_complete_views_match_ordinary_rendering_in_each_context(self):
        suffixes = (
            "goal : U\ngoal = {!!}\n",
            "module Context {A : Set} (a : A) where\n  goal : A\n  goal = {!!}\n",
            "module _ {ℓ : Level} (A : Set ℓ) (poly : A) where\n"
            "  goal : A\n  goal = {!!}\n",
        )
        adapter = Agda28Adapter()
        for suffix in suffixes:
            with (
                self.subTest(suffix=suffix),
                source_session(SOURCE + suffix) as (
                    path,
                    session,
                    budget,
                    parent,
                ),
            ):
                active = session._source_for(parent.module_id)
                _, response = session.transport.command(
                    active, adapter.module_contents(0, "Catalogue"), transactional=True
                )
                ordinary = dict(adapter.named_contents(response))
                self.assertTrue(
                    {"poly", "box", "irrelevant", "Sealed", "_,_"} <= ordinary.keys(),
                    response.events,
                )
                for query in (
                    {},
                    {"include_dependencies": True},
                    {"normalize_query": True},
                    {"normalize_query": True, "include_dependencies": True},
                    {"type_family_query": True},
                    {"type_family_query": True, "include_dependencies": True},
                    {"type_spine_heads": True},
                    {"type_spine_heads": True, "include_dependencies": True},
                ):
                    payload = exclusions_payload(
                        frozenset(), output_bytes=budget.output_bytes, **query
                    )
                    _, response = session.transport.command(
                        active, adapter.module_contents(0, payload), transactional=True
                    )
                    (scope,) = [
                        e.value for e in response.events if e.kind == "AgdaProverScope"
                    ]
                    views = {
                        alias: row["type"]
                        for row in scope["declarations"]
                        for alias in row["aliases"]
                    }
                    for name, expected in ordinary.items():
                        self.assertEqual(
                            views["Catalogue." + name], expected, (name, query)
                        )
                rejected = session.try_action(
                    parent, ActionInput("check-term", InteractionId(0), "Set"), budget
                )
                self.assertFalse(rejected.accepted)
                _, repeated = session.transport.command(
                    active, adapter.module_contents(0, payload), transactional=True
                )
                self.assertEqual(
                    [e.value for e in repeated.events if e.kind == "AgdaProverScope"],
                    [scope],
                )
                self.assertEqual(
                    session.inspect_goals(parent, budget).state.structural_hash,
                    parent.structural_hash,
                )
                self.assertEqual(path.read_text(), SOURCE + suffix)
