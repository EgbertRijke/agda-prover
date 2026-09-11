"""Exact-state read reuse: optional native conformance, never proof caching."""

from __future__ import annotations

import os
import unittest
from contextlib import contextmanager
from dataclasses import replace
from unittest.mock import patch

import test_live_scope_capacity as capacity
from test_live_scope_capacity import NATIVE, source_session

from agdaprover.bridge.contracts import BridgeError, BridgeFailure, InteractionId
from agdaprover.bridge.operations import ActionInput, OpenProjectRequest
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import DecodedResponse
from agdaprover.contracts import TaskSpec
from agdaprover.joint import prove_joint_prefix
from agdaprover.resource_budget import ResourceExhausted

SOURCE = """{-# OPTIONS --safe --without-K #-}
module ScopeCapacity where
data U : Set where
  u : U
module Library where
  abstract
    Opaque : Set
    Opaque = U
    witness : Opaque
    witness = u
  private
    secret : Opaque
    secret = witness
open Library using (Opaque) renaming (witness to chosen)
goal : Opaque
goal = {!!}
future : Opaque
future = chosen
"""


@contextmanager
def reused_session(source=SOURCE, *, enabled=True, **options):
    with (
        patch.dict(
            os.environ, {"AGDAPROVER_REUSE_SCOPED_READS": "1" if enabled else "0"}
        ),
        source_session(source, **options) as opened,
    ):
        yield opened


@unittest.skipUnless(
    os.environ.get("AGDAPROVER_TEST_LIVE_SCOPE") == "1" and NATIVE.is_file(),
    "explicit native live-scope test required",
)
class ScopedReadReuseTests(unittest.TestCase):
    def read(self, session, budget, parent, *, goal=0, excluded=("goal",)):
        return session.search_scoped_retrieval(
            parent, InteractionId(goal), budget, excluded_names=frozenset(excluded)
        )

    def test_exact_repeat_and_all_query_modes_keep_visibility(self):
        for options in (
            {},
            {"dependencies": True},
            {"query_views": True},
            {"type_family": True},
            {"type_heads": True},
        ):
            with (
                self.subTest(options=options),
                reused_session(**options) as (path, session, budget, parent),
            ):
                first = self.read(session, budget, parent)
                count = session.transport.cost.commands
                self.assertIs(self.read(session, budget, parent), first)
                self.assertEqual(session.transport.cost.commands, count)
                self.assertEqual(session.scoped_read_cache_hits, 1)
                names = dict(first.declarations())
                self.assertIn("chosen", names)
                self.assertNotIn("witness", names)
                self.assertFalse(
                    any(n.endswith(("secret", "future", "goal")) for n in names)
                )
                self.assertEqual(path.read_text(), SOURCE)

    def test_disabled_read_repeats_kernel_query(self):
        with reused_session(enabled=False) as (_, session, budget, parent):
            first = self.read(session, budget, parent)
            count = session.transport.cost.commands
            self.assertEqual(self.read(session, budget, parent), first)
            self.assertEqual(session.transport.cost.commands, count + 1)
            self.assertEqual(session.scoped_read_cache_hits, 0)
            self.assertIsNone(session._last_scoped_read)

    def test_joint_readiness_and_search_share_scope_with_legacy_fallback(self):
        outcomes = {False: [], True: []}
        original = ConformingKernelSession.search_scoped_retrieval
        for enabled, live in (
            (False, True),
            (True, True),
            (False, False),
            (True, False),
        ):
            hits = []

            def observe(session, *args, observed_hits=hits, **kwargs):
                before = session.scoped_read_cache_hits
                result = original(session, *args, **kwargs)
                observed_hits.append(session.scoped_read_cache_hits - before)
                return result

            with (
                self.subTest(enabled=enabled, live=live),
                reused_session(enabled=enabled) as (path, session, _budget, _parent),
            ):
                session.close()
                with (
                    patch.dict(
                        os.environ,
                        {"AGDAPROVER_SCOPED_RETRIEVAL": "1" if live else "0"},
                    ),
                    patch.object(
                        ConformingKernelSession, "search_scoped_retrieval", observe
                    ),
                ):
                    result = prove_joint_prefix(
                        TaskSpec(path, ranker="symbolic", timeout_seconds=15)
                    )
                if live:
                    self.assertEqual(result.status, "verified", result.diagnostics)
                    self.assertTrue(result.validation["fresh_process"])
                self.assertEqual(path.read_text(), SOURCE)
                self.assertEqual(bool(sum(hits)), enabled and live)
                self.assertEqual(
                    bool(result.search_stats["scoped_builder_queries"]),
                    enabled and live,
                )
                outcomes[live].append((result.status, result.patch))
        # The legacy catalogue does not resolve this opaque alias; enabling
        # read reuse alone must not change its outcome or widen its authority.
        for pair in outcomes.values():
            self.assertEqual(pair[0], pair[1])

    def test_exclusions_and_goal_change_miss_and_evict(self):
        source = SOURCE + "another : Opaque\nanother = {!!}\n"
        with reused_session(source) as (_, session, budget, parent):
            first = self.read(session, budget, parent)
            count = session.transport.cost.commands
            filtered = self.read(session, budget, parent, excluded=("goal", "chosen"))
            self.assertEqual(session.transport.cost.commands, count + 1)
            self.assertFalse(
                any(
                    n.endswith("witness") or n == "chosen"
                    for n, _ in filtered.declarations()
                )
            )
            other = self.read(session, budget, parent, goal=1)
            self.assertEqual(session.transport.cost.commands, count + 2)
            self.assertNotEqual(other.allowed.scope_id, first.allowed.scope_id)
            self.assertEqual(self.read(session, budget, parent), first)
            self.assertEqual(session.transport.cost.commands, count + 3)

    def test_changed_child_misses_and_closed_goal_is_rejected(self):
        source = SOURCE + "another : Opaque\nanother = {!!}\n"
        with reused_session(source) as (_, session, budget, parent):
            first = self.read(session, budget, parent, goal=1)
            changed = session.try_action(
                parent,
                ActionInput("give", InteractionId(0), "chosen", commit=True),
                budget,
            )
            self.assertTrue(changed.accepted)
            child = changed.transition.child_state
            count = session.transport.cost.commands
            second = self.read(session, budget, child, goal=1)
            self.assertEqual(session.transport.cost.commands, count + 1)
            self.assertNotEqual(first.allowed.scope_id, second.allowed.scope_id)
            with self.assertRaises(BridgeError) as error:
                self.read(session, budget, child, goal=0)
            self.assertEqual(error.exception.failure, BridgeFailure.INVALID_REQUEST)

    def test_rejected_speculation_keeps_parent_observation(self):
        with reused_session() as (_, session, budget, parent):
            first = self.read(session, budget, parent)
            rejected = session.try_action(
                parent,
                ActionInput("refine", InteractionId(0), "u", commit=False),
                budget,
            )
            self.assertFalse(rejected.accepted)
            self.assertIs(self.read(session, budget, parent), first)
            self.assertEqual(session.scoped_read_cache_hits, 1)

    def test_stale_source_generation_budget_and_close_cannot_hit(self):
        with reused_session() as (path, session, budget, parent):
            self.read(session, budget, parent)
            count = session.transport.cost.commands
            for token, allowance, failure in (
                (
                    replace(parent, process_generation=parent.process_generation + 1),
                    budget,
                    BridgeFailure.STALE_TOKEN,
                ),
                (
                    replace(
                        parent,
                        source_revision=replace(parent.source_revision, value="e" * 64),
                    ),
                    budget,
                    BridgeFailure.STALE_TOKEN,
                ),
                (parent, replace(budget), BridgeFailure.INVALID_REQUEST),
            ):
                with self.assertRaises(BridgeError) as error:
                    self.read(session, allowance, token)
                self.assertEqual(error.exception.failure, failure)
            path.write_text(SOURCE + "-- externally edited\n")
            with self.assertRaises(BridgeError) as error:
                self.read(session, budget, parent)
            self.assertEqual(error.exception.failure, BridgeFailure.STALE_TOKEN)
            self.assertEqual(session.transport.cost.commands, count)
            self.assertEqual(session.scoped_read_cache_hits, 0)
            session.close()
            self.assertIsNone(session._last_scoped_read)

    def test_hits_obey_deadline_cancellation_and_shared_resources(self):
        with reused_session() as (_, session, budget, parent):
            self.read(session, budget, parent)
            count = session.transport.cost.commands
            with patch(
                "agdaprover.bridge.session.time.monotonic",
                return_value=budget.deadline + 1,
            ):
                with self.assertRaises(BridgeError) as error:
                    self.read(session, budget, parent)
                self.assertEqual(error.exception.failure, BridgeFailure.TIMEOUT)
            with patch(
                "agdaprover.bridge.resources.checkpoint",
                side_effect=ResourceExhausted("cpu", 2, 1),
            ):
                with self.assertRaises(ResourceExhausted):
                    self.read(session, budget, parent)
            session._cancellation.cancel()
            with self.assertRaises(BridgeError) as error:
                self.read(session, budget, parent)
            self.assertEqual(error.exception.failure, BridgeFailure.CANCELLED)
            self.assertEqual(session.transport.cost.commands, count)
            self.assertEqual(session.scoped_read_cache_hits, 0)

    def test_malformed_read_does_not_publish_a_cache_entry(self):
        with reused_session() as (_, session, budget, parent):
            with patch.object(
                session.transport,
                "command",
                return_value=(None, DecodedResponse((), "0" * 64, 0)),
            ):
                with self.assertRaises(BridgeError) as error:
                    self.read(session, budget, parent)
                self.assertEqual(
                    error.exception.failure, BridgeFailure.PROTOCOL_FAILURE
                )
                self.assertIsNone(session._last_scoped_read)
            self.assertIsNotNone(self.read(session, budget, parent))

    def test_terminated_process_cannot_serve_cached_observations(self):
        with reused_session() as (_, session, budget, parent):
            self.read(session, budget, parent)
            session.transport.close()
            with self.assertRaises(BridgeError) as error:
                self.read(session, budget, parent)
            self.assertEqual(error.exception.failure, BridgeFailure.STALE_TOKEN)
            self.assertEqual(session.scoped_read_cache_hits, 0)

    def test_project_reset_clears_observation_and_invalidates_old_state(self):
        with reused_session() as (path, session, budget, parent):
            self.read(session, budget, parent)
            path.write_text(SOURCE + "-- a new source revision\n")
            opened = session.reset_project(OpenProjectRequest(path), budget)
            self.assertIsNone(session._last_scoped_read)
            loaded = session.load_module(
                opened.project, opened.root_module, opened.source_revision, budget
            )
            with self.assertRaises(BridgeError) as error:
                self.read(session, budget, parent)
            self.assertEqual(error.exception.failure, BridgeFailure.STALE_TOKEN)
            self.assertIsNotNone(
                self.read(session, budget, loaded.transition.child_state)
            )

    def test_enabled_live_failure_does_not_fall_back_to_legacy_catalogues(self):
        with reused_session() as (path, session, _budget, _parent):
            session.close()
            with (
                patch.object(
                    ConformingKernelSession,
                    "search_scoped_retrieval",
                    side_effect=ResourceExhausted("cpu", 2, 1),
                ),
                patch("agdaprover.joint.visible_scope_declarations") as legacy,
            ):
                result = prove_joint_prefix(
                    TaskSpec(path, ranker="symbolic", timeout_seconds=15)
                )
            self.assertEqual(result.status, "resource-exhausted", result.diagnostics)
            self.assertIsNone(result.patch)
            legacy.assert_not_called()

    def test_resource_refusal_is_not_cached(self):
        source = SOURCE.replace(
            "goal : Opaque",
            "".join(f"d{i} : U\nd{i} = u\n" for i in range(80)) + "goal : Opaque",
        )
        with reused_session(source, output_bytes=8192) as (_, session, budget, parent):
            for _ in range(2):
                with self.assertRaises(BridgeError) as error:
                    self.read(session, budget, parent)
                self.assertEqual(
                    error.exception.failure, BridgeFailure.RESOURCE_EXHAUSTED
                )
                self.assertIsNone(session._last_scoped_read)

    def test_read_reuse_cannot_replace_fresh_validation(self):
        source = """{-# OPTIONS --safe --without-K #-}
module ScopeCapacity where
data U : Set where
  u : U
goal : U
goal = {!!}
"""
        with reused_session(source) as (path, session, budget, parent):
            self.read(session, budget, parent)
            self.read(session, budget, parent)
            capacity.NativeScopeCapacityTests.assert_parent_and_fresh_proof(
                self, path, session, budget, parent
            )

    def test_changed_query_options_miss_and_local_envelope_still_applies(self):
        with reused_session() as (_, session, budget, parent):
            first = self.read(session, budget, parent)
            count = session.transport.cost.commands
            session._scope_type_heads_enabled = True
            second = self.read(session, budget, parent)
            self.assertEqual(session.transport.cost.commands, count + 1)
            self.assertNotEqual(first.allowed.scope_id, second.allowed.scope_id)
            with patch.object(
                session.transport.supervisor,
                "check",
                side_effect=session._error(
                    BridgeFailure.RESOURCE_EXHAUSTED,
                    "bridge-memory-exhausted",
                    "test memory limit",
                ),
            ):
                with self.assertRaises(BridgeError) as error:
                    self.read(session, budget, parent)
                self.assertEqual(
                    error.exception.failure, BridgeFailure.RESOURCE_EXHAUSTED
                )
            self.assertEqual(session.transport.cost.commands, count + 1)
            self.assertEqual(session.scoped_read_cache_hits, 0)
