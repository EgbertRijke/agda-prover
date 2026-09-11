"""Kernel-owned copattern introduction and its proof/state boundaries."""

from __future__ import annotations

import shutil
import tempfile
import time
import unittest
from contextlib import contextmanager
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import (
    BridgeBudget,
    BridgeError,
    BridgeFailure,
    InteractionId,
    SourceRange,
)
from agdaprover.bridge.operations import (
    ActionInput,
    OpenProjectRequest,
    PolicyProfile,
    SourceEdit,
    SourcePatch,
)
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.bridge.versions.agda_2_8 import (
    Agda28Adapter,
    DecodedResponse,
    RawEvent,
)
from agdaprover.kernel.protocol import ResultSplittingSession
from agdaprover.reconstruction import apply_source_edit, reconstruct_case_split

SOURCE = """{-# OPTIONS --guardedness --without-K #-}
module Orbit where
record Orbit (A : Set) : Set where
  coinductive
  constructor pack
  field
    view : A
    advance : Orbit A
open Orbit
module _ {A : Set} (a : A) where
  stationary : Orbit A
  stationary = {!!}
"""


def response(row):
    return DecodedResponse((RawEvent("MakeCase", row),), "0" * 64, 100)


@contextmanager
def source_file(source=SOURCE):
    with tempfile.TemporaryDirectory(prefix="agdaprover-result-split-") as folder:
        path = Path(folder) / "Orbit.agda"
        path.write_text(source)
        yield path


@contextmanager
def opened(source=SOURCE):
    with source_file(source) as path, ConformingKernelSession() as session:
        budget = BridgeBudget(wall_seconds=20, cpu_seconds=20)
        project = session.open_project(OpenProjectRequest(path), budget)
        loaded = session.load_module(
            project.project, project.root_module, project.source_revision, budget
        )
        parent = loaded.transition.child_state
        assert parent is not None
        yield path, session, budget, project, parent


class ResultSplitCodecTests(unittest.TestCase):
    def test_result_split_has_no_subject_and_preserves_unicode_clauses(self):
        adapter = Agda28Adapter()
        self.assertEqual(adapter.split_result(4), 'Cmd_make_case 4 noRange ""')
        row = {
            "kind": "MakeCase",
            "interactionPoint": {"id": 4},
            "clauses": ["f .π = ?", "f .σ = ?"],
            "variant": "Function",
        }
        checked = adapter.result_split(response(row), interaction_id=4)
        self.assertTrue(checked.accepted)
        self.assertEqual(checked.clauses, tuple(row["clauses"]))

    def test_malformed_missing_duplicate_and_wrong_goal_are_protocol_errors(self):
        row = {
            "kind": "MakeCase",
            "interactionPoint": {"id": 4},
            "clauses": ["f .π = ?"],
            "variant": "Function",
        }
        malformed = [
            {**row, "kind": "Other"},
            {**row, "interactionPoint": {"id": True}},
            {**row, "interactionPoint": {"id": 3}},
            {**row, "interactionPoint": {}},
            {**row, "interactionPoint": None},
            *({**row, "clauses": value} for value in ([], [0], [""], ["\x00"], "?")),
            {**row, "variant": None},
            {**row, "variant": ""},
        ]
        adapter = Agda28Adapter()
        cases = [response(item) for item in malformed]
        valid = response(row)
        cases.extend(
            (replace(valid, events=()), replace(valid, events=valid.events * 2))
        )
        for candidate in cases:
            with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                adapter.result_split(candidate, interaction_id=4)


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class ResultSplittingTests(unittest.TestCase):
    def test_copattern_clauses_reconstruct_and_freshly_validate_renamed_corecursion(
        self,
    ):
        for view, advance in (("view", "advance"), ("peek", "resume")):
            source = SOURCE.replace("view", view).replace("advance", advance)
            if view == "peek":
                source = (
                    source.replace("record Orbit", "record Pulse")
                    .replace("Orbit A", "Pulse A")
                    .replace("open Orbit\n", "open Pulse\n")
                )
            with self.subTest(view=view), source_file(source) as path:
                with AgdaSession(timeout_seconds=20) as session:
                    self.assertIsInstance(session, ResultSplittingSession)
                    goal = session.inspect_goal(session.load_module(path)[0])
                    parent = session.current_state()
                    proposal = session.check_result_split(parent, goal_id=goal.goal_id)
                    self.assertTrue(proposal.accepted, proposal.diagnostic)
                    edit = reconstruct_case_split(source, goal, proposal.clauses)
                    generated = apply_source_edit(source, edit)
                    self.assertIn(f"  stationary .{view} = ?", generated)
                    self.assertIn(f"  stationary .{advance} = ?", generated)
                    self.assertEqual(
                        session.inspect_state(parent)[0].goal_id, goal.goal_id
                    )
                    self.assertEqual(path.read_text(), source)
                completed = generated.replace(f".{view} = ?", f".{view} = a").replace(
                    f".{advance} = ?", f".{advance} = stationary"
                )
                # Supplied leaf terms test this primitive, not autonomous proof
                # search or NNUE credit. Fresh checking includes productivity.
                self.assertTrue(self.validate(source, completed))

    def validate(self, source, completed):
        with opened(source) as (_path, session, budget, project, _parent):
            result = session.validate_patch(
                project.project,
                SourcePatch(
                    project.environment_id,
                    project.source_revision,
                    project.root_module,
                    (SourceEdit(SourceRange(1, len(source) + 1), source, completed),),
                ),
                PolicyProfile("result-split-test"),
                budget,
            )
            self.assertTrue(result.trust_report and result.trust_report.fresh_process)
            return result.verified

    def test_unguarded_recursion_and_constructor_guard_are_rejected(self):
        for term in ("stationary", "pack a stationary"):
            with self.subTest(term=term):
                self.assertFalse(self.validate(SOURCE, SOURCE.replace("{!!}", term)))

    def test_proposals_preserve_parent_and_charge_each_query_without_reloads(self):
        with opened() as (_path, session, budget, _project, parent):
            before = session.inspect_goals(parent, budget).state.to_dict()
            for _ in range(2):
                proposal = session.split_result(parent, InteractionId(0), budget)
                self.assertTrue(proposal.accepted)
                self.assertIsNone(proposal.transition.child_state)
                self.assertEqual(proposal.generated_goals, ())
                self.assertEqual(proposal.transition.cost.commands, 1)
                self.assertEqual(proposal.transition.cost.module_loads, 0)
                self.assertEqual(proposal.transition.cost.rollback_replays, 0)
            self.assertEqual(
                before, session.inspect_goals(parent, budget).state.to_dict()
            )

    def test_observing_parent_does_not_lose_committed_child(self):
        with opened() as (_path, session, budget, _project, parent):
            introduced = session.try_action(
                parent, ActionInput("refine", InteractionId(0), "", commit=True), budget
            )
            self.assertTrue(introduced.accepted)
            child = introduced.transition.child_state
            self.assertIsNotNone(child)
            before = session.inspect_goals(child, budget).state.to_dict()
            self.assertTrue(
                session.split_result(parent, InteractionId(0), budget).accepted
            )
            self.assertEqual(
                before, session.inspect_goals(child, budget).state.to_dict()
            )

    def test_copattern_capability_does_not_assume_coinductive_eta(self):
        source = (
            SOURCE[: SOURCE.index("module _")]
            + """
open import Agda.Builtin.Equality using (_≡_; refl)
module _ (A : Set) (s : Orbit A) where
  eta : pack (view s) (advance s) ≡ s
  eta = {!!}
"""
        )
        self.assertFalse(self.validate(source, source.replace("{!!}", "refl")))

    def test_function_result_introduces_arguments_before_fields(self):
        source = SOURCE.replace("  stationary : Orbit A", "  stationary : A → Orbit A")
        with opened(source) as (_path, session, budget, _project, parent):
            proposal = session.split_result(parent, InteractionId(0), budget)
            self.assertTrue(proposal.accepted)
            self.assertEqual(proposal.clauses, ("stationary x = ?",))

    def test_inductive_dependent_record_fields_retain_types(self):
        source = """{-# OPTIONS --safe --without-K #-}
module Orbit where
open import Agda.Builtin.Bool using (Bool)
record Bundle : Set₁ where
  field
    Carrier : Set
    element : Carrier
    transform : Carrier → Carrier
open Bundle
build : Bundle
build = {!!}
"""
        with source_file(source) as path, AgdaSession(timeout_seconds=20) as session:
            goal = session.inspect_goal(session.load_module(path)[0])
            proposal = session.check_result_split(session.current_state(), goal_id=0)
            self.assertTrue(proposal.accepted)
            generated = apply_source_edit(
                source, reconstruct_case_split(source, goal, proposal.clauses)
            )
            expected = (
                "build .Carrier = ?",
                "build .element = ?",
                "build .transform = ?",
            )
            self.assertEqual(proposal.clauses, expected)
        # Substitution after the earlier field is supplied is Agda-owned.
        generated = generated.replace("build .Carrier = ?", "build .Carrier = Bool")
        with source_file(generated) as path, AgdaSession(timeout_seconds=20) as session:
            goals = tuple(session.inspect_goal(g) for g in session.load_module(path))
            self.assertEqual(tuple(g.target for g in goals), ("Bool", "Bool → Bool"))

    def test_unsupported_result_and_coinductive_input_are_not_case_split(self):
        source = (
            SOURCE[: SOURCE.index("module _")]
            + """
open import Agda.Builtin.Bool using (Bool)
stationary : Orbit Bool → Bool
stationary s = {!!}
"""
        )
        with opened(source) as (_path, session, budget, _project, parent):
            proposal = session.split_result(parent, InteractionId(0), budget)
            self.assertFalse(proposal.accepted)
            self.assertTrue(proposal.rejection_code)
            self.assertFalse(
                session.case_split(parent, "s", InteractionId(0), budget).accepted
            )
            self.assertEqual(len(session.inspect_goals(parent, budget).state.goals), 1)

    def test_named_case_contract_and_missing_goal_are_not_relaxed(self):
        with opened() as (_path, session, budget, _project, parent):
            with self.assertRaises(BridgeError) as rejected:
                session.case_split(parent, "", InteractionId(0), budget)
            self.assertEqual(rejected.exception.diagnostic.code, "invalid-case-subject")
            with self.assertRaises(BridgeError) as rejected:
                session.split_result(parent, InteractionId(99), budget)
            self.assertEqual(
                rejected.exception.diagnostic.code, "result-split-goal-not-open"
            )

    def test_stale_revision_cancellation_and_elapsed_budget_prevent_dispatch(self):
        for mode in ("stale", "cancelled", "budget"):
            with (
                self.subTest(mode=mode),
                opened() as (path, session, budget, _project, parent),
            ):
                if mode == "stale":
                    path.write_text(SOURCE + "\n-- changed\n")
                elif mode == "cancelled":
                    session._cancellation.cancel()
                else:
                    # Keep the session's budget identity; simulate elapsed time
                    # without sleeping or constructing a replacement allowance.
                    object.__setattr__(budget, "started", time.monotonic() - 30)
                with patch(
                    "agdaprover.bridge.transport.os.write",
                    side_effect=AssertionError("dispatch"),
                ):
                    with self.assertRaises(BridgeError) as rejected:
                        session.split_result(parent, InteractionId(0), budget)
                self.assertIn(
                    rejected.exception.failure,
                    {
                        BridgeFailure.STALE_TOKEN,
                        BridgeFailure.CANCELLED,
                        BridgeFailure.TIMEOUT,
                    },
                )

    def test_replacement_budget_cannot_reset_the_envelope(self):
        with opened() as (_path, session, budget, _project, parent):
            with self.assertRaises(BridgeError) as rejected:
                session.split_result(parent, InteractionId(0), replace(budget))
            self.assertEqual(
                rejected.exception.diagnostic.code, "budget-object-mismatch"
            )

    def test_malformed_observation_invalidates_active_marker_then_parent_recovers(self):
        with opened() as (_path, session, budget, _project, parent):
            command = session._synthetic_command_id()
            invalid = DecodedResponse((), "0" * 64, 0)
            with patch.object(
                session.transport, "command", return_value=(command, invalid)
            ):
                with self.assertRaises(BridgeError) as rejected:
                    session.split_result(parent, InteractionId(0), budget)
            self.assertEqual(rejected.exception.failure, BridgeFailure.PROTOCOL_FAILURE)
            self.assertIsNone(session._active_state)
            self.assertTrue(
                session.split_result(parent, InteractionId(0), budget).accepted
            )


if __name__ == "__main__":
    unittest.main()
