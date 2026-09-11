"""Agda 2.8 interaction conformance: syntax observations are not proofs."""

import shutil
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from agdaprover.bridge.compat_p0 import AgdaSession
from agdaprover.bridge.contracts import BridgeError, BridgeFailure, InteractionId
from agdaprover.bridge.interaction import ClauseAction, RewriteMode
from agdaprover.bridge.operations import ReductionPolicy, TermInput
from agdaprover.bridge.versions.agda_2_8 import Agda28Adapter, DecodedResponse, RawEvent
from agdaprover.reconstruction import apply_source_edit, reconstruct_case_split

PREFIX = """{-# OPTIONS --safe --without-K #-}
module Operations where
data Flag : Set where on off : Flag
data Rel {A : Set} (x : A) : A → Set where point : Rel x x
identity : {A : Set} → A → A
identity x = x
Alias : Set
Alias = Flag
"""


class InteractionCodecTests(unittest.TestCase):
    def test_missing_obligation_reports_cannot_be_interpreted_as_zero(self):
        adapter = Agda28Adapter()

        def response(info):
            return DecodedResponse(
                (RawEvent("DisplayInfo", {"info": info}),), "0" * 64, 100
            )

        constraints = response({"kind": "Constraints", "constraints": []})
        metas = response(
            {"kind": "AllGoalsWarnings", "visibleGoals": [], "invisibleGoals": []}
        )
        self.assertEqual(adapter.residual_obligation_counts(constraints, metas), (0, 0))
        for bad in (
            replace(metas, events=()),
            replace(metas, events=metas.events * 2),
            response({"kind": "AllGoalsWarnings", "visibleGoals": []}),
            response(
                {"kind": "AllGoalsWarnings", "visibleGoals": [], "invisibleGoals": [{}]}
            ),
        ):
            with self.assertRaises(ValueError):
                adapter.residual_obligation_counts(constraints, bad)
        with self.assertRaises(ValueError):
            adapter.residual_obligation_counts(replace(constraints, events=()), metas)

    def test_inferred_and_computed_views_reject_wrong_identity_and_missing_text(self):
        adapter = Agda28Adapter()
        for kind, decode in (
            ("InferredType", adapter.inferred),
            ("NormalForm", adapter.normalized),
        ):
            row = {
                "kind": "DisplayInfo",
                "info": {
                    "kind": "GoalSpecific",
                    "interactionPoint": {"id": 3},
                    "goalInfo": {"kind": kind, "expr": "Flag"},
                },
            }
            valid = DecodedResponse((RawEvent("DisplayInfo", row),), "0" * 64, 100)
            self.assertTrue(decode(valid, 3).accepted)
            for bad in (
                replace(valid, events=()),
                replace(valid, events=valid.events * 2),
            ):
                with self.assertRaises(ValueError):
                    decode(bad, 3)
            with self.assertRaises(ValueError):
                decode(valid, 4)
            for text in (None, 3, "", "\x00"):
                bad = {
                    **row,
                    "info": {**row["info"], "goalInfo": {"kind": kind, "expr": text}},
                }
                with self.assertRaises(ValueError):
                    decode(replace(valid, events=(RawEvent("DisplayInfo", bad),)), 3)

    def test_all_agda_rewrite_modes_are_distinct_and_unicode_is_literal(self):
        adapter = Agda28Adapter()
        agda_modes = ("AsIs", "Instantiated", "HeadNormal", "Simplified", "Normalised")
        for mode, spelling in zip(RewriteMode, agda_modes, strict=True):
            self.assertIn(spelling, adapter.inspect_goal(3, mode))
            self.assertIn(spelling, adapter.infer(3, "π α", mode))
            self.assertIn(spelling, adapter.helper_type(3, "h α", mode))
            self.assertNotIn("\\u", adapter.helper_type(3, "h α", mode))

    def test_clause_intents_round_trip_and_reject_mixed_or_malformed_requests(self):
        adapter = Agda28Adapter()
        for action, subject in (
            (ClauseAction("variables", ("x", "y")), "x y"),
            (ClauseAction("result"), ""),
            (ClauseAction("ellipsis"), "."),
        ):
            self.assertEqual(ClauseAction.from_dict(action.to_dict()), action)
            self.assertEqual(
                adapter.make_clause(3, action), f'Cmd_make_case 3 noRange "{subject}"'
            )
        for kind, subjects in [
            ("wrong", ()),
            ("variables", ()),
            ("result", ("x",)),
            ("variables", ("x y",)),
            ("variables", (".",)),
            ("variables", (3,)),
        ]:
            with (
                self.subTest(kind=kind, subjects=subjects),
                self.assertRaises(ValueError),
            ):
                ClauseAction(kind, subjects)

    def test_helper_response_requires_one_matching_interaction_and_signature(self):
        adapter = Agda28Adapter()
        row = {
            "kind": "DisplayInfo",
            "info": {
                "kind": "GoalSpecific",
                "interactionPoint": {"id": 3},
                "goalInfo": {"kind": "HelperFunction", "signature": "h : A → A"},
            },
        }
        response = DecodedResponse((RawEvent("DisplayInfo", row),), "0" * 64, 100)
        self.assertEqual(adapter.helper_signature(response, 3), "h : A → A")
        for candidate in (
            replace(response, events=()),
            replace(response, events=response.events * 2),
        ):
            with self.assertRaises(ValueError):
                adapter.helper_signature(candidate, 3)
        for point in ({"id": 4}, {"id": True}, {}, None):
            bad = {**row, "info": {**row["info"], "interactionPoint": point}}
            with self.assertRaises(ValueError):
                adapter.helper_signature(
                    replace(response, events=(RawEvent("DisplayInfo", bad),)), 3
                )


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class InteractionConformanceTests(unittest.TestCase):
    def test_light_obligation_counts_match_full_inspection_with_constant_commands(self):
        _path, _source, session, _goals = self.opened(
            "witness : Flag → Rel on on\nwitness x = point\nf : Rel on on\nf = {!!}\ng : Flag\ng = {!!}\n"
        )
        parent = session.current_state()
        child = session.commit_proof_action(
            parent, kind="give", goal_id=0, expression="witness _"
        ).child_state
        self.assertIsNotNone(child)
        for state in (parent, child, parent):
            full = session._session.inspect_goals(state, session._budget).state
            expected = (
                sum(
                    m.status == "open" and m.interaction_id is None for m in full.metas
                ),
                len(full.constraints),
            )
            before = session._session.transport.cost.commands
            self.assertEqual(session.internal_obligation_counts(state), expected)
            self.assertEqual(session._session.transport.cost.commands - before, 2)
        self.assertTrue(session.check_candidate(0, "point").accepted)

    def test_refinement_and_completion_do_not_confuse_hidden_metas_with_solutions(self):
        _path, _source, session, goals = self.opened(
            "witness : Flag → Rel on on\nwitness x = point\nf : Rel on on\nf = {!!}\n"
        )
        parent = session.current_state()
        self.assertTrue(session.check_candidate(0, "witness _").accepted)
        self.assertFalse(session.check_complete_candidate(0, "witness _").accepted)
        self.assertEqual(session.current_state(), parent)
        self.assertTrue(session.check_complete_candidate(0, "point").accepted)
        refined = session.commit_proof_action(
            parent, kind="refine", goal_id=0, expression="witness"
        )
        self.assertTrue(refined.accepted)
        self.assertEqual(len(refined.generated_goals), 1)
        self.assertTrue(session.check_complete_candidate(0, "witness on").accepted)
        self.assertEqual(session.inspect_goal(goals[0]).target, "Rel on on")

    def opened(self, suffix):
        directory = self.enterContext(tempfile.TemporaryDirectory())
        path = Path(directory) / "Operations.agda"
        source = PREFIX + suffix
        path.write_text(source)
        session = self.enterContext(AgdaSession(timeout_seconds=20))
        goals = session.load_module(path)
        self.addCleanup(lambda: self.assertEqual(path.read_text(), source))
        return path, source, session, goals

    def test_multiple_variable_split_agrees_with_sequential_agda_splitting(self):
        _path, source, session, goals = self.opened(
            "f : Flag → Flag → Flag\nf x y = {!!}\n"
        )
        state = session.current_state()
        batch = session.check_clause_action(
            state, goal_id=0, action=ClauseAction("variables", ("x", "y"))
        )
        self.assertTrue(batch.accepted, batch.diagnostic)
        self.assertEqual(len(batch.clauses), 4)
        self.assertTrue(all("on" in c or "off" in c for c in batch.clauses))
        edit = reconstruct_case_split(source, goals[0], batch.clauses)
        self.assertIn("f on off", apply_source_edit(source, edit))
        self.assertEqual(session.current_state(), state)
        self.assertTrue(session.check_candidate(0, "x").accepted)
        rejected = session.check_clause_action(
            state, goal_id=0, action=ClauseAction("variables", ("x", "missing"))
        )
        self.assertFalse(rejected.accepted)
        self.assertTrue(session.check_candidate(0, "y").accepted)

    def test_hidden_and_instance_binders_are_bound_by_agda_not_eliminated(self):
        _path, _source, session, _goals = self.opened(
            "f : {x : Flag} ⦃ y : Flag ⦄ → Flag\nf = {!!}\n"
        )
        state = session.current_state()
        batch = session.check_clause_action(
            state, goal_id=0, action=ClauseAction("variables", ("x", "y"))
        )
        self.assertTrue(batch.accepted, batch.diagnostic)
        self.assertEqual(len(batch.clauses), 1)
        self.assertIn("{x}", batch.clauses[0])
        self.assertIn("⦃ y ⦄", batch.clauses[0])

    def test_ellipsis_expansion_and_illegal_module_parameter_split(self):
        _path, source, session, goals = self.opened(
            "f : Flag → Flag\nf x with x\n... | on = {!!}\n... | off = off\n"
        )
        split = session.check_clause_action(
            session.current_state(), goal_id=0, action=ClauseAction("ellipsis")
        )
        self.assertTrue(split.accepted, split.diagnostic)
        self.assertFalse(split.clauses[0].startswith("..."))
        self.assertIn(
            "f ",
            apply_source_edit(
                source, reconstruct_case_split(source, goals[0], split.clauses)
            ),
        )
        _path, _source, scoped, _ = self.opened(
            "module _ (x : Flag) where\n  f : Flag\n  f = {!!}\n"
        )
        rejected = scoped.check_clause_action(
            scoped.current_state(), goal_id=0, action=ClauseAction("variables", ("x",))
        )
        self.assertFalse(rejected.accepted)
        self.assertTrue(scoped.check_candidate(0, "x").accepted)

    def test_rewrite_views_do_not_change_canonical_state_or_scope(self):
        _path, _source, session, goals = self.opened(
            "f : (x : Alias) → Rel (identity x) x\nf x = {!!}\n"
        )
        state = session.current_state()
        canonical = session.inspect_goal(goals[0])
        views = {
            mode: session.inspect_goal_view(state, goal_id=0, mode=mode)
            for mode in RewriteMode
        }
        self.assertIn("identity", views[RewriteMode.AS_IS].target)
        self.assertNotIn("identity", views[RewriteMode.NORMAL].target)
        for mode, view in views.items():
            self.assertEqual(view.goal_id, 0)
            self.assertEqual(view.source_range, canonical.source_range)
            self.assertIsNotNone(
                session.infer_type(state, goal_id=0, expression="x", mode=mode)
            )
        self.assertEqual(session.inspect_goal(goals[0]), canonical)
        self.assertEqual(session.current_state(), state)
        self.assertTrue(session.check_candidate(0, "point").accepted)
        for policy in (ReductionPolicy.AS_IS, ReductionPolicy.SIMPLIFIED):
            with self.assertRaises(BridgeError) as error:
                session._session.normalize(
                    state,
                    TermInput("x"),
                    policy,
                    session._budget,
                    interaction_id=InteractionId(0),
                )
            self.assertEqual(
                error.exception.failure, BridgeFailure.UNSUPPORTED_CAPABILITY
            )

    def test_helper_inference_generalizes_compounds_and_remains_observational(self):
        _path, _source, session, goals = self.opened(
            "f : {A : Set} {x y z : A} → Rel x y → Rel y z → Rel x z\nf p q = {!!}\n"
        )
        state = session.current_state()
        original = session.inspect_goal(goals[0])
        for mode in RewriteMode:
            signature = session.helper_signature(
                state, goal_id=0, application="helper p q", mode=mode
            )
            self.assertTrue(signature.startswith("helper :"), signature)
            self.assertIn("Rel", signature)
        self.assertIsNone(
            session.helper_signature(state, goal_id=0, application="helper missing")
        )
        compound = session.helper_signature(
            state, goal_id=0, application="helper (identity p) q"
        )
        self.assertIsNotNone(compound)
        self.assertEqual(session.inspect_goal(goals[0]), original)
        self.assertEqual(session.current_state(), state)
        self.assertTrue(session.check_candidate(0, "(λ { point r → r }) p q").accepted)

    def test_local_lambda_and_let_bound_names_are_not_case_coordinates(self):
        for definition, name in (
            ("f : Flag → Flag\nf = λ x → {!!}\n", "x"),
            ("f : Flag\nf = let x = on in {!!}\n", "x"),
        ):
            with self.subTest(definition=definition):
                _path, _source, session, _ = self.opened(definition)
                split = session.check_clause_action(
                    session.current_state(),
                    goal_id=0,
                    action=ClauseAction("variables", (name,)),
                )
                self.assertFalse(split.accepted)
                self.assertTrue(session.check_complete_candidate(0, "on").accepted)
