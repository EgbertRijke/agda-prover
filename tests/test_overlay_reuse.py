"""Root-only revisions may retain imports, never old proof-state tokens."""

import shutil
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

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
from agdaprover.bridge.resources import CancellationToken
from agdaprover.bridge.session import ConformingKernelSession
from agdaprover.resource_budget import ResourceLimitError


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class OverlayReuseTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.first = self.project("first")
        self.second = self.project("second")
        self.budget = BridgeBudget(wall_seconds=30, cpu_seconds=30)

    def project(self, name):
        root = self.root / name
        root.mkdir()
        (root / "local.agda-lib").write_text("name: local\ninclude: .\n")
        (root / "libraries").write_text(str(root / "local.agda-lib") + "\n")
        (root / "Support.agda").write_text(
            "{-# OPTIONS --safe #-}\nmodule Support where\ndata U : Set where u : U\n"
        )
        source = root / "Main.agda"
        source.write_text(
            "module Main where\nopen import Support\nvalue : U\nvalue = {!!}\n"
        )
        return OpenProjectRequest(source, library_file=root / "libraries")

    def load(self, session, opened):
        return session.load_module(
            opened.project, opened.root_module, opened.source_revision, self.budget
        )

    def test_only_opted_in_root_revision_keeps_process_and_invalidates_tokens(self):
        self.second.source_file.write_text(
            self.second.source_file.read_text() + "\n-- new revision\n"
        )
        for enabled in (False, True):
            with (
                patch.dict(
                    "os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": str(int(enabled))}
                ),
                ConformingKernelSession() as session,
            ):
                first = session.open_project(self.first, self.budget)
                parent = self.load(session, first).transition.child_state
                original_paths = dict(session._runtime_sources)
                second = session.reset_project(self.second, self.budget)
                with self.assertRaises(BridgeError):
                    session.inspect_goals(parent, self.budget)
                result = self.load(session, second)
                self.assertEqual(result.state.goals[0].target.text, "U")
                self.assertEqual(
                    session.transport.process_generation, 1 if enabled else 2
                )
                self.assertEqual(
                    dict(session._runtime_sources) == original_paths, enabled
                )
                self.assertEqual(session.root_overlay_reuses, int(enabled))
            self.assertEqual(session._last_resources.orphan_processes, 0)

    def test_changed_root_has_fresh_semantics_and_fresh_validation(self):
        text = (
            "module Main where\nopen import Support\n"
            "Chosen : Set\nChosen = U → U\n"
            "value : Chosen\nvalue = {!!}\n"
        )
        self.second.source_file.write_text(text)
        with (
            patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
            ConformingKernelSession() as session,
        ):
            first = session.open_project(self.first, self.budget)
            self.load(session, first)
            second = session.reset_project(self.second, self.budget)
            parent = self.load(session, second).transition.child_state
            for expression, expected in (("u", False), ("λ x → x", True)):
                checked = session.try_action(
                    parent,
                    ActionInput("check-term", InteractionId(0), expression),
                    self.budget,
                )
                self.assertEqual(checked.accepted, expected)
            start = text.index("{!!}") + 1
            validated = session.validate_patch(
                second.project,
                SourcePatch(
                    second.environment_id,
                    second.source_revision,
                    second.root_module,
                    (SourceEdit(SourceRange(start, start + 4), "{!!}", "λ x → x"),),
                ),
                PolicyProfile("p0-restricted-term-ir"),
                self.budget,
            )
            self.assertTrue(validated.verified, validated.diagnostics)
            self.assertTrue(validated.trust_report.fresh_process)
            self.assertEqual(session.root_overlay_reuses, 1)

    def test_scoped_mutual_and_shared_meta_revisions_match_fresh_sessions(self):
        bodies = (
            "private\n  hidden : U\n  hidden = u\n"
            "module Scoped (A : Set) where\n"
            "  mutual\n    first : A → A\n    second : A → A\n"
            "    first x = second x\n    second x = x\n"
            "  value : A → U\n  value = {!!}\n",
            "T : Set\nT = {!!}\nvalue : T\nvalue = {!!}\n",
        )
        for body in bodies:
            self.second.source_file.write_text(
                "module Main where\nopen import Support\n" + body
            )
            with (
                self.subTest(body=body),
                patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
                ConformingKernelSession() as session,
                ConformingKernelSession() as fresh,
            ):
                self.load(session, session.open_project(self.first, self.budget))
                reused = self.load(
                    session, session.reset_project(self.second, self.budget)
                )
                clean = self.load(fresh, fresh.open_project(self.second, self.budget))
                self.assertEqual(
                    reused.state.structural_hash, clean.state.structural_hash
                )
                self.assertEqual(reused.state.goals, clean.state.goals)
                self.assertEqual(reused.state.constraints, clean.state.constraints)
                self.assertEqual(session.root_overlay_reuses, 1)

    def test_failed_load_then_repair_does_not_reuse_old_root_state(self):
        self.second.source_file.write_text(
            "module Main where\nopen import Support\nbad : U\nbad = λ x → x\n"
        )
        repaired = self.project("repaired")
        with (
            patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
            ConformingKernelSession() as session,
        ):
            first = session.open_project(self.first, self.budget)
            parent = self.load(session, first).transition.child_state
            second = session.reset_project(self.second, self.budget)
            with self.assertRaises(BridgeError):
                self.load(session, second)
            with self.assertRaises(BridgeError):
                session.inspect_goals(parent, self.budget)
            loaded = self.load(session, session.reset_project(repaired, self.budget))
            self.assertEqual(loaded.state.goals[0].target.text, "U")
            self.assertEqual(session.root_overlay_reuses, 2)

    def test_publication_failure_keeps_previous_epoch_and_bytes(self):
        self.second.source_file.write_text(
            self.second.source_file.read_text() + "-- revision\n"
        )
        for failure in ("io", "deadline", "cancel", "quota"):
            with (
                self.subTest(failure=failure),
                patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
                ConformingKernelSession() as session,
            ):
                first = session.open_project(self.first, self.budget)
                parent = self.load(session, first).transition.child_state
                original = session._runtime_sources[first.root_module]
                before = original.read_bytes()
                publish = session._publish_root_reuse

                def fail_publication(reuse, budget, failure=failure, publish=publish):
                    if failure == "io":
                        with patch(
                            "agdaprover.bridge.session.os.replace",
                            side_effect=OSError("injected"),
                        ):
                            publish(reuse, budget)
                    elif failure == "deadline":
                        publish(reuse, BridgeBudget(wall_seconds=1e-9, cpu_seconds=30))
                    elif failure == "quota":
                        with patch(
                            "agdaprover.bridge.session.charge_io",
                            side_effect=ResourceLimitError("injected quota"),
                        ):
                            publish(reuse, budget)
                    else:
                        cancelled = CancellationToken()
                        cancelled.cancel()
                        with patch.object(session, "_cancellation", cancelled):
                            publish(reuse, budget)

                with patch.object(session, "_publish_root_reuse", fail_publication):
                    with self.assertRaises(
                        ResourceLimitError if failure == "quota" else BridgeError
                    ) as raised:
                        session.reset_project(self.second, self.budget)
                if failure != "quota":
                    self.assertEqual(
                        raised.exception.failure,
                        {
                            "io": BridgeFailure.RESOURCE_EXHAUSTED,
                            "deadline": BridgeFailure.TIMEOUT,
                            "cancel": BridgeFailure.CANCELLED,
                        }[failure],
                    )
                self.assertEqual(original.read_bytes(), before)
                self.assertEqual(list(original.parent.glob(".agdaprover-root-*")), [])
                self.assertEqual(
                    len(session.inspect_goals(parent, self.budget).state.goals), 1
                )
                self.assertEqual(session.root_overlay_reuses, 0)

    def test_tampered_old_overlay_rebuilds_instead_of_reusing(self):
        with (
            patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
            ConformingKernelSession() as session,
        ):
            first = session.open_project(self.first, self.budget)
            self.load(session, first)
            old = session._runtime_sources[first.root_module]
            old.write_text("module Main where\n-- unexpected content\n")
            second = session.reset_project(self.second, self.budget)
            self.load(session, second)
            self.assertEqual(session.root_overlay_reuses, 0)
            self.assertEqual(session.transport.process_generation, 2)

    def test_dependency_options_manifest_or_module_routing_changes_rebuild(self):
        for mutation in (
            "dependency",
            "options",
            "source-options",
            "manifest",
            "routing",
        ):
            request = self.project(mutation)
            if mutation == "dependency":
                (request.source_file.parent / "Support.agda").write_text(
                    "module Support where\ndata U : Set where other : U\n"
                )
            elif mutation == "options":
                request = replace(request, options=("--without-K",))
            elif mutation == "source-options":
                request.source_file.write_text(
                    "{-# OPTIONS --safe #-}\n" + request.source_file.read_text()
                )
            elif mutation == "manifest":
                (request.source_file.parent / "local.agda-lib").write_text(
                    "name: local\ninclude: .\nflags: --without-K\n"
                )
            else:
                (request.source_file.parent / "More.agda").write_text(
                    "module More where\n"
                )
                request.source_file.write_text(
                    request.source_file.read_text() + "\nopen import More\n"
                )
            with (
                self.subTest(mutation=mutation),
                patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
                ConformingKernelSession() as session,
            ):
                first = session.open_project(self.first, self.budget)
                self.load(session, first)
                second = session.reset_project(request, self.budget)
                self.load(session, second)
                self.assertEqual(session.transport.process_generation, 2)

    def test_no_library_root_reuses_paths_and_ignores_ambient_interfaces(self):
        plain = self.root / "plain"
        plain.mkdir()
        source = plain / "Main.agda"
        source.write_text("module Main where\nid : {A : Set} → A → A\nid = {!!}\n")
        # This is not a cache input. The bridge copies sources, never ambient
        # interfaces, and the pinned kernel still checks the revised root.
        (plain / "Main.agdai").write_bytes(b"untrusted interface")
        with (
            patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
            ConformingKernelSession() as session,
        ):
            request = OpenProjectRequest(source)
            first = session.open_project(request, self.budget)
            self.load(session, first)
            paths = dict(session._runtime_sources)
            source.write_text(source.read_text() + "-- root changed\n")
            self.load(session, session.reset_project(request, self.budget))
            self.assertEqual(session._runtime_sources, paths)
            self.assertEqual(session.root_overlay_reuses, 1)

    def test_damaged_staging_cannot_be_adopted_on_cache_miss(self):
        from agdaprover.bridge import session as implementation

        materialize = implementation.materialize_project
        with (
            patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"}),
            ConformingKernelSession() as session,
        ):
            first = session.open_project(self.first, self.budget)
            parent = self.load(session, first).transition.child_state

            def damage(*args, **kwargs):
                overlay = materialize(*args, **kwargs)
                overlay.source_for(first.root_module).unlink()
                return overlay

            with patch.object(implementation, "materialize_project", damage):
                with self.assertRaises(BridgeError):
                    session.reset_project(self.second, self.budget)
            self.assertEqual(
                len(session.inspect_goals(parent, self.budget).state.goals), 1
            )
            self.assertEqual(session.root_overlay_reuses, 0)


if __name__ == "__main__":
    unittest.main()
