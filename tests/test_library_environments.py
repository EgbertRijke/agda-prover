"""Library profiles must survive speculative and clean source overlays."""

from __future__ import annotations

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
from agdaprover.bridge.overlay import _relocated_manifest, materialize_project
from agdaprover.bridge.project import _parse_agda_lib, resolve_project
from agdaprover.bridge.resources import CancellationToken
from agdaprover.bridge.session import ConformingKernelSession


def mixed_project(root: Path, *, import_sorts: bool = True) -> OpenProjectRequest:
    primary = root / "primary"
    support = root / "support"
    (primary / "src").mkdir(parents=True)
    (support / "src").mkdir(parents=True)
    (primary / "primary.agda-lib").write_text(
        "name: primary\ninclude: src\ndepend: support\n"
        "flags: --no-import-sorts -- no global sort imports\n"
    )
    (support / "support.agda-lib").write_text(
        "name: support\ninclude: src\nflags: --without-K\n"
    )
    (support / "src/Support.agda").write_text(
        "module Support where\ndata Box : Set where\n  box : Box\n"
    )
    source = primary / "src/Main.agda"
    source.write_text(
        "module Main where\n"
        + ("open import Agda.Primitive using (Set)\n" if import_sorts else "")
        + "open import Support\nidentity : {A : Set} → A → A\n"
        "identity = {!!}\n"
    )
    database = root / "libraries"
    database.write_text(str(support / "support.agda-lib") + "\n")
    return OpenProjectRequest(source, library_file=database)


class LibraryParsingTests(unittest.TestCase):
    def test_relocation_does_not_sanitize_invalid_fields_or_flag_boundaries(
        self,
    ) -> None:
        text = b"name: main\ninclude: /original\nflags: --without-K\n  --exact-split\ninclude: /other\nunknown: field\n"
        moved = _relocated_manifest(text, ("source space",)).decode()
        self.assertEqual(moved.count("include:"), 2)
        self.assertIn("flags: --without-K\n  --exact-split", moved)
        self.assertIn("unknown: field", moved)
        self.assertIn("include: source\\ space", moved)

    def test_flag_spelling_is_not_an_agda_library_comment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            manifest = request.source_file.parent.parent / "primary.agda-lib"
            library = _parse_agda_lib(manifest, BridgeBudget.for_run(5))
            self.assertEqual(library.flags, ("--no-import-sorts",))


@unittest.skipUnless(shutil.which("agda"), "requires Agda 2.8")
class LibraryEnvironmentTests(unittest.TestCase):
    def test_fresh_validation_does_not_inherit_the_temporary_parent_library(
        self,
    ) -> None:
        cases = (
            (".", True, "Main", ".agda"),
            ("src", True, "Nested.Main", ".agda"),
            ("source space", False, "Main", ".lagda.md"),
            ("src", False, "Nested.Main", ".lagda.md"),
        )
        for include, named, module, suffix in cases:
            with (
                self.subTest(
                    include=include, named=named, module=module, suffix=suffix
                ),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                sources = root / include
                sources.mkdir(exist_ok=True)
                manifest = root / "local.agda-lib"
                escaped_include = include.replace(" ", "\\ ")
                manifest.write_text(
                    ("name: local\n" if named else "")
                    + f"include: {escaped_include}\nflags: --without-K\n"
                )
                registry = root / "libraries"
                registry.write_text(str(manifest) + "\n")
                source = sources / (module.replace(".", "/") + suffix)
                source.parent.mkdir(parents=True, exist_ok=True)
                text = f"module {module} where\nidentity : {{A : Set}} → A → A\nidentity = {{!!}}\n"
                if suffix == ".lagda.md":
                    text = "# A literate library\n\n```agda\n" + text + "```\n"
                source.write_text(text)
                temporary = root / "temporary"
                temporary.mkdir()
                budget = BridgeBudget.for_run(15)
                with patch.object(tempfile, "tempdir", str(temporary)):
                    session = ConformingKernelSession()
                    try:
                        opened = session.open_project(
                            OpenProjectRequest(source, library_file=registry), budget
                        )
                        loaded = session.load_module(
                            opened.project,
                            opened.root_module,
                            opened.source_revision,
                            budget,
                        )
                        self.assertIsNotNone(loaded.transition.child_state)
                        start = text.index("{!!}") + 1
                        edit = SourcePatch(
                            opened.environment_id,
                            opened.source_revision,
                            opened.root_module,
                            (
                                SourceEdit(
                                    SourceRange(start, start + 4), "{!!}", "λ x → x"
                                ),
                            ),
                        )
                        result = session.validate_patch(
                            opened.project,
                            edit,
                            PolicyProfile("test-library-overlay"),
                            budget,
                        )
                        self.assertTrue(result.verified, result.to_dict())
                        assert result.trust_report is not None
                        self.assertTrue(result.trust_report.fresh_process)
                        invalid = replace(
                            edit,
                            edits=(
                                SourceEdit(
                                    SourceRange(start, start + 4), "{!!}", "λ x → Set"
                                ),
                            ),
                        )
                        rejected = session.validate_patch(
                            opened.project,
                            invalid,
                            PolicyProfile("test-library-overlay"),
                            budget,
                        )
                        self.assertFalse(rejected.verified)
                        assert rejected.trust_report is not None
                        self.assertNotEqual(rejected.trust_report.exit_status, 0)
                        self.assertEqual(source.read_text(), text)
                    finally:
                        session.close()

    def test_escaped_include_spaces_and_comma_dependencies_round_trip(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            support = root / "support"
            (support / "src").rename(support / "source space")
            manifest = support / "support.agda-lib"
            manifest.write_text(
                manifest.read_text().replace("include: src", "include: source\\ space")
            )
            primary = root / "primary/primary.agda-lib"
            primary.write_text(
                primary.read_text().replace("depend: support", "depend: support,")
            )
            project, _ = resolve_project(request, BridgeBudget.for_run(10))
            overlay = materialize_project(
                project, root / "overlay", BridgeBudget.for_run(10), CancellationToken()
            )
            relocated, _ = resolve_project(
                replace(
                    request,
                    source_file=overlay.source_for(project.root_module),
                    library_file=overlay.library_file,
                ),
                BridgeBudget.for_run(10),
            )
            self.assertEqual(
                [s.sha256 for s in project.sources],
                [s.sha256 for s in relocated.sources],
            )

    def test_absolute_library_includes_are_relocated_not_left_live(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            manifest = root / "support/support.agda-lib"
            manifest.write_text(
                manifest.read_text().replace(
                    "include: src", f"include: {root / 'support/src'}"
                )
            )
            project, _ = resolve_project(request, BridgeBudget.for_run(10))
            overlay = materialize_project(
                project, root / "overlay", BridgeBudget.for_run(10), CancellationToken()
            )
            for path, _ in overlay.artifacts:
                if path.endswith(".agda-lib"):
                    text = (root / "overlay" / path).read_text()
                    self.assertNotIn(str(root / "support"), text)
                    self.assertIn("include: src", text)

    def test_relocated_environment_can_be_reset_without_stale_library_paths(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = mixed_project(root / "first")
            second = mixed_project(root / "second", import_sorts=False)
            budget = BridgeBudget.for_run(20)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(first, budget)
                session.load_module(
                    opened.project, opened.root_module, opened.source_revision, budget
                )
                reset = session.reset_project(second, budget)
                with self.assertRaises(BridgeError) as caught:
                    session.load_module(
                        reset.project, reset.root_module, reset.source_revision, budget
                    )
                self.assertEqual(caught.exception.failure, BridgeFailure.LOAD_FAILURE)
            finally:
                resources = session.close()
            self.assertEqual(resources.orphan_processes, 0)

    def test_changed_registration_database_invalidates_open_session(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            budget = BridgeBudget.for_run(10)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(request, budget)
                assert request.library_file is not None
                request.library_file.write_text("")
                with self.assertRaises(BridgeError) as caught:
                    session.load_module(
                        opened.project,
                        opened.root_module,
                        opened.source_revision,
                        budget,
                    )
                self.assertEqual(caught.exception.failure, BridgeFailure.STALE_TOKEN)
            finally:
                session.close()

    def test_overlay_checks_source_hash_and_charges_configuration_artifacts(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            project, _ = resolve_project(request, BridgeBudget.for_run(10))
            with self.assertRaises(BridgeError) as captured:
                materialize_project(
                    project,
                    root / "limited",
                    BridgeBudget(artifact_count=2),
                    CancellationToken(),
                )
            self.assertEqual(
                captured.exception.failure, BridgeFailure.RESOURCE_EXHAUSTED
            )
            request.source_file.write_text(
                request.source_file.read_text() + "-- changed\n"
            )
            with self.assertRaises(BridgeError) as captured:
                materialize_project(
                    project,
                    root / "changed",
                    BridgeBudget.for_run(10),
                    CancellationToken(),
                )
            self.assertEqual(captured.exception.failure, BridgeFailure.STALE_TOKEN)

    def test_library_cannot_make_unfinished_validation_look_complete(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            manifest = root / "primary/primary.agda-lib"
            manifest.write_text(
                manifest.read_text().replace(
                    "--no-import-sorts", "--no-import-sorts --allow-unsolved-metas"
                )
            )
            text = (
                request.source_file.read_text()
                + "unfinished : Box\nunfinished = {!!}\n"
            )
            request.source_file.write_text(text)
            budget = BridgeBudget.for_run(10)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(request, budget)
                start = text.index("{!!}") + 1
                patch = SourcePatch(
                    opened.environment_id,
                    opened.source_revision,
                    opened.root_module,
                    (SourceEdit(SourceRange(start, start + 4), "{!!}", "λ x → x"),),
                )
                result = session.validate_patch(
                    opened.project,
                    patch,
                    PolicyProfile("p0-restricted-term-ir"),
                    budget,
                )
                self.assertFalse(result.verified)
                self.assertIn(
                    "unsafe-checking-option", [d.code for d in result.diagnostics]
                )
            finally:
                session.close()

    def test_mixed_flags_apply_only_to_their_own_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            original = request.source_file.read_bytes()
            budget = BridgeBudget.for_run(20)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(request, budget)
                loaded = session.load_module(
                    opened.project, opened.root_module, opened.source_revision, budget
                )
                parent = loaded.transition.child_state
                self.assertIsNotNone(parent)
                assert parent is not None
                rejected = session.try_action(
                    parent, ActionInput("check-term", InteractionId(0), "box"), budget
                )
                self.assertFalse(rejected.accepted)
                self.assertEqual(
                    len(session.inspect_goals(parent, budget).state.goals), 1
                )
                result = session.try_action(
                    parent,
                    ActionInput("check-term", InteractionId(0), "λ x → x"),
                    budget,
                )
                self.assertTrue(result.accepted)
                text = original.decode()
                start = text.index("{!!}") + 1
                patch = SourcePatch(
                    opened.environment_id,
                    opened.source_revision,
                    opened.root_module,
                    (SourceEdit(SourceRange(start, start + 4), "{!!}", "λ x → x"),),
                )
                validated = session.validate_patch(
                    opened.project,
                    patch,
                    PolicyProfile("p0-restricted-term-ir"),
                    budget,
                )
                self.assertTrue(validated.verified, validated.diagnostics)
                assert validated.trust_report is not None
                self.assertTrue(validated.trust_report.fresh_process)
                artifacts = validated.trust_report.imported_artifacts
                self.assertEqual(
                    sum(path.endswith(".agda-lib") for path, _ in artifacts), 2
                )
                self.assertEqual(request.source_file.read_bytes(), original)
            finally:
                resources = session.close()
            self.assertEqual(resources.orphan_processes, 0)

    def test_library_flags_are_not_silently_ignored_on_first_load(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory), import_sorts=False)
            budget = BridgeBudget.for_run(10)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(request, budget)
                with self.assertRaises(BridgeError) as caught:
                    session.load_module(
                        opened.project,
                        opened.root_module,
                        opened.source_revision,
                        budget,
                    )
                self.assertEqual(caught.exception.failure, BridgeFailure.LOAD_FAILURE)
                self.assertIn("Set", str(caught.exception))
            finally:
                session.close()

    def test_changed_library_manifest_invalidates_an_open_environment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            budget = BridgeBudget.for_run(10)
            session = ConformingKernelSession()
            try:
                opened = session.open_project(request, budget)
                manifest = Path(directory) / "support/support.agda-lib"
                manifest.write_text(manifest.read_text() + "-- changed\n")
                with self.assertRaises(BridgeError) as caught:
                    session.load_module(
                        opened.project,
                        opened.root_module,
                        opened.source_revision,
                        budget,
                    )
                self.assertEqual(caught.exception.failure, BridgeFailure.STALE_TOKEN)
            finally:
                session.close()

    def test_flags_and_source_ownership_are_in_the_environment_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            project, _ = resolve_project(request, BridgeBudget.for_run(10))
            self.assertIn("--no-import-sorts", project.options)
            self.assertNotIn("--no-import-sorts", project.command_options)
            self.assertEqual(
                {s.module.name: s.library_name for s in project.sources},
                {"Main": "primary", "Support": "support"},
            )
            global_request = replace(
                request, options=(*request.options, "--no-import-sorts")
            )
            global_project, _ = resolve_project(
                global_request, BridgeBudget.for_run(10)
            )
            self.assertEqual(project.options, global_project.options)
            self.assertNotEqual(project.environment_id, global_project.environment_id)
