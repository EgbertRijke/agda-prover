"""Public requests and all checking workspaces retain explicit library inputs."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from test_library_environments import mixed_project

from agdaprover.application import default_application, inspect_source
from agdaprover.bridge.source_prefix import parser_executable
from agdaprover.cli import build_parser, task_from_arguments
from agdaprover.contracts import TaskSpec, task_identity
from agdaprover.editor_api import EDITOR_REQUEST_SCHEMA, EditorRequest, source_sha256
from agdaprover.guided import guided_prove
from agdaprover.interactive import launch_interactive_run
from agdaprover.kernel.p0 import AgdaSession
from agdaprover.project_configuration import ProjectConfiguration
from agdaprover.resource_budget import ResourceLimits, ResourceScope, charge_io
from agdaprover.verification import prepare_project_overlay, validate_reconstruction


class ConfigurationContractTests(unittest.TestCase):
    def test_inspection_honors_the_callers_resource_envelope(self) -> None:
        limits = ResourceLimits(cpu_seconds=25, memory_bytes=3 * 1024**3)
        with (
            ResourceScope(limits),
            patch(
                "agdaprover.application.inspection.ConformingKernelSession"
            ) as session,
        ):
            opened = session.return_value.__enter__.return_value.open_project
            opened.side_effect = ValueError("stop after capturing the budget")
            result = inspect_source(Path("Main.agda"), timeout_seconds=10)
            budget = opened.call_args.args[1]
            self.assertEqual(budget.memory_bytes, limits.memory_bytes)
            self.assertEqual(budget.cpu_seconds, limits.cpu_seconds)
            self.assertEqual(budget.wall_seconds, 10)
            self.assertEqual(result.exit_code, 4)

        scope = ResourceScope(ResourceLimits(io_bytes=1))
        scope.open()
        try:
            with patch("agdaprover.application.inspection.project_request") as request:
                request.side_effect = lambda *_: charge_io(2)
                result = inspect_source(Path("Main.agda"))
            self.assertEqual(result.exit_code, 6)
            self.assertEqual(result.payload["status"], "resource-exhausted")
        finally:
            self.assertIsNotNone(scope.finish())

    def test_round_trip_and_rejected_configuration(self) -> None:
        configuration = ProjectConfiguration("agda", Path("registry"), ("--without-K",))
        self.assertEqual(
            ProjectConfiguration.from_dict(configuration.to_dict()), configuration
        )
        for field, value in (
            ("schema_version", "future"),
            ("options", "--without-K"),
            ("library_file", ""),
            ("executable", False),
            ("extra", 1),
        ):
            with self.subTest(field=field), self.assertRaises(ValueError):
                ProjectConfiguration.from_dict(
                    {**configuration.to_dict(), field: value}
                )
        for option in (
            "-i/tmp",
            "--library-file=/tmp/evil",
            "--no-libraries",
            "--only-scope-checking",
            "--compile",
            "--html-dir=/tmp",
            "--without-K --safe",
            "--safe\x00",
        ):
            with self.subTest(option=option), self.assertRaises(ValueError):
                ProjectConfiguration(options=(option,))

    def test_cli_and_task_identity(self) -> None:
        parser = build_parser()
        baseline = parser.parse_args(["prove", "Main.agda"])
        task = task_from_arguments(
            baseline, baseline.source, baseline.ranker, baseline.model
        )
        self.assertIsNone(task.project_configuration)
        empty = parser.parse_args(["prove", "Main.agda", "--no-default-agda-options"])
        self.assertEqual(
            task_from_arguments(
                empty, empty.source, empty.ranker, empty.model
            ).project_configuration.options,
            (),
        )
        arguments = parser.parse_args(
            ["prove", "Main.agda", "--library-file", "registry", "--agda-option=--safe"]
        )
        configured = task_from_arguments(
            arguments, arguments.source, arguments.ranker, arguments.model
        )
        self.assertEqual(
            configured.project_configuration,
            ProjectConfiguration("agda", Path("registry"), ("--safe",)),
        )
        options = dict(
            source_hash="source",
            mode="prove",
            policy_profile="test",
            toolchain_id=None,
            model_ids={},
        )
        self.assertNotEqual(
            task_identity(task, **options), task_identity(configured, **options)
        )


@unittest.skipUnless(shutil.which("agda"), "requires Agda 2.8")
class PublicLibraryProjectTests(unittest.TestCase):
    def test_registered_imports_survive_case_and_guided_search(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            support = root / "support/src/Support.agda"
            support.write_text(
                support.read_text()
                + "data Wrap (A : Set) : Set where\n  wrap : A → Wrap A\n"
            )
            source = request.source_file.read_text().replace(
                "identity : {A : Set} → A → A\nidentity = {!!}",
                "unwrap : {A : Set} → Wrap A → A\nunwrap = {!!}",
            )
            request.source_file.write_text(source)
            configuration = ProjectConfiguration(library_file=request.library_file)
            task = TaskSpec(
                request.source_file,
                project_configuration=configuration,
                timeout_seconds=20,
            )
            result = default_application.prove(task)
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertGreater(result.cost.case_split_checks, 0)
            with AgdaSession(
                project_configuration=configuration, timeout_seconds=10
            ) as session:
                goal = session.inspect_goal(session.load_module(request.source_file)[0])
            guided = guided_prove(
                request.source_file,
                goal,
                action_budget=100,
                timeout_seconds=20,
                max_depth=8,
                focused_model=None,
                refinement_model=None,
                project_configuration=configuration,
            )
            self.assertEqual(guided.status, "solved", guided.diagnostic)
            validation, _ = validate_reconstruction(
                request.source_file,
                guided.patch,
                project_configuration=configuration,
                timeout_seconds=10,
            )
            self.assertTrue(validation["checked"], validation)

    def test_empty_global_options_preserve_a_library_using_K(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            (root / "support/support.agda-lib").write_text(
                "name: support\ninclude: src\n"
            )
            support = root / "support/src/Support.agda"
            support.write_text(
                support.read_text() + "open import Agda.Builtin.Equality\n"
                "k : {A : Set} {x : A} (p : x ≡ x) → p ≡ refl\nk refl = refl\n"
            )
            ordinary = ProjectConfiguration(library_file=request.library_file)
            rejected = inspect_source(
                request.source_file, project_configuration=ordinary, timeout_seconds=10
            )
            self.assertEqual(rejected.exit_code, 4)
            configuration = ProjectConfiguration(
                library_file=request.library_file, options=()
            )
            result = default_application.prove_prefix(
                TaskSpec(
                    request.source_file,
                    project_configuration=configuration,
                    timeout_seconds=20,
                )
            )
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertEqual(
                result.trust_report["checking_environment"]["command_options"], []
            )

    def test_original_library_change_cannot_be_accepted_after_overlay_search(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            configuration = ProjectConfiguration(library_file=request.library_file)
            manifest = request.source_file.parent.parent / "primary.agda-lib"
            original = manifest.read_text()

            def changed(*args, **kwargs):
                manifest.write_text(original + "-- changed during search\n")
                return validate_reconstruction(*args, **kwargs)

            with patch("agdaprover.joint.validate_reconstruction", side_effect=changed):
                result = default_application.prove_prefix(
                    TaskSpec(
                        request.source_file,
                        project_configuration=configuration,
                        timeout_seconds=20,
                    )
                )
            self.assertEqual(result.status, "invalid-task", result.diagnostics)
            self.assertIn("checking input changed", str(result.diagnostics))

    def test_explicit_missing_registry_is_an_input_error(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            result = default_application.prove_prefix(
                TaskSpec(
                    request.source_file,
                    timeout_seconds=10,
                    project_configuration=ProjectConfiguration(
                        library_file=Path(directory) / "missing"
                    ),
                )
            )
            self.assertEqual(result.status, "invalid-task", result.diagnostics)

    def test_interactive_worker_and_acceptance_keep_configuration(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            configuration = ProjectConfiguration(library_file=request.library_file)
            controller = launch_interactive_run(
                TaskSpec(
                    request.source_file,
                    timeout_seconds=20,
                    project_configuration=configuration,
                ),
                variation_path=root / "variation.json",
                result_path=root / "result.json",
            )
            try:
                deadline = time.monotonic() + 25
                while (
                    controller.state not in {"completed", "failed"}
                    and time.monotonic() < deadline
                ):
                    time.sleep(0.02)
                result = controller.result()
                self.assertIsNotNone(result)
                self.assertEqual(
                    result["status"], "verified", result.get("diagnostics")
                )
                variation = controller.principal_variation()
                self.assertTrue(variation["acceptance_options"])
                accepted = controller.accept_goal(
                    variation["acceptance_options"][0]["goal_id"],
                    variation["variation_id"],
                )
                self.assertEqual(accepted["status"], "verified")
                self.assertIn(
                    "--no-default-libraries",
                    accepted["trust_report"]["checker_command"],
                )
            finally:
                controller.stop()

    def test_public_inspect_prove_prefix_and_step(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            configuration = ProjectConfiguration(library_file=request.library_file)
            task = TaskSpec(
                request.source_file,
                max_candidates=60,
                timeout_seconds=20,
                project_configuration=configuration,
            )
            inspected = inspect_source(
                request.source_file,
                project_configuration=configuration,
                timeout_seconds=10,
            )
            self.assertEqual(inspected.exit_code, 0, inspected.payload)
            original = request.source_file.read_bytes()
            for method in (default_application.prove, default_application.prove_prefix):
                with self.subTest(operation=method.__name__):
                    result = method(task)
                    self.assertEqual(result.status, "verified", result.to_dict())
                    self.assertTrue(result.validation["fresh_process"])
                    self.assertIn(
                        "--no-default-libraries", result.trust_report["checker_command"]
                    )
                    self.assertEqual(request.source_file.read_bytes(), original)
            step = default_application.step(task)
            self.assertEqual(step.status, "accepted-step", step.to_dict())

    def test_nested_overlay_rebinds_registry_and_rejects_lost_flags(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            configuration = ProjectConfiguration(library_file=request.library_file)
            moved = prepare_project_overlay(
                request.source_file,
                request.source_file.read_text(),
                root / "first",
                project_configuration=configuration,
                timeout_seconds=10,
            )
            moved_again = prepare_project_overlay(
                moved.source_file,
                moved.source_file.read_text(),
                root / "second",
                project_configuration=moved.configuration,
                timeout_seconds=10,
            )
            self.assertNotEqual(
                configuration.library_file, moved.configuration.library_file
            )
            self.assertNotEqual(
                moved.configuration.library_file, moved_again.configuration.library_file
            )
            self.assertNotIn(
                str(root / "primary"),
                moved_again.configuration.library_file.read_text(),
            )
            outcome = default_application.prove_prefix(
                TaskSpec(
                    moved_again.source_file,
                    project_configuration=moved_again.configuration,
                    timeout_seconds=20,
                )
            )
            self.assertEqual(outcome.status, "verified", outcome.to_dict())
            invalid = moved_again.source_file.read_text().replace(
                "open import Agda.Primitive using (Set)\n", ""
            )
            moved_again.source_file.write_text(invalid)
            outcome = default_application.prove_prefix(
                TaskSpec(
                    moved_again.source_file,
                    project_configuration=moved_again.configuration,
                    timeout_seconds=20,
                )
            )
            self.assertNotEqual(outcome.status, "verified")

    @unittest.skipUnless(parser_executable(), "requires the source-prefix parser")
    def test_prefix_validation_with_unrelated_later_hole(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            request = mixed_project(Path(directory))
            source = request.source_file.read_text() + "later : Box\nlater = {!!}\n"
            request.source_file.write_text(source)
            task = TaskSpec(
                request.source_file,
                goal_id=0,
                timeout_seconds=20,
                project_configuration=ProjectConfiguration(
                    library_file=request.library_file
                ),
            )
            result = default_application.prove_prefix(task)
            self.assertEqual(result.status, "verified", result.to_dict())
            self.assertEqual(result.validation["validation_scope"], "target-prefix")

    def test_editor_and_cli_from_an_unrelated_directory(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            request = mixed_project(root)
            configuration = ProjectConfiguration(library_file=request.library_file)
            payload = {
                "schema_version": EDITOR_REQUEST_SCHEMA,
                "request_id": "test:library",
                "operation": "prove-prefix",
                "source_file": str(request.source_file),
                "source_sha256": source_sha256(request.source_file),
                "goal_position": 1,
                "timeout_seconds": 20,
                "project_configuration": configuration.to_dict(),
            }
            parsed = EditorRequest.from_dict(payload)
            self.assertEqual(parsed.project_configuration, configuration)
            completed = subprocess.run(
                [sys.executable, "-m", "agdaprover", "editor-api"],
                input=json.dumps(payload),
                cwd=root,
                text=True,
                capture_output=True,
                timeout=30,
            )
            self.assertEqual(
                completed.returncode, 0, completed.stdout + completed.stderr
            )
            self.assertEqual(
                json.loads(completed.stdout)["result"]["status"], "verified"
            )
