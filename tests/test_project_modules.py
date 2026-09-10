"""Project/module-scope agreement for ordinary parameterized Agda sources."""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path

from agdaprover.application.service import ProverApplication
from agdaprover.bridge.contracts import BridgeError, ModuleId
from agdaprover.bridge.project import (
    _is_toolchain_module,
    _module_name,
    write_source_overlay,
)
from agdaprover.contracts import TaskSpec
from agdaprover.module_scope import ModuleScope, analyze_module_scope


class ProjectModuleHeaderTests(unittest.TestCase):
    def test_primitive_submodules_are_distinct_from_user_agda_modules(self) -> None:
        for name in ("Agda.Primitive", "Agda.Primitive.Cubical", "Agda.Builtin.Nat"):
            with self.subTest(name=name):
                self.assertTrue(_is_toolchain_module(name))
        for name in ("Agda.PrimitiveHelper", "Agda.User", "Project.Agda.Primitive"):
            with self.subTest(name=name):
                self.assertFalse(_is_toolchain_module(name))

    def test_provisional_overlay_keeps_primitive_import_for_the_kernel(self) -> None:
        text = (
            "{-# OPTIONS --cubical --safe #-}\n"
            "module Endpoints where\n"
            "open import Agda.Primitive.Cubical using (I; i0)\n"
            "endpoint : I\nendpoint = {!!}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "Endpoints.agda"
            source.write_text(text)
            candidate, copies = write_source_overlay(source, text, root / "overlay")
            self.assertEqual(candidate.read_text(), text)
            self.assertEqual(len(copies), 1)
            self.assertEqual(source.read_text(), text)

    def test_missing_root_is_an_input_result_not_a_bridge_traceback(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "Main.agda"
            source.write_text("identity : {A : Set} → A → A\nidentity = {!!}\n")
            result = ProverApplication().prove_prefix(TaskSpec(source))
            self.assertEqual(result.status, "invalid-task")
            self.assertIn("top-level module", result.diagnostics[0]["message"])
            self.assertIsNone(result.patch)

    def test_module_identity_accepts_shared_spellings_but_not_path_syntax(self) -> None:
        for name in ("Main", "Example.Ω-types", "_Private.Prime′"):
            with self.subTest(name=name):
                value = ModuleId(name, "Main.agda")
                self.assertEqual(ModuleId.from_dict(value.to_dict()), value)
        for name in ("../Main", "A/B", "A\\B", "A..B", ".Main", "Main.", "A B"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                ModuleId(name, "Main.agda")

    def test_parameters_do_not_hide_the_root_behind_a_nested_module(self) -> None:
        source = (
            "open import Agda.Primitive using (Level)\n"
            "module Main {a : Level} (A : Set a) where\n"
            "  module Child where\n"
            "    identity : A → A\n"
            "    identity = {!!}\n"
        )
        self.assertEqual(_module_name(Path("Main.agda"), source), "Main")
        scope = analyze_module_scope(source, source.index("{!!}"))
        self.assertEqual(scope.frames[0].name, "Main")
        self.assertEqual(
            [p.names for p in scope.frames[0].parameters], [("a",), ("A",)]
        )

    def test_multiline_unicode_header_and_nested_binders(self) -> None:
        source = (
            "module\n"
            "  Example.Ω-types\n"
            "  {A : Set} (B : A → Set)\n"
            "  (f : (x : A) → B x) {{point : A}} where\n"
            "value : A\nvalue = {!!}\n"
        )
        self.assertEqual(_module_name(Path("Ω-types.agda"), source), "Example.Ω-types")
        scope = analyze_module_scope(source, source.index("{!!}"))
        self.assertEqual(scope.frames[0].name, "Example.Ω-types")
        self.assertEqual(
            [p.names for p in scope.parameters], [("A",), ("B",), ("f",), ("point",)]
        )

    def test_inferred_parameter_annotations_stay_unknown_and_round_trip(self) -> None:
        source = (
            "module Main {a b} (A : Set a) {{choice}} ⦃witness⦄ where\n"
            "identity : A → A\nidentity = {!!}\n"
        )
        scope = analyze_module_scope(source, source.index("{!!}"))
        self.assertEqual(
            [(p.names, p.type_text, p.hiding, p.rendered) for p in scope.parameters],
            [
                (("a", "b"), "", "implicit", "{a b}"),
                (("A",), "Set a", "explicit", "(A : Set a)"),
                (("choice",), "", "instance", "{{choice}}"),
                (("witness",), "", "instance", "⦃witness⦄"),
            ],
        )
        self.assertEqual(ModuleScope.from_dict(scope.to_dict()), scope)
        for group in ("{}", "{{}}", "{a → b}", "{A.B}"):
            malformed = f"module Main {group} where\nidentity = {{!!}}\n"
            with self.subTest(group=group), self.assertRaises(ValueError):
                analyze_module_scope(malformed, malformed.index("{!!}"))

    def test_indented_root_and_commented_telescope_retain_source_metadata(self) -> None:
        source = (
            "  module Main {- context -} {a {- inferred -}} (A : Set a) where\n"
            "    module Child where\n"
            "      identity : A → A\n      identity = {!!}\n"
        )
        self.assertEqual(_module_name(Path("Main.agda"), source), "Main")
        scope = analyze_module_scope(source, source.index("{!!}"))
        self.assertEqual([f.kind for f in scope.frames], ["root", "named"])
        self.assertEqual(scope.frames[0].indentation, 2)
        self.assertEqual(scope.parameters[0].names, ("a",))
        self.assertEqual(scope.parameters[0].type_text, "")
        self.assertEqual(scope.parameters[0].rendered, "{a {- inferred -}}")

    def test_comments_prose_and_module_aliases_do_not_supply_a_root(self) -> None:
        source = (
            "module Prose where\n```text\nmodule Foreign where\n```\n"
            "```agda\n-- module Comment where\n"
            "module Alias = Imported\n"
            "module Real (A : Set) where\nvalue : A → A\nvalue = {!!}\n```\n"
        )
        path = Path("Real.lagda.md")
        self.assertEqual(_module_name(path, source), "Real")
        self.assertEqual(
            analyze_module_scope(source, source.index("{!!}"), path).frames[0].name,
            "Real",
        )
        for text in (
            "module Alias = Imported\n",
            "module _ where\n  module Nested where\n",
            "module Main (A : Set} where\n",
            "module Main (A : Set)\n",
        ):
            with self.subTest(source=text), self.assertRaises(BridgeError):
                _module_name(Path("Main.agda"), text)

    def test_overlay_preserves_parameterized_unicode_imports(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root, overlay = root / "source", root / "overlay"
            (source_root / "Support").mkdir(parents=True)
            dependency = source_root / "Support/Ω-types.agda"
            dependency.write_text("module Support.Ω-types (A : Set) where\n")
            source = source_root / "Main.agda"
            text = "module Main (A : Set) where\nopen import Support.Ω-types A\n"
            source.write_text(text)
            destination, copied = write_source_overlay(source, text, overlay)
            self.assertEqual(destination.read_text(), text)
            self.assertEqual(
                (overlay / "Support/Ω-types.agda").read_bytes(), dependency.read_bytes()
            )
            self.assertEqual(len(copied), 2)


@unittest.skipUnless(shutil.which("agda"), "requires Agda")
class ParameterizedRootProofTests(unittest.TestCase):
    def test_cubical_primitive_goal_has_a_freshly_validated_completion(self) -> None:
        text = (
            "{-# OPTIONS --cubical --safe #-}\n"
            "module Endpoints where\n"
            "open import Agda.Primitive.Cubical using (I; i0)\n"
            "endpoint : I\nendpoint = {!!}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "Endpoints.agda"
            source.write_text(text)
            result = ProverApplication().prove_prefix(
                TaskSpec(source, timeout_seconds=20)
            )
            self.assertEqual(result.status, "verified", result.diagnostics)
            self.assertTrue(result.validation and result.validation["fresh_process"])
            self.assertEqual(source.read_text(), text)

    def test_unknown_primitive_module_is_not_accepted_by_namespace_alone(self) -> None:
        text = (
            "module MissingPrimitive where\n"
            "open import Agda.Primitive.NotAnInstalledModule\n"
            "answer : {A : Set} → A → A\nanswer = {!!}\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "MissingPrimitive.agda"
            source.write_text(text)
            result = ProverApplication().prove_prefix(
                TaskSpec(source, timeout_seconds=20)
            )
            self.assertEqual(result.status, "invalid-task", result.diagnostics)
            self.assertIsNone(result.patch)
            self.assertEqual(source.read_text(), text)

    def test_native_proof_keeps_the_root_telescope_and_imports(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            support = root / "Support-Ω.agda"
            support.write_text("module Support-Ω where\n")
            for multiline, literate, inferred, indented, commented in (
                (False, False, False, False, False),
                (True, False, False, False, False),
                (False, False, True, False, False),
                (True, False, True, False, False),
                (False, False, True, True, False),
                (True, False, True, True, True),
                (True, True, True, False, True),
            ):
                with self.subTest(
                    multiline=multiline,
                    literate=literate,
                    inferred=inferred,
                    indented=indented,
                    commented=commented,
                ):
                    header = "module\n  Main" if multiline else "module Main"
                    level = "{a}" if inferred else "{a : Level}"
                    if commented:
                        level = "{- context -} {a {- inferred -}}"
                    body = "  " if indented else ""
                    source = (
                        "{-# OPTIONS --without-K #-}\n"
                        "open import Agda.Primitive using (Level)\n"
                        f"{header} {level} (A : Set a) where\n"
                        f"{body}open import Support-Ω\n"
                        f"{body}identity : A → A\n{body}identity = {{!!}}\n"
                    )
                    if indented:
                        source = "".join(
                            "  " + line for line in source.splitlines(True)
                        )
                    if literate:
                        source = "# Parameterized module\n```agda\n" + source + "```\n"
                    path = root / ("Main.lagda.md" if literate else "Main.agda")
                    # No competing same-module source remains in this fixture.
                    if literate:
                        (root / "Main.agda").unlink()
                    path.write_text(source)
                    result = ProverApplication().prove_prefix(
                        TaskSpec(
                            path,
                            max_candidates=50,
                            max_verifier_calls=200,
                            timeout_seconds=15,
                        )
                    )
                    self.assertEqual(result.status, "verified", result.diagnostics)
                    self.assertTrue(result.validation and result.validation["checked"])
                    self.assertTrue(result.validation["fresh_process"])
                    self.assertEqual(path.read_text(), source)
                    scope = result.goal["module_scope"]
                    self.assertEqual(scope["frames"][0]["name"], "Main")
                    self.assertEqual(len(scope["frames"][0]["parameters"]), 2)


if __name__ == "__main__":
    unittest.main()
