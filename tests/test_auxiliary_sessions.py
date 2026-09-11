"""Auxiliary workers reuse imports, never a previous probe's proof state."""

import math
import shutil
import tempfile
import time
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import Mock, patch

from agdaprover.bridge.contracts import (
    BridgeDiagnostic,
    BridgeError,
    BridgeFailure,
    DiagnosticPhase,
)
from agdaprover.kernel.auxiliary import AuxiliarySessions, load_kernel_project
from agdaprover.kernel.p0 import AgdaBridgeError, AgdaLoadError, AgdaSession
from agdaprover.project_configuration import ProjectConfiguration
from agdaprover.resource_budget import ResourceLimitError
from agdaprover.verifier_budget import VerifierCallLimitExceeded


class LegacySession:
    def __init__(self):
        self.loads = []

    def load_module(self, source):
        self.loads.append((source, None))
        return ()


class RevisionSession(LegacySession):
    def load_project(self, source, configuration):
        self.loads.append((source, configuration))
        return ()


class AuxiliarySessionTests(unittest.TestCase):
    def setUp(self):
        self.created = []
        self.closed = []
        self.arguments = []

    def factory(self, cls=RevisionSession, cleanup_error=None):
        @contextmanager
        def create(**kwargs):
            self.arguments.append(kwargs)
            session = cls()
            self.created.append(session)
            try:
                yield session
            finally:
                self.closed.append(session)
                if cleanup_error is not None:
                    raise cleanup_error

        return create

    def test_reuse_requires_both_opt_in_and_capability(self):
        for enabled, cls in (
            (False, RevisionSession),
            (True, LegacySession),
            (True, RevisionSession),
        ):
            with self.subTest(enabled=enabled, cls=cls):
                self.setUp()
                with AuxiliarySessions(
                    self.factory(cls), deadline=math.inf, reuse=enabled
                ) as pool:
                    for index in range(3):
                        configuration = ProjectConfiguration(options=("--safe",))
                        with pool.open(project_configuration=configuration) as worker:
                            self.assertEqual(
                                load_kernel_project(
                                    worker, Path(f"Probe{index}.agda"), configuration
                                ),
                                (),
                            )
                expected = 1 if enabled and cls is RevisionSession else 3
                self.assertEqual(len(self.created), expected)
                self.assertEqual(self.closed, self.created)
                self.assertEqual(sum(len(w.loads) for w in self.created), 3)
                if expected == 1:
                    self.assertEqual(self.created[0].loads[-1][1], configuration)

    def test_environment_default_remains_opt_in(self):
        for flag, count in (("0", 2), ("1", 1)):
            self.setUp()
            with (
                patch.dict("os.environ", {"AGDAPROVER_REUSE_AUXILIARY_SESSION": flag}),
                AuxiliarySessions(self.factory(), deadline=math.inf) as pool,
            ):
                for _ in range(2):
                    with pool.open(project_configuration=None):
                        pass
            self.assertEqual(len(self.created), count)

    def test_legacy_unconfigured_factory_receives_no_configuration_keyword(self):
        @contextmanager
        def legacy(*, timeout_seconds, deadline):
            self.assertEqual(timeout_seconds, math.inf)
            self.assertEqual(deadline, math.inf)
            yield LegacySession()

        with AuxiliarySessions(legacy, deadline=math.inf, reuse=True) as pool:
            with pool.open(project_configuration=None):
                pass

    def test_failure_discards_worker_and_preserves_original_exception(self):
        for error in (
            AgdaLoadError("load"),
            ResourceLimitError("cpu"),
            TimeoutError("time"),
            KeyboardInterrupt(),
        ):
            self.setUp()
            with (
                self.subTest(error=type(error).__name__),
                AuxiliarySessions(
                    self.factory(), deadline=math.inf, reuse=True
                ) as pool,
            ):
                with self.assertRaises(type(error)) as raised:
                    with pool.open(project_configuration=None):
                        raise error
                self.assertIs(raised.exception, error)
                self.assertEqual(self.closed, self.created)
                with pool.open(project_configuration=None) as recovered:
                    self.assertIsNot(recovered, self.created[0])
            self.assertEqual(self.closed, self.created)

    def test_cleanup_error_does_not_mask_resource_or_cancellation(self):
        original = ResourceLimitError("cpu")
        pool = AuxiliarySessions(
            self.factory(cleanup_error=OSError("cleanup")),
            deadline=math.inf,
            reuse=True,
        )
        with pool:
            with self.assertRaises(ResourceLimitError) as raised:
                with pool.open(project_configuration=None):
                    raise original
            self.assertIs(raised.exception, original)
            self.assertIn("OSError", original.__notes__[0])
        self.assertEqual(self.closed, self.created)

    def test_deadline_never_renews_and_expiration_closes_idle_worker(self):
        with (
            patch("agdaprover.kernel.auxiliary.time.monotonic", return_value=10),
            AuxiliarySessions(self.factory(), deadline=30, reuse=True) as pool,
        ):
            with pool.open(project_configuration=None):
                pass
            self.assertEqual(self.arguments[0]["timeout_seconds"], 20)
            self.assertEqual(self.arguments[0]["deadline"], 30)
            with patch("agdaprover.kernel.auxiliary.time.monotonic", return_value=31):
                with self.assertRaises(TimeoutError):
                    with pool.open(project_configuration=None):
                        self.fail("expired worker was yielded")
            self.assertEqual(len(self.created), 1)
            self.assertEqual(self.closed, self.created)

    def test_cleanup_cancellation_or_resource_refusal_overrides_recoverable_error(self):
        for error in (
            KeyboardInterrupt(),
            ResourceLimitError("cpu"),
            VerifierCallLimitExceeded("quota"),
            TimeoutError("deadline"),
        ):
            self.setUp()
            pool = AuxiliarySessions(
                self.factory(cleanup_error=error), deadline=math.inf, reuse=True
            )
            with self.subTest(error=type(error).__name__), pool:
                with self.assertRaises(type(error)) as raised:
                    with pool.open(project_configuration=None):
                        raise AgdaLoadError("recoverable probe failure")
                self.assertIs(raised.exception, error)
            self.assertEqual(self.closed, self.created)

    def test_failed_factory_does_not_publish_a_worker_or_poison_next_lease(self):
        original = ResourceLimitError("startup")
        create = self.factory()
        attempts = 0

        @contextmanager
        def factory(**kwargs):
            nonlocal attempts
            attempts += 1
            if attempts == 1:
                raise original
            with create(**kwargs) as worker:
                yield worker

        with AuxiliarySessions(factory, deadline=math.inf, reuse=True) as pool:
            with self.assertRaises(ResourceLimitError) as raised:
                with pool.open(project_configuration=None):
                    self.fail("failed startup yielded a worker")
            self.assertIs(raised.exception, original)
            with pool.open(project_configuration=None):
                pass
        self.assertEqual(attempts, 2)
        self.assertEqual(self.closed, self.created)

    def test_compatibility_close_preserves_kernel_resource_error_category(self):
        for failure, expected in (
            (BridgeFailure.RESOURCE_EXHAUSTED, ResourceLimitError),
            (BridgeFailure.TIMEOUT, TimeoutError),
        ):
            error = BridgeError(
                failure,
                BridgeDiagnostic(
                    code="cleanup-budget",
                    phase=DiagnosticPhase.RESOURCE,
                    severity="error",
                    message="cleanup budget exhausted",
                ),
            )
            session = object.__new__(AgdaSession)
            session._session = Mock(close=Mock(side_effect=error))
            with self.subTest(failure=failure), self.assertRaises(expected) as raised:
                session.close()
            self.assertIs(raised.exception.__cause__, error)

    def test_serial_leases_and_closed_owners_are_enforced(self):
        with AuxiliarySessions(self.factory(), deadline=math.inf, reuse=True) as pool:
            with pool.open(project_configuration=None) as worker:
                with self.assertRaisesRegex(RuntimeError, "serial"):
                    with pool.open(project_configuration=None):
                        self.fail("nested lease was yielded")
                with self.assertRaisesRegex(RuntimeError, "leased"):
                    pool.__exit__(None, None, None)
                self.assertEqual(self.closed, [])
                self.assertIs(worker, self.created[0])
        with self.assertRaisesRegex(RuntimeError, "closed"):
            with pool.open(project_configuration=None):
                self.fail("closed owner was yielded")
        with self.assertRaises(ValueError):
            AuxiliarySessions(self.factory(), deadline=math.nan)
        self.assertEqual(self.closed, self.created)


@unittest.skipUnless(shutil.which("agda"), "Agda is required")
class AuxiliaryAgdaTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        env = patch.dict("os.environ", {"AGDAPROVER_REUSE_ROOT_OVERLAY": "1"})
        env.start()
        self.addCleanup(env.stop)
        self.first = self.project("first")
        self.second = self.project("second")

    def project(self, name, support="data U : Set where u : U\n", body=None):
        root = self.root / name
        root.mkdir()
        (root / "local.agda-lib").write_text("name: local\ninclude: .\n")
        registry = root / "libraries"
        registry.write_text(str(root / "local.agda-lib") + "\n")
        (root / "Support.agda").write_text("module Support where\n" + support)
        source = root / "Main.agda"
        source.write_text(
            "module Main where\nopen import Support\n"
            + ("value : U\nvalue = {!!}\n" if body is None else body)
        )
        return source, ProjectConfiguration(library_file=registry)

    def pool(self):
        return AuxiliarySessions(
            AgdaSession, deadline=time.monotonic() + 30, reuse=True
        )

    def test_rebinding_survives_deleted_probe_workspace_and_invalidates_tokens(self):
        with self.pool() as pool:
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
                parent = worker.current_state()
            # The caller owns its temporary input copy, not the kernel overlay.
            shutil.rmtree(self.first[0].parent)
            with pool.open(project_configuration=self.second[1]) as reused:
                self.assertIs(reused, worker)
                goals = load_kernel_project(reused, *self.second)
                self.assertEqual(goals[0].target, "U")
                self.assertEqual(reused._session.root_overlay_reuses, 1)
                self.assertEqual(reused._session.transport.process_generation, 1)
                with self.assertRaises(AgdaBridgeError):
                    reused.inspect_state(parent)
                self.assertTrue(reused.check_refinement(0, "u").accepted)
        self.assertTrue(worker._session._closed)

    def test_same_path_is_new_epoch_and_dependency_changes_rebuild(self):
        with self.pool() as pool:
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
                parent = worker.current_state()
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
                with self.assertRaises(AgdaBridgeError):
                    worker.inspect_state(parent)
                self.assertEqual(worker._session.root_overlay_reuses, 1)
            support = self.first[0].parent / "Support.agda"
            support.write_text("module Support where\ndata U : Set where other : U\n")
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
                self.assertFalse(worker.check_refinement(0, "u").accepted)
                self.assertTrue(worker.check_refinement(0, "other").accepted)
                self.assertEqual(worker._session.transport.process_generation, 2)

    def test_configuration_change_rebuilds_with_fresh_parity(self):
        changed = ProjectConfiguration(
            library_file=self.second[1].library_file, options=("--safe", "--without-K")
        )
        with self.pool() as pool:
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
            with pool.open(project_configuration=changed) as worker:
                goals = load_kernel_project(worker, self.second[0], changed)
                with AgdaSession(project_configuration=changed) as fresh:
                    clean = fresh.load_module(self.second[0])
                    self.assertEqual(goals, clean)
                self.assertEqual(worker._session.transport.process_generation, 2)
                self.assertEqual(worker._session.root_overlay_reuses, 0)

    def test_load_failure_discards_worker_and_leaves_primary_unchanged(self):
        bad = self.project("bad", body="value : U\nvalue = λ x → x\n")
        with (
            AgdaSession(project_configuration=self.first[1]) as primary,
            self.pool() as pool,
        ):
            goals = primary.load_module(self.first[0])
            parent = primary.current_state()
            with pool.open(project_configuration=self.second[1]) as worker:
                load_kernel_project(worker, *self.second)
            with self.assertRaises(AgdaLoadError):
                with pool.open(project_configuration=bad[1]) as worker:
                    load_kernel_project(worker, *bad)
            self.assertTrue(worker._session._closed)
            self.assertEqual(primary.inspect_state(parent), goals)
            with pool.open(project_configuration=self.second[1]) as recovered:
                self.assertIsNot(recovered, worker)
                self.assertEqual(load_kernel_project(recovered, *self.second), goals)

    def test_parameter_private_and_shared_meta_context_matches_fresh(self):
        body = """private
  hidden : U
  hidden = u
module Local (A : Set) (a : A) where
  chosen : A
  chosen = {!!}
T : Set
T = {!!}
point : T
point = {!!}
"""
        revised = self.project("scope", body=body)
        with self.pool() as pool:
            with pool.open(project_configuration=self.first[1]) as worker:
                load_kernel_project(worker, *self.first)
            with pool.open(project_configuration=revised[1]) as worker:
                goals = load_kernel_project(worker, *revised)
                with AgdaSession(project_configuration=revised[1]) as fresh:
                    clean = fresh.load_module(revised[0])
                    self.assertEqual(
                        tuple(worker.inspect_goal(g) for g in goals),
                        tuple(fresh.inspect_goal(g) for g in clean),
                    )
                self.assertEqual(worker._session.root_overlay_reuses, 1)


if __name__ == "__main__":
    unittest.main()
