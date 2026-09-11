"""Missing samples must distinguish completed children from live meter failures."""

import subprocess
import unittest
from unittest.mock import Mock, patch

from agdaprover.bridge.contracts import BridgeBudget, BridgeError, BridgeFailure
from agdaprover.bridge.resources import (
    CancellationToken,
    ProcessUsage,
    ResourceSupervisor,
)
from agdaprover.resource_budget import ResourceExhausted


class ResourceSamplingTests(unittest.TestCase):
    def supervisor(self, **limits):
        return ResourceSupervisor(BridgeBudget(**limits), CancellationToken())

    def exercise(self, supervisor, process, explicit):
        if explicit:
            return supervisor.sample(process)
        return supervisor.check(process, command_id=None, force_sample=True)

    def test_exit_transition_is_reaped_and_final_cpu_charged_once(self):
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                process = Mock(pid=1234, final_cpu_seconds=0.75)
                process.poll.return_value = None
                process.wait.return_value = 7
                supervisor = self.supervisor()
                with patch(
                    "agdaprover.bridge.resources.process_tree_usage", return_value=None
                ):
                    usage = self.exercise(supervisor, process, explicit)
                self.assertEqual(usage, ProcessUsage(0, 0.0, 0))
                self.assertEqual(supervisor.cpu_seconds, 0.75)
                process.wait.assert_called_once()
                self.assertGreater(process.wait.call_args.kwargs["timeout"], 0)
                self.assertLessEqual(process.wait.call_args.kwargs["timeout"], 0.01)
                supervisor.release(process)
                supervisor.release(process)
                self.assertEqual(supervisor.cpu_seconds, 0.75)

    def test_still_live_unmeterable_child_fails_closed(self):
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                process = Mock(pid=1234)
                process.poll.return_value = None
                process.wait.side_effect = subprocess.TimeoutExpired("checker", 0.01)
                supervisor = self.supervisor()
                with (
                    patch(
                        "agdaprover.bridge.resources.process_tree_usage",
                        return_value=None,
                    ),
                    self.assertRaises(BridgeError) as raised,
                ):
                    self.exercise(supervisor, process, explicit)
                self.assertEqual(
                    raised.exception.diagnostic.code, "resource-sampling-unavailable"
                )
                process.wait.assert_called_once()

    def test_wait_never_extends_deadline(self):
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                now = [10.999]
                supervisor = self.supervisor(started=10, wall_seconds=1)
                process = Mock(pid=1234, final_cpu_seconds=0.0)
                process.poll.return_value = None

                def finish(*, timeout, now=now):
                    self.assertAlmostEqual(timeout, 0.001)
                    now[0] = 11.001
                    return 0

                process.wait.side_effect = finish
                with (
                    patch(
                        "agdaprover.bridge.resources.process_tree_usage",
                        return_value=None,
                    ),
                    patch(
                        "agdaprover.bridge.resources.time.monotonic",
                        side_effect=lambda now=now: now[0],
                    ),
                    self.assertRaises(BridgeError) as raised,
                ):
                    self.exercise(supervisor, process, explicit)
                self.assertEqual(raised.exception.failure, BridgeFailure.TIMEOUT)

    def test_cancellation_during_exit_wait_is_not_success(self):
        for explicit in (False, True):
            with self.subTest(explicit=explicit):
                supervisor = self.supervisor()
                process = Mock(pid=1234, final_cpu_seconds=0.0)
                process.poll.return_value = None

                def finish(supervisor=supervisor, **_):
                    supervisor.cancellation.cancel()
                    return 0

                process.wait.side_effect = finish
                with (
                    patch(
                        "agdaprover.bridge.resources.process_tree_usage",
                        return_value=None,
                    ),
                    self.assertRaises(BridgeError) as raised,
                ):
                    self.exercise(supervisor, process, explicit)
                self.assertEqual(raised.exception.failure, BridgeFailure.CANCELLED)

    def test_parent_resource_refusal_after_wait_propagates(self):
        supervisor = self.supervisor()
        process = Mock(pid=1234, final_cpu_seconds=0.0)
        process.poll.return_value = None
        process.wait.return_value = 0

        def checkpoint():
            if process.wait.called:
                raise ResourceExhausted("cpu-seconds", 2, 1)

        with (
            patch("agdaprover.bridge.resources.process_tree_usage", return_value=None),
            patch("agdaprover.bridge.resources.checkpoint", side_effect=checkpoint),
            self.assertRaises(ResourceExhausted),
        ):
            supervisor.check(process, command_id=None, force_sample=True)

    def test_final_cpu_cannot_bypass_bridge_limit(self):
        supervisor = self.supervisor(cpu_seconds=1)
        process = Mock(pid=1234, final_cpu_seconds=1.1)
        process.poll.return_value = None
        process.wait.return_value = 0
        with (
            patch("agdaprover.bridge.resources.process_tree_usage", return_value=None),
            self.assertRaises(BridgeError) as raised,
        ):
            supervisor.check(process, command_id=None, force_sample=True)
        self.assertEqual(raised.exception.diagnostic.code, "bridge-cpu-exhausted")

    def test_available_sample_does_not_wait(self):
        supervisor = self.supervisor()
        process = Mock(pid=1234, final_cpu_seconds=0.0)
        usage = ProcessUsage(100, 0.5, 1)
        with patch(
            "agdaprover.bridge.resources.process_tree_usage", return_value=usage
        ):
            self.assertEqual(
                supervisor.check(process, command_id=None, force_sample=True), usage
            )
        process.wait.assert_not_called()
        self.assertEqual(supervisor.cpu_seconds, 0.5)

    def test_already_reaped_child_does_not_wait(self):
        supervisor = self.supervisor()
        process = Mock(pid=1234, final_cpu_seconds=0.5)
        process.poll.return_value = 0
        with patch("agdaprover.bridge.resources.process_tree_usage", return_value=None):
            self.assertEqual(
                supervisor.check(process, command_id=None, force_sample=True),
                ProcessUsage(0, 0.0, 0),
            )
        process.wait.assert_not_called()
        self.assertEqual(supervisor.cpu_seconds, 0.5)


if __name__ == "__main__":
    unittest.main()
