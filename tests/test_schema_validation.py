from __future__ import annotations

import unittest
from copy import deepcopy

from agdaprover.contracts import CostMetrics, ProverResult, StepResult
from agdaprover.schema_validation import validate_prover_result, validate_step_result


class P0SchemaValidationTests(unittest.TestCase):
    def test_library_evidence_preserves_reported_options_instead_of_default_flags(self):
        validation, trust = self.checked_evidence()
        options = [
            "--no-default-libraries",
            "--library-file=/overlay/libraries",
            "--ignore-interfaces",
            "-i",
            ".",
        ]
        environment = {
            "schema_version": "agdaprover.checking-environment.v1",
            "root_module": "Example",
            "command_options": [],
            "libraries": [
                {"name": "support", "includes": ["src"], "manifest_sha256": "a" * 64}
            ],
            "sources": {"Support": {"library": "support", "sha256": "b" * 64}},
        }
        result = ProverResult(
            task_id="task",
            status="verified",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
            proof_term="refl",
            patch={"replacement": "refl"},
            validation=validation,
            trust_report={
                **trust,
                "options": options,
                "checker_command": ["agda", *options, "Example.agda"],
                "checking_environment": environment,
                "sandbox_profile": "isolated-overlay-pinned-libraries-process-group-v1",
            },
        ).to_dict()
        validate_prover_result(result)
        for key, invalid in (
            ("schema_version", "future"),
            ("root_module", ""),
            ("libraries", []),
            ("command_options", ["--without-K"]),
            ("sources", {"Support": {"library": [], "sha256": "b" * 64}}),
        ):
            changed = deepcopy(result)
            changed["trust_report"]["checking_environment"][key] = invalid
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_prover_result(changed)
        for key, invalid in (
            ("checking_environment", None),
            ("sandbox_profile", "unknown"),
            ("checker_command", ["agda", "Example.agda"]),
            ("checker_exit_status", False),
        ):
            changed = deepcopy(result)
            changed["trust_report"][key] = invalid
            with self.subTest(key=key), self.assertRaises(ValueError):
                validate_prover_result(changed)
        changed = deepcopy(result)
        changed["trust_report"]["options"].append("--allow-unsolved-metas")
        changed["trust_report"]["checker_command"].insert(-1, "--allow-unsolved-metas")
        with self.assertRaisesRegex(ValueError, "unreported options"):
            validate_prover_result(changed)
        del changed["trust_report"]["checking_environment"]
        with self.assertRaisesRegex(ValueError, "strict offline trust report"):
            validate_prover_result(changed)

    def test_verifier_quota_reports_are_closed_versioned_and_consistent(self) -> None:
        for result_type, validator in (
            (ProverResult, validate_prover_result),
            (StepResult, validate_step_result),
        ):
            result = result_type(
                task_id="task",
                status="resource-exhausted",
                source_file="Example.agda",
                source_hash="0" * 64,
                ranker="symbolic",
            )
            self.assertNotIn("verifier_budget", result.to_dict())
            quota = {
                "schema_version": "agdaprover.verifier-budget.v1",
                "limit": 3,
                "used": 3,
                "interaction_commands": 2,
                "fresh_validations": 1,
                "denied_calls": 1,
            }
            value = {**result.to_dict(), "verifier_budget": quota}
            validator(value)
            for change in (
                {"schema_version": "future"},
                {"used": 4},
                {"used": 2},
                {"limit": 0},
                {"used": True},
                {"unknown": 0},
            ):
                with self.subTest(change=change), self.assertRaises(ValueError):
                    validator({**value, "verifier_budget": {**quota, **change}})
            with self.assertRaisesRegex(ValueError, "resource-exhausted"):
                validator({**value, "status": "unsolved"})
            # Consuming exactly the last credit is not itself a denial.
            validator(
                {
                    **value,
                    "status": "unsolved",
                    "verifier_budget": {**quota, "denied_calls": 0},
                }
            )

    @staticmethod
    def checked_evidence() -> tuple[dict[str, object], dict[str, object]]:
        return (
            {
                "checked": True,
                "fresh_process": True,
                "timed_out": False,
                "exit_status": 0,
            },
            {
                "fresh_process": True,
                "offline": True,
                "checker_exit_status": 0,
                "options": ["--without-K", "--exact-split"],
            },
        )

    def test_every_non_evidentiary_prover_status_round_trips(self) -> None:
        statuses = (
            "needs-clarification",
            "unsolved",
            "resource-exhausted",
            "invalid-task",
            "policy-rejected",
            "toolchain-error",
            "internal-error",
        )
        for status in statuses:
            with self.subTest(status=status):
                value = ProverResult(
                    task_id="task",
                    status=status,  # type: ignore[arg-type]
                    source_file="Example.agda",
                    source_hash="0" * 64,
                    ranker="symbolic",
                ).to_dict()
                self.assertEqual(validate_prover_result(value)["status"], status)

    def test_verified_requires_fresh_evidence(self) -> None:
        value = ProverResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
        ).to_dict()
        value["status"] = "verified"
        with self.assertRaisesRegex(ValueError, "proof term or patch"):
            validate_prover_result(value)

    def test_optional_traces_retain_their_array_contract(self) -> None:
        value = ProverResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
        ).to_dict()
        value["policy_trace"] = "malformed"
        with self.assertRaisesRegex(ValueError, "policy_trace must be a list"):
            validate_prover_result(value)

    def test_fresh_target_definition_validation_allows_preexisting_holes(self) -> None:
        value = ProverResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
        ).to_dict()
        validation, trust_report = self.checked_evidence()
        value.update(
            {
                "status": "verified",
                "proof_term": "refl",
                "patch": {"replacement": "refl"},
                "validation": {
                    **validation,
                    "exit_status": 42,
                    "validation_scope": "target-definition",
                    "acceptance_basis": "fresh interaction accepted target",
                    "remaining_open_goals": [{"goal_id": 1}],
                },
                "trust_report": {
                    **trust_report,
                    "checker_exit_status": 42,
                    "validation_scope": "target-definition",
                    "supplemental_checker_command": [
                        "agda",
                        "--interaction-json",
                    ],
                },
            }
        )
        self.assertEqual(validate_prover_result(value)["status"], "verified")

    def test_evidentiary_statuses_accept_complete_checked_evidence(self) -> None:
        base = ProverResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
        ).to_dict()
        validation, trust_report = self.checked_evidence()
        verified = {
            **base,
            "status": "verified",
            "proof_term": "refl",
            "patch": {"replacement": "refl"},
            "validation": validation,
            "trust_report": trust_report,
        }
        impossible = {
            **base,
            "status": "impossible",
            "impossibility_certificate": {"kind": "finite-refutation"},
            "validation": validation,
            "trust_report": trust_report,
        }
        self.assertEqual(validate_prover_result(verified)["status"], "verified")
        self.assertEqual(validate_prover_result(impossible)["status"], "impossible")

        untrusted = {
            **verified,
            "trust_report": {**trust_report, "offline": False},
        }
        with self.assertRaisesRegex(ValueError, "strict offline trust report"):
            validate_prover_result(untrusted)

    def test_step_is_closed_and_requires_action_on_acceptance(self) -> None:
        value = StepResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
            cost=CostMetrics(),
        ).to_dict()
        self.assertEqual(validate_step_result(value)["status"], "unsolved")
        value["future"] = True
        with self.assertRaisesRegex(ValueError, "unknown result fields"):
            validate_step_result(value)

    def test_accepted_step_requires_and_accepts_an_action(self) -> None:
        value = StepResult(
            task_id="task",
            status="unsolved",
            source_file="Example.agda",
            source_hash="0" * 64,
            ranker="symbolic",
            cost=CostMetrics(),
        ).to_dict()
        value["status"] = "accepted-step"
        with self.assertRaisesRegex(ValueError, "lacks an action"):
            validate_step_result(value)
        value["action"] = {"tag": "introduce-pi"}
        self.assertEqual(validate_step_result(value)["status"], "accepted-step")


if __name__ == "__main__":
    unittest.main()
