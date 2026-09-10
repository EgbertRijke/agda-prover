"""A partially trained OR policy cannot reorder unrelated decision families."""

import json
import struct
import tempfile
import unittest
from pathlib import Path

from agdaprover.contracts import GoalInfo
from agdaprover.nnue import (
    FEATURE_SCHEMA_VERSION,
    MAGIC,
    MODEL_FEATURE_FAMILIES,
    MODEL_SCHEMA_VERSION,
    SCOPED_MAGIC,
    SCOPED_MODEL_SCHEMA_VERSION,
    NNUEModel,
)
from agdaprover.or_policy import ORPolicyRouter, policy_candidate


class PolicyDomainTests(unittest.TestCase):
    def model_file(self, path, **overrides):
        header = {
            "schema_version": SCOPED_MODEL_SCHEMA_VERSION,
            "feature_schema_version": FEATURE_SCHEMA_VERSION,
            "feature_family": MODEL_FEATURE_FAMILIES["or-decision-ranking"],
            "role": "or-decision-ranking",
            "input_size": 8,
            "hidden_size": 1,
            "seed": 1,
            "policy_families": ["case-variable"],
            **overrides,
        }
        encoded = json.dumps(header).encode()
        path.write_bytes(
            SCOPED_MAGIC + struct.pack("<I", len(encoded)) + encoded + bytes(44)
        )

    def test_scoped_model_loads_without_a_training_sidecar(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "policy.apnnue"
            self.model_file(path)
            model = NNUEModel.load(path, expected_role="or-decision-ranking")
        self.assertEqual(model.policy_families, ("case-variable",))
        self.assertTrue(model.supports_policy_family("case-variable"))
        self.assertFalse(model.supports_policy_family("visible-premise"))

    def test_unsupported_family_preserves_candidates_and_does_no_scoring(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "policy.apnnue"
            self.model_file(path)
            router = ORPolicyRouter(refinement_model=NNUEModel.load(path))
        goal = GoalInfo(0, "A", (), (1, 5))
        candidates = tuple(
            policy_candidate(
                family="visible-premise",
                tag="premise",
                expression=x,
                type_text="A",
                symbolic_key=(i,),
            )
            for i, x in enumerate(("z", "a"))
        )
        self.assertEqual(router.rank(goal, candidates).candidates, candidates)
        self.assertEqual(router.metrics()["model_items_scored"], 0)
        self.assertEqual(router.metrics()["unsupported_family_fallbacks"], 1)
        record = router.recorder.to_list()[0]
        self.assertEqual(record["symbolic_order"], record["model_order"])
        self.assertIsNone(record["model_id"])
        self.assertEqual(
            record["provenance"]["policy_fallback_reason"],
            "unsupported-decision-family",
        )
        cases = tuple(
            policy_candidate(
                family="case-variable",
                tag="split",
                expression=x,
                type_text="A",
                symbolic_key=(i,),
            )
            for i, x in enumerate(("p", "q"))
        )
        self.assertEqual(router.rank(goal, cases).candidates, cases)
        self.assertEqual(router.metrics()["model_items_scored"], 2)
        self.assertNotIn(
            "policy_fallback_reason", router.recorder.to_list()[1]["provenance"]
        )

    def test_scope_is_nonempty_canonical_and_role_specific(self):
        for families in (
            None,
            [],
            "case-variable",
            ["case-variable", "case-variable"],
            ["unknown"],
            ["focused-hypothesis"],
            [True],
            ["visible-premise", "case-variable"],
        ):
            with self.subTest(families=families), tempfile.TemporaryDirectory() as d:
                path = Path(d) / "bad.apnnue"
                self.model_file(path, policy_families=families)
                with self.assertRaises(ValueError):
                    NNUEModel.load(path)
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "wrong-role.apnnue"
            self.model_file(
                path,
                role="proof-term-ranking",
                feature_family=MODEL_FEATURE_FAMILIES["proof-term-ranking"],
            )
            with self.assertRaises(ValueError):
                NNUEModel.load(path)

    def test_legacy_unscoped_artifacts_keep_their_existing_behavior(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "legacy.apnnue"
            header = {
                "schema_version": MODEL_SCHEMA_VERSION,
                "feature_schema_version": FEATURE_SCHEMA_VERSION,
                "feature_family": MODEL_FEATURE_FAMILIES["or-decision-ranking"],
                "role": "or-decision-ranking",
                "input_size": 8,
                "hidden_size": 1,
                "seed": 1,
            }
            encoded = json.dumps(header).encode()
            path.write_bytes(
                MAGIC + struct.pack("<I", len(encoded)) + encoded + bytes(44)
            )
            model = NNUEModel.load(path)
            self.assertIsNone(model.policy_families)
            self.assertTrue(model.supports_policy_family("visible-premise"))
            self.assertFalse(model.supports_policy_family("evidence-application-v1"))
            # Scope cannot be smuggled into an old format that old runtimes ignore.
            header["policy_families"] = ["case-variable"]
            encoded = json.dumps(header).encode()
            path.write_bytes(
                MAGIC + struct.pack("<I", len(encoded)) + encoded + bytes(44)
            )
            with self.assertRaises(ValueError):
                NNUEModel.load(path)

    def test_format_magic_and_header_must_agree(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "wrong-magic.apnnue"
            self.model_file(path)
            path.write_bytes(MAGIC + path.read_bytes()[len(SCOPED_MAGIC) :])
            with self.assertRaises(ValueError):
                NNUEModel.load(path)

    def test_new_evidence_domain_requires_explicit_scoped_weights(self):
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "evidence.apnnue"
            self.model_file(path, policy_families=["evidence-application-v1"])
            model = NNUEModel.load(path)
            self.assertTrue(model.supports_policy_family("evidence-application-v1"))
            self.assertFalse(model.supports_policy_family("constructor-choice"))
