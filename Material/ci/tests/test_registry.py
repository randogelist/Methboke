"""Registry boundary tests. Docker, Lean and network calls are mocked."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("registry", Path(__file__).resolve().parents[1] / "registry.py")
registry = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(registry)


class RegistryContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in registry.COMPATIBILITY_FILES:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name + " locked input\n")
        self.env = {
            "GITHUB_REPOSITORY": "randogelist/Methboke",
            "GITHUB_SHA": "a" * 40,
            "GITHUB_RUN_ID": "12345",
            "GITHUB_RUN_ATTEMPT": "2",
            "GITHUB_REF_NAME": "Clay-Admission-Candidate-01",
        }
        self.state = registry.metadata(self.root, self.env)
        self.state.update(container_exit_code=0, parent_image_digest="repo@sha256:" + "b" * 64)
        self.expected_ids = {"QFB_ROOT"}
        registry.save(self.root / "Material/endpoints.json", {
            "endpoint_count": 1, "endpoints": [{"id": "QFB_ROOT"}],
        })
        self.report = {
            "status": "PASS", "commit": self.env["GITHUB_SHA"],
            "endpoints": [{"id": "QFB_ROOT", "status": "PASS", "input_hash": "c" * 64}],
        }

    def test_source_amendment_preserves_cache_compatibility(self):
        before = registry.compatibility(self.root)
        (self.root / "Material/NewEndpoint.lean").write_text("-- new source\n")
        self.assertEqual(before, registry.compatibility(self.root))
        (self.root / "Material/lake-manifest.json").write_text("new lock")
        self.assertNotEqual(before, registry.compatibility(self.root))

    def test_valid_pass(self):
        self.assertEqual(registry.validate_pass(self.report, self.state, self.expected_ids), self.report["endpoints"])

    def test_failed_container_cannot_reuse_old_pass_report(self):
        self.state["container_exit_code"] = 1
        with self.assertRaises(ValueError):
            registry.validate_pass(self.report, self.state, self.expected_ids)

    def test_previous_commit_report_cannot_publish(self):
        self.report["commit"] = "d" * 40
        with self.assertRaises(ValueError):
            registry.validate_pass(self.report, self.state, self.expected_ids)

    def test_missing_failed_duplicate_or_unhashed_endpoint_rejected(self):
        mutations = [
            [],
            [{"id": "QFB_ROOT", "status": "FAIL", "input_hash": "c" * 64}],
            self.report["endpoints"] * 2,
            [{"id": "QFB_ROOT", "status": "PASS", "input_hash": "unverified"}],
        ]
        for endpoints in mutations:
            with self.subTest(endpoints=endpoints), self.assertRaises(ValueError):
                registry.validate_pass(dict(self.report, endpoints=endpoints), self.state, self.expected_ids)

    def test_report_must_cover_exact_checked_in_endpoint_set(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            registry.validate_pass(self.report, self.state, {"QFB_ROOT", "QFB_TAIL"})
        with self.assertRaisesRegex(ValueError, "extra"):
            registry.validate_pass(self.report, self.state, {"QFB_TAIL"})

    def test_invalid_checked_in_endpoint_manifest_rejected(self):
        self.assertEqual(registry.expected_endpoint_ids(self.root), self.expected_ids)
        registry.save(self.root / "Material/endpoints.json", {
            "endpoint_count": 2, "endpoints": [{"id": "QFB_ROOT"}],
        })
        with self.assertRaises(ValueError):
            registry.expected_endpoint_ids(self.root)

    def test_image_reuse_requires_pass_compatible_source_and_platform(self):
        info = {"Os": "linux", "Architecture": "amd64", "Config": {"Labels": {
            registry.LABEL_PREFIX + "status": "PASS",
            registry.LABEL_PREFIX + "compatibility": self.state["compatibility_key"],
            "org.opencontainers.image.source": "https://github.com/randogelist/Methboke",
        }}}
        self.assertTrue(registry.compatible_image(info, self.state))
        info["Config"]["Labels"][registry.LABEL_PREFIX + "status"] = "FAIL"
        self.assertFalse(registry.compatible_image(info, self.state))

    def test_branch_slug_collision_has_distinct_pointer(self):
        first = registry.metadata(self.root, dict(self.env, GITHUB_REF_NAME="x/y"))
        second = registry.metadata(self.root, dict(self.env, GITHUB_REF_NAME="x-y"))
        self.assertNotEqual(first["pointer"], second["pointer"])

    def test_old_successful_rerun_keeps_immutable_images_without_pointer_regression(self):
        state_path = self.root / "state.json"
        registry.save(state_path, self.state)
        registry.save(self.root / "Material/registry/current.json", self.report)
        commands = []

        def fake_execute(args, **kwargs):
            commands.append(args)
            result = [{"RepoDigests": [self.state["image_repository"] + "@sha256:" + "e" * 64]}]
            return subprocess.CompletedProcess(args, 0, json.dumps(result), "")

        with patch.object(registry, "execute", side_effect=fake_execute), \
                patch.object(registry, "current_branch_head", return_value="f" * 40):
            registry.publish(self.root, state_path)
        pushed = [args[2] for args in commands if args[:2] == ["docker", "push"]]
        self.assertIn(self.state["immutable_tag"], pushed)
        self.assertNotIn(self.state["pointer"], pushed)
        self.assertEqual(len(pushed), 2)  # Aggregate plus one exact endpoint tag.
        self.assertFalse(registry.load(state_path)["pointer_updated"])

    def test_current_successful_head_advances_pointer_last(self):
        state_path = self.root / "state.json"
        registry.save(state_path, self.state)
        registry.save(self.root / "Material/registry/current.json", self.report)
        commands = []

        def fake_execute(args, **kwargs):
            commands.append(args)
            data = [{"RepoDigests": [self.state["image_repository"] + "@sha256:" + "e" * 64]}]
            return subprocess.CompletedProcess(args, 0, json.dumps(data), "")

        with patch.object(registry, "execute", side_effect=fake_execute), \
                patch.object(registry, "current_branch_head", return_value=self.state["commit"]):
            registry.publish(self.root, state_path)
        pushed = [args[2] for args in commands if args[:2] == ["docker", "push"]]
        self.assertEqual(pushed[-1], self.state["pointer"])
        self.assertTrue(registry.load(state_path)["pointer_updated"])


if __name__ == "__main__":
    unittest.main()
