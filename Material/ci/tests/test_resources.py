"""Pure/mocked resource guards: no Docker, Lean, Lake or network execution."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("resource_registry", Path(__file__).resolve().parents[1] / "registry.py")
registry = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(registry)


class ResourceTests(unittest.TestCase):
    def test_meminfo_bytes_and_private_runner_budget(self):
        parsed = registry.parse_meminfo("MemTotal: 7340032 kB\nMemAvailable: 6291456 kB\n")
        self.assertEqual(parsed["MemTotal"], 7 * registry.GIB)
        limits = registry.resource_limits({"memory_total_bytes": parsed["MemTotal"],
                                          "memory_available_bytes": parsed["MemAvailable"], "cpu_count": 2})
        self.assertEqual(limits["memory_bytes"], 5 * registry.GIB)
        self.assertEqual(limits["memory_swap_bytes"], limits["memory_bytes"])
        self.assertGreaterEqual(limits["host_memory_reserve_bytes"], 2 * registry.GIB)
        self.assertEqual(limits["cpus"], 2)

    def test_larger_runner_stays_bounded(self):
        limits = registry.resource_limits({"memory_total_bytes": 64 * registry.GIB,
                                          "memory_available_bytes": 60 * registry.GIB, "cpu_count": 16})
        self.assertEqual(limits["memory_bytes"], 5 * registry.GIB)
        self.assertEqual(limits["cpus"], 2)

    def test_low_memory_is_rejected(self):
        with self.assertRaises(ValueError):
            registry.resource_limits({"memory_total_bytes": 3 * registry.GIB,
                                      "memory_available_bytes": 2 * registry.GIB, "cpu_count": 2})

    def test_oom_metadata_is_preserved(self):
        state = registry.container_exit_metadata({
            "State": {"ExitCode": 137, "OOMKilled": True, "Status": "exited", "Error": ""},
            "HostConfig": {"Memory": 5 * registry.GIB, "MemorySwap": 5 * registry.GIB,
                           "NanoCpus": 2 * 10**9, "PidsLimit": 512}})
        self.assertEqual(state["container_exit_code"], 137)
        self.assertTrue(state["container_oom_killed"])
        self.assertEqual(state["enforced_resources"]["Memory"], 5 * registry.GIB)

    def test_disk_preflight_fails_without_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            snapshot = {"disk": {"workspace": {"free_bytes": 10 * registry.GIB},
                                 "docker": {"free_bytes": 10 * registry.GIB}}}
            info = {"DockerRootDir": "/var/lib/docker", "MemoryLimit": True,
                    "SwapLimit": True, "CpuCfsQuota": True}
            with patch.object(registry, "host_resources", return_value=snapshot), \
                 patch.object(registry, "execute", return_value=SimpleNamespace(stdout=json.dumps(info), returncode=0)) as calls:
                with self.assertRaises(ValueError):
                    registry.preflight(root, "test", 20)
                self.assertEqual(calls.call_count, 1)
                self.assertTrue((root / "Material/registry/resources-test.json").is_file())

    def run_fixture(self, root, oom):
        state_path = root / "state.json"
        state = {"commit": "1" * 40, "run_id": "1", "attempt": "1", "repository": "test/repo",
                 "branch": "main", "compatibility_key": "2" * 64, "parent_image_digest": None,
                 "restore_mode": "cold_bootstrap", "base_image": "test:base", "container": "material-1-1",
                 "docker_root": "/var/lib/docker"}
        registry.save(state_path, state)
        limits = {"memory_bytes": 5 * registry.GIB, "memory_swap_bytes": 5 * registry.GIB,
                  "cpus": 2, "pids_limit": 512}
        commands = []

        def fake_execute(argv, **kwargs):
            commands.append(argv)
            if argv[:2] == ["docker", "inspect"]:
                content = [{"State": {"ExitCode": 137 if oom else 0, "Status": "exited",
                                       "Running": False, "OOMKilled": oom}, "HostConfig": {}}]
                return SimpleNamespace(returncode=0, stdout=json.dumps(content))
            return SimpleNamespace(returncode=137 if oom and argv[:2] == ["docker", "start"] else 0, stdout="")

        with patch.object(registry, "preflight", return_value=({}, limits)), \
             patch.object(registry, "execute", side_effect=fake_execute), \
             patch.object(registry.threading, "Thread"), \
             patch.object(registry, "host_resources", return_value={}), \
             patch.object(registry.subprocess, "run", side_effect=AssertionError("no external process")):
            if oom:
                with self.assertRaises(RuntimeError):
                    registry.run(root, state_path)
            else:
                registry.run(root, state_path)
        return commands, registry.load(state_path)

    def test_run_enforces_caps_and_retains_success_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            commands, state = self.run_fixture(Path(directory), False)
            creation = next(x for x in commands if x[:2] == ["docker", "create"])
            self.assertEqual(creation[creation.index("--memory") + 1], str(5 * registry.GIB))
            self.assertEqual(creation[creation.index("--memory-swap") + 1], str(5 * registry.GIB))
            self.assertEqual(creation[creation.index("--cpus") + 1], "2")
            self.assertEqual(state["status"], "BUILT")
            self.assertFalse(state["container_oom_killed"])

    def test_run_oom_cannot_be_classified_as_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            _, state = self.run_fixture(Path(directory), True)
            self.assertEqual(state["status"], "BUILD_FAILED")
            self.assertTrue(state["container_oom_killed"])
            self.assertEqual(state["container_exit_code"], 137)

    def test_collect_preserves_complete_host_monitor(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state_path = root / "state.json"
            registry.save(state_path, {"container": "material-1-1", "status": "BUILT"})
            monitor = root / "Material/registry/host-monitor.jsonl"
            monitor.parent.mkdir(parents=True)
            monitor.write_text('first\nlast\n')

            def fake_execute(argv, **kwargs):
                if argv[:2] == ["docker", "inspect"]:
                    return SimpleNamespace(returncode=0, stdout='[{"State":{"Status":"exited","ExitCode":0}}]')
                if argv[:2] == ["docker", "cp"]:
                    monitor.write_text('first\n')
                return SimpleNamespace(returncode=0, stdout='')

            with patch.object(registry, "execute", side_effect=fake_execute), \
                 patch.dict(registry.os.environ, {}, clear=True):
                registry.collect(root, state_path)
            self.assertEqual(monitor.read_text(), 'first\nlast\n')


if __name__ == "__main__":
    unittest.main()
