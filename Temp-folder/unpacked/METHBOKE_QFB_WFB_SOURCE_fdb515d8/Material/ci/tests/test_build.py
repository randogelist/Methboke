"""Pure parser/filesystem and mocked-run tests; no Lean or Lake execution."""
from __future__ import annotations

import importlib.util
import json
import io
import threading
import time
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


MODULE = Path(__file__).resolve().parents[1] / "build.py"
spec = importlib.util.spec_from_file_location("material_build", MODULE)
build = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(build)


def audit(name="Example.root", axioms="[propext, Classical.choice, Quot.sound]"):
    statement = (f"'{name}' does not depend on any axioms" if axioms is None
                 else f"'{name}' depends on axioms: {axioms}")
    return (f"TYPE_BEGIN:{name}\n{name} : True\nTYPE_END:{name}\n"
            f"AXIOMS_BEGIN:{name}\n{statement}\nAXIOMS_END:{name}\n")


class AuditTests(unittest.TestCase):
    def test_accepts_standard_axioms(self):
        parsed = build.parse_audit(audit(), ["Example.root"])
        self.assertEqual(set(parsed["axioms"]["Example.root"]), build.STANDARD_AXIOMS)
        self.assertEqual(parsed["types"]["Example.root"], "Example.root : True")

    def test_accepts_axiom_free_definition(self):
        self.assertEqual(build.parse_audit(audit(axioms=None), ["Example.root"])["axioms"],
                         {"Example.root": []})

    def test_lean_433_universe_output_does_not_hide_compiler_failure(self):
        observed = audit(axioms="[propext, Classical.choice.{u}, Quot.sound.{u}]")
        parsed = build.parse_audit(observed, ["Example.root"])
        self.assertEqual(set(parsed["axioms"]["Example.root"]), build.STANDARD_AXIOMS)
        with self.assertRaises(build.BuildError):
            build.parse_audit("Audit.lean:4:0: error: Unknown option `pp.width`\n" + observed,
                              ["Example.root"])

    def test_rejects_custom_axiom_and_sorry(self):
        for value in ("[Example.admission]", "[sorryAx]", "[propext, sorryAx]"):
            with self.subTest(value=value), self.assertRaises(build.BuildError):
                build.parse_audit(audit(axioms=value), ["Example.root"])

    def test_manifest_cannot_expand_allowlist(self):
        with self.assertRaises(build.BuildError):
            build.parse_audit(audit(), ["Example.root"], set(build.STANDARD_AXIOMS) | {"sorryAx"})

    def test_rejects_missing_duplicate_or_reordered_records(self):
        samples = [audit().replace("TYPE_END:Example.root\n", ""), audit() + audit(),
                   audit().replace("TYPE_BEGIN:Example.root", "TYPE_BEGIN:Other.root")]
        for value in samples:
            with self.subTest(value=value), self.assertRaises(build.BuildError):
                build.parse_audit(value, ["Example.root"])

    def test_rejects_empty_type_and_wrong_axiom_identity(self):
        for value in (audit().replace("Example.root : True\n", ""),
                      audit().replace("'Example.root' depends", "'Other.root' depends")):
            with self.assertRaises(build.BuildError):
                build.parse_audit(value, ["Example.root"])

    def test_rejects_sorry_warning_outside_blocks(self):
        with self.assertRaises(build.BuildError):
            build.parse_audit(audit() + "warning: declaration uses sorry\n", ["Example.root"])

    def test_multiple_declarations(self):
        parsed = build.parse_audit(audit() + audit("Example.second", None),
                                   ["Example.root", "Example.second"])
        self.assertEqual(len(parsed["types"]), 2)


class SourceTests(unittest.TestCase):
    def test_nested_comments_and_strings_cannot_inject_imports(self):
        source = '/- import Fake /- import Other -/ -/\nimport Mathlib.Init -- import Wrong\n'
        source += 'def text := "import Bad"\npublic import Lean Elab\n'
        self.assertEqual(build.lean_imports(source), ["Mathlib.Init", "Lean", "Elab"])

    def test_missing_local_import_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaises(build.BuildError):
                build.current_closure(root, {}, ["SingularClosure.Missing"], {})

    def test_amended_source_changes_hash_and_records_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "_vendor/SingularClosure/Test.lean"
            source.parent.mkdir(parents=True)
            old = b"import Mathlib.Init\ntheorem root : True := True.intro\n"
            source.write_bytes(old)
            index = {"SingularClosure.Test": source}
            baseline = {"SingularClosure.Test": {"sha256": build.sha256(old)}}
            before, _, drift = build.current_closure(root, index, list(index), baseline)
            self.assertFalse(drift)
            source.write_bytes(old + b"-- amendment\n")
            after, _, drift = build.current_closure(root, index, list(index), baseline)
            self.assertNotEqual(before[0]["sha256"], after[0]["sha256"])
            self.assertEqual(len(drift), 1)

    def test_audit_reuse_requires_checksum_and_reparse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            identity = "1" * 64
            relative = "registry/audits/Example-" + identity + ".log"
            path = root / relative
            path.parent.mkdir(parents=True)
            path.write_text(audit())
            entry = {"id": "Example", "spec": {"declarations": [{"name": "Example.root"}],
                      "allowed_axioms": sorted(build.STANDARD_AXIOMS)}}
            old = {"status": "PASS", "input_hash": identity, "audit_log": relative,
                   "audit_sha256": build.sha256(path.read_bytes())}
            self.assertIsNotNone(build.reuse_audit(root, old, entry, identity))
            path.write_text(audit(axioms="[sorryAx]"))
            old["audit_sha256"] = build.sha256(path.read_bytes())
            self.assertIsNone(build.reuse_audit(root, old, entry, identity))

    def test_validate_only_cannot_execute_subprocess(self):
        plan = {"toolchain": "leanprover/lean4:v4.33.0", "mathlib_commit": "a" * 40,
                "all_endpoint_ids": ["Example"],
                "endpoints": [{"id": "Example", "input_plan_hash": "b" * 64, "source_drift": []}]}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = root / "registry/current.json"
            report.parent.mkdir(parents=True)
            report.write_text('{"status":"PASS"}\n')
            original = report.read_bytes()
            with patch.object(build, "validate", return_value=plan), \
                 patch.object(build.subprocess, "run", side_effect=AssertionError("no subprocess allowed")):
                result = build.run_build(root, report, None, False, True, {})
            self.assertEqual(result, 0)
            self.assertEqual(report.read_bytes(), original)

    def test_non_ci_non_native_execution_fails_before_subprocess(self):
        plan = {"toolchain": "leanprover/lean4:v4.33.0", "mathlib_commit": "a" * 40,
                "all_endpoint_ids": ["Example"],
                "endpoints": [{"id": "Example", "input_plan_hash": "b" * 64, "source_drift": []}]}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = root / "registry/current.json"
            with patch.object(build, "validate", return_value=plan), \
                 patch.object(build.subprocess, "run", side_effect=AssertionError("must not execute")):
                result = build.run_build(root, report, None, False, False, {})
            self.assertEqual(result, 1)
            self.assertEqual(json.loads(report.read_text())["status"], "FAIL")


class RetainedDependencyCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.plan = {"toolchain": "leanprover/lean4:v4.33.0", "mathlib_commit": "a" * 40,
                     "dependency_lock": {"packages": [{"name": "mathlib", "rev": "a" * 40}]}}
        self.verified = [{"name": "mathlib", "commit": "a" * 40, "tracked_source_clean": True}]
        self.previous = {"status": "PASS", "compiler_executed": True, "all_endpoints_selected": True,
                         "toolchain": self.plan["toolchain"], "mathlib_commit": "a" * 40,
                         "platform": {"system": build.platform.system(), "machine": build.platform.machine()},
                         "verified_dependencies": self.verified}
        self.environment = {"MATERIAL_RESTORE_MODE": "previous_passed_container",
                            "MATERIAL_PARENT_IMAGE_DIGEST": "ghcr.io/owner/repo@sha256:" + "b" * 64}
        self.stem = self.root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Init"
        self.stem.parent.mkdir(parents=True)
        for suffix in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace"):
            Path(str(self.stem) + suffix).write_text("installed")

    def ready(self):
        return build.retained_dependency_cache_ready(self.root, self.plan, self.previous,
                                                     ["Mathlib.Init"], self.verified, self.environment)

    def test_compatible_passed_objects_skip_network_hydration(self):
        self.assertEqual(self.ready(), (True, "compatible_passed_dependency_outputs"))

    def test_cold_or_digestless_execution_requires_cache_get(self):
        self.environment["MATERIAL_RESTORE_MODE"] = "cold_bootstrap"
        self.assertFalse(self.ready()[0])
        self.environment["MATERIAL_RESTORE_MODE"] = "previous_passed_container"
        self.environment["MATERIAL_PARENT_IMAGE_DIGEST"] = ""
        self.assertFalse(self.ready()[0])

    def test_missing_new_import_or_trace_requires_cache_get(self):
        Path(str(self.stem) + ".trace").unlink()
        self.assertFalse(self.ready()[0])
        self.assertFalse(build.retained_dependency_cache_ready(
            self.root, self.plan, self.previous, ["Mathlib.NewImport"],
            self.verified, self.environment)[0])

    def test_changed_or_dirty_dependency_cannot_skip_hydration(self):
        self.verified = [{"name": "mathlib", "commit": "c" * 40, "tracked_source_clean": True}]
        self.assertFalse(self.ready()[0])
        self.verified = [{"name": "mathlib", "commit": "a" * 40, "tracked_source_clean": False}]
        self.assertFalse(self.ready()[0])

    def test_failed_or_other_platform_report_requires_cache_get(self):
        self.previous["status"] = "FAIL"
        self.assertFalse(self.ready()[0])
        self.previous["status"] = "PASS"
        self.previous["platform"] = {"system": "Other", "machine": "Other"}
        self.assertFalse(self.ready()[0])


class SerialModuleScheduleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        records = [{"module": "A", "sha256": "a", "imports": []},
                   {"module": "B", "sha256": "b", "imports": ["A"]},
                   {"module": "C", "sha256": "c", "imports": ["B"]},
                   {"module": "D", "sha256": "d", "imports": []},
                   {"module": "Example.Audit", "sha256": "x", "imports": ["C"]}]
        self.plan = {"config": {"lakefile.lean": "config"}, "endpoints": [
            {"id": "Example", "spec": {"audit_module": "Example.Audit"}, "files": records}]}
        self.previous = {"status": "PASS", "build_configuration": self.plan["config"],
                         "local_module_inputs": {r["module"]: r["sha256"] for r in records}}
        for name in ("A", "B", "C", "D"):
            stem = self.root / ".lake/build/lib/lean" / name
            stem.parent.mkdir(parents=True, exist_ok=True)
            for suffix in (".olean", ".trace"):
                Path(str(stem) + suffix).write_text("compiled")

    def test_cold_schedule_is_topological_and_excludes_audit_module(self):
        order, inputs, mode = build.serial_module_plan(self.root, self.plan, {}, False)
        self.assertLess(order.index("A"), order.index("B"))
        self.assertLess(order.index("B"), order.index("C"))
        self.assertNotIn("Example.Audit", order)
        self.assertEqual(mode, "all_local_modules")

    def test_warm_no_change_schedules_no_compilation(self):
        self.assertEqual(build.serial_module_plan(self.root, self.plan, self.previous, True)[0], [])

    def test_amended_module_schedules_transitive_dependents_only(self):
        self.plan["endpoints"][0]["files"][1]["sha256"] = "amended"
        self.assertEqual(build.serial_module_plan(self.root, self.plan, self.previous, True)[0], ["B", "C"])

    def test_missing_output_schedules_dependency_and_dependents(self):
        (self.root / ".lake/build/lib/lean/A.trace").unlink()
        self.assertEqual(build.serial_module_plan(self.root, self.plan, self.previous, True)[0], ["A", "B", "C"])

    def test_cycle_fails_before_compiler(self):
        self.plan["endpoints"][0]["files"][0]["imports"] = ["C"]
        with self.assertRaises(build.BuildError):
            build.serial_module_plan(self.root, self.plan, {}, False)


class StreamingCommandTests(unittest.TestCase):
    class Process:
        def __init__(self, stdout, returncode=0, release=None):
            self.stdout = stdout
            self.returncode = returncode
            self.release = release
        def wait(self, timeout=None):
            return self.returncode
        def kill(self):
            self.returncode = -9
            if self.release is not None:
                self.release.set()

    def test_log_is_flushed_before_command_completion(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "stream.log"
            release = threading.Event()
            def lines():
                yield "phase one\n"
                release.wait(2)
                yield "phase two\n"
            process = self.Process(lines(), release=release)
            result = []
            with patch.object(build.subprocess, "Popen", return_value=process):
                worker = threading.Thread(target=lambda: result.append(
                    build.execute(["mock-compiler"], root, log, {"MATERIAL_COMMAND_TIMEOUT": "3"})))
                worker.start()
                deadline = time.monotonic() + 1
                try:
                    while time.monotonic() < deadline and (not log.exists() or "phase one" not in log.read_text()):
                        time.sleep(0.01)
                    self.assertIn("phase one", log.read_text())
                    self.assertTrue(worker.is_alive())
                finally:
                    release.set()
                    worker.join(2)
            self.assertEqual(result[0][0], "phase one\nphase two\n")

    def test_timeout_retains_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "timeout.log"
            release = threading.Event()
            def lines():
                yield "before timeout\n"
                release.wait(3)
            process = self.Process(lines(), release=release)
            with patch.object(build.subprocess, "Popen", return_value=process), \
                    self.assertRaises(build.subprocess.TimeoutExpired):
                build.execute(["mock-compiler"], root, log, {"MATERIAL_COMMAND_TIMEOUT": "1"})
            self.assertIn("before timeout", log.read_text())
            self.assertIn("partial output retained", log.read_text())

    def test_nonzero_exit_retains_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "failure.log"
            process = self.Process(io.StringIO("compiler error details\n"), returncode=1)
            with patch.object(build.subprocess, "Popen", return_value=process), self.assertRaises(build.BuildError):
                build.execute(["mock-compiler"], root, log, {})
            self.assertIn("compiler error details", log.read_text())


class PipelineTests(unittest.TestCase):
    def plan(self):
        return {"toolchain": "leanprover/lean4:v4.33.0", "mathlib_commit": "a" * 40,
                "all_endpoint_ids": ["Example"], "dependency_lock": {"packages": []},
                "endpoints": [{"id": "Example", "input_plan_hash": "b" * 64,
                               "source_drift": [], "files": [],
                               "external_imports": ["Mathlib.Init"],
                               "spec": {"declarations": [{"name": "Example.root"}],
                                        "allowed_axioms": sorted(build.STANDARD_AXIOMS)}}]}

    def fake_execute(self, commands, fail_rerun=False):
        builds = [0]

        def run(command, root, log, environment):
            commands.append(command)
            output = ""
            if command == ["lake", "env", "lean", "--version"]:
                output = "Lean (version 4.33.0, x86_64-unknown-linux-gnu, Release)\n"
            elif command == ["lake", "env", "lean", "Example/Audit.lean"]:
                output = audit()
            elif command[:2] == ["lake", "build"]:
                builds[0] += 1
                if fail_rerun and builds[0] == 2:
                    raise build.BuildError("simulated no-op rerun failure")
            log.parent.mkdir(parents=True, exist_ok=True)
            log.write_text(output)
            return output, 0.01
        return run

    def test_pass_requires_fresh_audit_on_every_commit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lake-manifest.json").write_text('{"packages":[]}\n')
            report = root / "registry/current.json"
            commands = []
            with patch.object(build, "validate", return_value=self.plan()), \
                 patch.object(build, "verify_dependencies", return_value=[]), \
                 patch.object(build, "execute", side_effect=self.fake_execute(commands)), \
                 patch.object(build.subprocess, "run", side_effect=AssertionError("all compiler calls mocked")):
                self.assertEqual(build.run_build(root, report, None, False, False,
                                                {"CI": "true", "GITHUB_SHA": "1" * 40}), 0)
                first = json.loads(report.read_text())
                self.assertEqual(first["status"], "PASS")
                self.assertFalse(first["endpoints"][0]["audit_reused"])
                self.assertEqual(build.run_build(root, report, None, False, False,
                                                {"CI": "true", "GITHUB_SHA": "2" * 40}), 0)
            second = json.loads(report.read_text())
            self.assertEqual(second["commit"], "2" * 40)
            self.assertFalse(second["endpoints"][0]["audit_reused"])
            self.assertEqual(second["endpoints"][0]["audit_origin_commit"], "2" * 40)
            self.assertEqual(commands.count(["lake", "env", "lean", "Example/Audit.lean"]), 2)
            self.assertEqual(commands.count(["lake", "build", "Example"]), 4)

    def test_failed_rerun_cannot_promote_even_after_theorem_audit_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lake-manifest.json").write_text('{"packages":[]}\n')
            report = root / "registry/current.json"
            with patch.object(build, "validate", return_value=self.plan()), \
                 patch.object(build, "verify_dependencies", return_value=[]), \
                 patch.object(build, "execute", side_effect=self.fake_execute([], fail_rerun=True)), \
                 patch.object(build.subprocess, "run", side_effect=AssertionError("all compiler calls mocked")):
                result = build.run_build(root, report, None, False, False,
                                         {"CI": "true", "GITHUB_SHA": "1" * 40})
            self.assertEqual(result, 1)
            self.assertEqual(json.loads(report.read_text())["status"], "FAIL")


if __name__ == "__main__":
    unittest.main()
