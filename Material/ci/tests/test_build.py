"""Pure parser/filesystem and mocked-run tests; no Lean or Lake execution."""
from __future__ import annotations

import importlib.util
import json
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

    def test_pass_requires_audit_then_reuses_exact_evidence_on_next_commit(self):
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
            self.assertTrue(second["endpoints"][0]["audit_reused"])
            self.assertEqual(second["endpoints"][0]["audit_origin_commit"], "1" * 40)
            self.assertEqual(commands.count(["lake", "env", "lean", "Example/Audit.lean"]), 1)
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
