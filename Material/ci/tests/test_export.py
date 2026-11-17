"""Filesystem-only regression tests; no Lean, Lake or subprocess execution."""

from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import zipfile


SCRIPT = Path(__file__).resolve().parents[1] / "export_endpoint.py"
SPEC = importlib.util.spec_from_file_location("material_export", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
EXPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXPORT)


class ExportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.root = self.base / "Material"
        self.root.mkdir()
        self.output = self.base / "standalone"
        self.records = []
        self.source("SingularClosure.Base", "import Mathlib\n/- /- import Missing.X -/ -/\ndef α : Nat := 1\n".encode())
        self.source("SingularClosure.Leaf", b"import SingularClosure.Base\r\n\ndef leaf : Nat := 2\r\n")
        self.source("SingularClosure.Unused", b"import Mathlib\ndef unused : Nat := 3\n")
        self.put("Example/Endpoint.lean", b"import SingularClosure.Leaf\n")
        self.put("Example/Audit.lean", b"import Example.Endpoint\n#check leaf\n#print axioms leaf\n")
        self.put("lean-toolchain", (EXPORT.TOOLCHAIN + "\n").encode())
        self.put("ci/build.py", b"# Self-contained fixture; no compiler execution.\n")
        self.endpoint = {
            "id": "Example", "endpoint_module": "Example.Endpoint",
            "audit_module": "Example.Audit", "imports": ["SingularClosure.Leaf"],
            "declarations": [{"name": "leaf", "kind": "def"}],
        }
        self.closure = {
            "endpoint": "Example", "lean_toolchain": EXPORT.TOOLCHAIN,
            "mathlib_commit": EXPORT.MATHLIB_REV,
            "roots": ["SingularClosure.Leaf"], "local_module_count": 2,
            "files": copy.deepcopy(self.records[:2]), "source_closure_sha256": "fixture",
        }
        self.manifest = {"schema_version": 1, "files": self.records,
                         "local_module_count": 3, "provenance": []}
        self.save("Example/endpoint.json", self.endpoint)
        self.save("Example/closure.json", self.closure)
        self.save("_vendor/source-manifest.json", self.manifest)
        self.save("endpoints.json", {
            "endpoint_count": 1, "declaration_count": 1,
            "endpoints": [{"id": "Example", "manifest": "Example/endpoint.json",
                           "closure": "Example/closure.json"}],
        })
        self.save("lake-manifest.json", {
            "version": "1.2.0", "name": "material", "packagesDir": ".lake/packages",
            "packages": [{"name": "mathlib", "rev": EXPORT.MATHLIB_REV,
                          "url": "https://github.com/leanprover-community/mathlib4"}],
        })

    def put(self, relative: str, content: bytes) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

    def save(self, relative: str, value: dict) -> None:
        self.put(relative, (json.dumps(value, ensure_ascii=False) + "\n").encode())

    def source(self, module: str, content: bytes) -> None:
        relative = "_vendor/" + module.replace(".", "/") + ".lean"
        self.put(relative, content)
        self.records.append({
            "module": module, "path": relative, "local_path": relative,
            "sha256": EXPORT.sha256(content), "git_blob_sha": EXPORT.git_blob_sha(content),
            "imports": EXPORT.imports_of(content),
        })

    def export(self, **kwargs) -> dict:
        return EXPORT.export_endpoint("Example", self.output, root=self.root, **kwargs)

    def test_complete_subset_preserves_exact_bytes_and_lock(self) -> None:
        result = self.export()
        self.assertEqual(result["local_modules"], 2)
        for row in self.records[:2]:
            self.assertEqual((self.root / row["path"]).read_bytes(),
                             (self.output / row["path"]).read_bytes())
        self.assertFalse((self.output / self.records[2]["path"]).exists())
        self.assertEqual(EXPORT.load_json(self.output / "lake-manifest.json")["name"], "material_endpoint")
        self.assertEqual(EXPORT.load_json(self.output / "endpoints.json")["endpoint_count"], 1)
        self.assertEqual(len(EXPORT.load_json(self.output / "_vendor/source-manifest.json")["files"]), 2)
        self.assertIn("--native --endpoint Example", (self.output / "run.cmd").read_text())
        self.assertIn("--endpoint Example", (self.output / "run.sh").read_text())
        self.assertNotIn("--native", (self.output / "run.sh").read_text())
        self.assertIn('${CI:-}', (self.output / "run.sh").read_text())
        self.assertIn('srcDir := "_vendor"', (self.output / "lakefile.lean").read_text())
        info = EXPORT.load_json(self.output / "export.json")
        self.assertEqual(info["status"], "PREPARED")
        self.assertEqual(info["local_lean_executions"], 0)
        self.assertIsNone(info["external_compiler_evidence"])
        self.assertIsNone(info["theorem_axiom_audit"])

    def test_zip_contains_complete_export(self) -> None:
        archive = self.base / "endpoint.zip"
        self.export(zip_path=archive)
        with zipfile.ZipFile(archive) as handle:
            self.assertIn("standalone/Example/Audit.lean", handle.namelist())
            self.assertIn("standalone/_vendor/SingularClosure/Base.lean", handle.namelist())
            self.assertEqual(handle.read("standalone/_vendor/SingularClosure/Leaf.lean"),
                             (self.root / self.records[1]["path"]).read_bytes())
            self.assertTrue(all(".." not in Path(name).parts for name in handle.namelist()))

    def test_missing_declared_transitive_dependency_is_rejected(self) -> None:
        self.closure["files"] = self.closure["files"][1:]
        self.save("Example/closure.json", self.closure)
        with self.assertRaisesRegex(EXPORT.ExportError, "incomplete or stale"):
            self.export()
        self.assertFalse(self.output.exists())

    def test_missing_source_module_is_rejected(self) -> None:
        self.manifest["files"] = self.records[1:]
        self.save("_vendor/source-manifest.json", self.manifest)
        with self.assertRaisesRegex(EXPORT.ExportError, "Missing transitive local module"):
            self.export()

    def test_modified_source_is_rejected(self) -> None:
        self.put(self.records[0]["path"], b"import Mathlib\ndef changed : Nat := 7\n")
        with self.assertRaisesRegex(EXPORT.ExportError, "content hash mismatch"):
            self.export()

    def test_stale_manifest_imports_are_rejected(self) -> None:
        self.manifest["files"][1]["imports"] = []
        self.save("_vendor/source-manifest.json", self.manifest)
        with self.assertRaisesRegex(EXPORT.ExportError, "Stale import manifest"):
            self.export()

    def test_changed_endpoint_roots_are_rejected(self) -> None:
        self.put("Example/Endpoint.lean", b"import SingularClosure.Unused\n")
        with self.assertRaisesRegex(EXPORT.ExportError, "closure roots disagree"):
            self.export()

    def test_unpinned_toolchain_is_rejected(self) -> None:
        self.put("lean-toolchain", b"leanprover/lean4:nightly\n")
        with self.assertRaisesRegex(EXPORT.ExportError, "toolchain differs"):
            self.export()

    def test_unpinned_mathlib_is_rejected(self) -> None:
        lock = EXPORT.load_json(self.root / "lake-manifest.json")
        lock["packages"][0]["rev"] = "master"
        self.save("lake-manifest.json", lock)
        with self.assertRaisesRegex(EXPORT.ExportError, "Mathlib lock differs"):
            self.export()

    def test_existing_output_is_preserved(self) -> None:
        self.output.mkdir()
        (self.output / "existing.txt").write_text("preserve")
        with self.assertRaisesRegex(EXPORT.ExportError, "absent or empty"):
            self.export()
        self.assertEqual((self.output / "existing.txt").read_text(), "preserve")

    def test_path_traversal_is_rejected(self) -> None:
        with self.assertRaisesRegex(EXPORT.ExportError, "Invalid endpoint ID"):
            EXPORT.export_endpoint("../Example", self.output, root=self.root)
        self.records[0]["path"] = "_vendor/../../outside.lean"
        self.save("_vendor/source-manifest.json", self.manifest)
        with self.assertRaisesRegex(EXPORT.ExportError, "path does not match module name"):
            self.export()

    def test_audit_only_dependency_cannot_escape_the_closure(self) -> None:
        self.put("Example/Audit.lean", b"import Example.Endpoint\nimport SingularClosure.Unused\n")
        with self.assertRaisesRegex(EXPORT.ExportError, "incomplete or stale"):
            self.export()

    def test_comments_do_not_create_fake_dependencies(self) -> None:
        source = b'import Mathlib\n/- import Missing.X /- import Missing.Y -/ -/\n#eval "import Missing.Z"\n'
        self.assertEqual(EXPORT.imports_of(source), ["Mathlib"])


if __name__ == "__main__":
    unittest.main()
