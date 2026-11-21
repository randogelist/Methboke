#!/usr/bin/env python3
"""Apply the first statement-preserving R3 datum-admission proof repair.

This script performs static text/JSON transformations only.  It replaces the
single brittle definitional `change` with Mathlib's explicit Schwartz line
Derivative theorem, synchronizes the inactive source copy, source hashes,
endpoint provenance and closure manifests, and runs static validators.  It does
not invoke Lean, Lake, a kernel, or compiled objects.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MATERIAL = ROOT / "Material"
MODULE = "MethbokeAddon.R3Ehrenfest.DatumAdmission"
PACKAGE = "R3EhrenfestDatumAdmission"
SOURCE_REL = "MethbokeAddon/R3Ehrenfest/DatumAdmission.lean"
SOURCE = MATERIAL / SOURCE_REL
CANDIDATE = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_DATUM_CANDIDATE/DatumAdmission.lean.txt"
STATUS = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_DATUM_CANDIDATE/STATUS.json"

OLD = """  rw [htrace]\n  simp_rw [hx]\n  change (∑ j : Fin 3,\n      (fderiv ℝ (a.value : Space → Space) x (coordinateVector j)) j) •\n        coordinateVector 0 = 0\n  rw [smoothDatum_divergence_sum a x]\n  simp\n"""

NEW = """  rw [htrace]\n  simp_rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]\n  rw [smoothDatum_divergence_sum a x]\n  simp\n"""


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def save(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint(value: object) -> str:
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def import_build_module():
    path = MATERIAL / "ci/build.py"
    spec = importlib.util.spec_from_file_location("material_build_static", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load Material/ci/build.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def replace_exact(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(OLD) != 1:
        raise RuntimeError(f"expected exactly one diagnosed proof block in {path}")
    path.write_text(text.replace(OLD, NEW), encoding="utf-8")


def update_owned(source_revision: str) -> None:
    path = MATERIAL / "owned-sources.json"
    data = load(path)
    row = next((item for item in data["modules"] if item.get("module") == MODULE), None)
    if row is None:
        raise RuntimeError("owned source row missing")
    row["sha256"] = sha256(SOURCE.read_bytes())
    row["origin"] = {
        "repository": "randogelist/Methboke",
        "revision": source_revision,
        "path": "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_DATUM_CANDIDATE/DatumAdmission.lean.txt",
        "role": "Statement-preserving repair of the single externally diagnosed line-derivative normalization; active and inactive source bytes are identical. Matching external verification remains mandatory."
    }
    save(path, data)


def update_endpoint(source_revision: str) -> None:
    path = MATERIAL / PACKAGE / "endpoint.json"
    data = load(path)
    root = data["source_roots"][0]
    root["source_snapshot"]["revision"] = source_revision
    root["source_snapshot"]["role"] = (
        "Exact statement-preserving repair snapshot replacing one brittle definitional change by "
        "SchwartzMap.lineDerivOp_apply_eq_fderiv; matching registered external verification pending."
    )
    for declaration in data["declarations"]:
        declaration["source"]["revision"] = source_revision
        declaration["source"]["revision_status"] = "EXACT_REPAIRED_SOURCE_SNAPSHOT_PENDING_EXTERNAL_VERIFICATION"
    save(path, data)


def compute_closure(build, source_revision: str) -> tuple[str, int]:
    source_manifest = load(MATERIAL / "_vendor/source-manifest.json")
    baseline = {item["module"]: item for item in source_manifest["files"]}
    index = build.module_index(MATERIAL)
    files, external, drift = build.current_closure(
        MATERIAL, index, [PACKAGE + ".Endpoint", PACKAGE + ".Audit"], baseline
    )
    payload = {"roots": [MODULE], "files": files, "external_imports": external}
    closure_hash = fingerprint(payload)
    closure = load(MATERIAL / PACKAGE / "closure.json")
    closure.update({
        "source_revision_status": "STATEMENT_PRESERVING_REPAIR_PENDING_MATCHING_EXTERNAL_VERIFICATION",
        "source_baseline": source_revision,
        "source_preparation_revision": source_revision,
        "roots": [MODULE],
        "files": files,
        "external_imports": external,
        "source_drift": drift,
        "source_closure_sha256": closure_hash,
        "validation_boundary": "Static source/import/hash inspection only. The repair changes no public declaration statement. Matching external compiler, independent exact-type consumers, standard-only named axiom reports, publication and full Material acceptance are required."
    })
    save(MATERIAL / PACKAGE / "closure.json", closure)
    return closure_hash, len(files)


def update_registry(closure_hash: str, source_modules: int) -> None:
    path = MATERIAL / "endpoints.json"
    data = load(path)
    row = next((item for item in data["endpoints"] if item.get("id") == PACKAGE), None)
    if row is None:
        raise RuntimeError("endpoint registry row missing")
    row["source_closure_sha256"] = closure_hash
    row["local_source_modules"] = source_modules
    data["status"] = "PENDING_EXTERNAL_CI"
    save(path, data)


def update_status(source_revision: str, closure_hash: str) -> None:
    data = load(STATUS)
    data.update({
        "status": "REPAIRED_AFTER_EXTERNAL_DIAGNOSTIC_PENDING_MATCHING_EXTERNAL_CI",
        "repair_source_revision": source_revision,
        "source_closure_sha256": closure_hash,
        "external_compilation_completed": False,
        "exact_type_and_axiom_acceptance": False,
        "root_proved": False,
        "stopped_witness_constructed": False,
        "repair": {
            "failed_source_revision": "090dd7efc311cc8f079600f31d7a7804e2b890f0",
            "failed_run_id": 44883719460,
            "failed_module": MODULE,
            "diagnostic": "One change tactic attempted definitional reduction from Schwartz directional derivatives to fderiv values.",
            "resolution": "Rewrite explicitly with SchwartzMap.lineDerivOp_apply_eq_fderiv.",
            "public_statement_changes": False,
            "prior_accepted_source_changes": False,
            "local_lean_executions": 0
        }
    })
    save(STATUS, data)


def main() -> None:
    source_revision = os.environ.get("GITHUB_SHA", "")
    if len(source_revision) != 40:
        raise RuntimeError("GITHUB_SHA exact repair source required")
    replace_exact(SOURCE)
    replace_exact(CANDIDATE)
    if SOURCE.read_bytes() != CANDIDATE.read_bytes():
        raise RuntimeError("active and inactive repaired source copies differ")
    update_owned(source_revision)
    update_endpoint(source_revision)
    build = import_build_module()
    closure_hash, source_modules = compute_closure(build, source_revision)
    update_registry(closure_hash, source_modules)
    update_status(source_revision, closure_hash)
    subprocess.run(["python3", "scripts/count_lean_lines.py", "--write-readme"], cwd=ROOT, check=True)
    subprocess.run(["python3", "Material/ci/build.py", "--validate-only"], cwd=ROOT, check=True)
    print(json.dumps({
        "status": "REPAIRED_PENDING_MATCHING_EXTERNAL_CI",
        "package": PACKAGE,
        "declarations": 15,
        "source_closure_sha256": closure_hash,
        "public_statement_changes": False,
        "local_lean_executions": 0,
        "root_proved": False
    }, indent=2))


if __name__ == "__main__":
    main()
