#!/usr/bin/env python3
"""Activate the prepared R3 derivative-representative package without invoking Lean.

This is a one-shot static repository transformation. It copies the already
reviewed .lean.txt candidate into active Material paths, registers its exact
sources and endpoint, computes the current source closure, updates the scoped
R3 goal package list, and refreshes the README Lean source count.
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
CANDIDATE = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_LAYER_CANDIDATE"
MODULE = "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative"
PACKAGE = "R3EhrenfestDerivativeRepresentative"
SOURCE_REL = "MethbokeAddon/R3Ehrenfest/DerivativeRepresentative.lean"
SOURCE = MATERIAL / SOURCE_REL
PACKAGE_DIR = MATERIAL / PACKAGE
SCOPE = (
    "Classical coordinate derivatives of the actual smooth sharp-cutoff representative "
    "equal representatives of the already constructed native Fourier derivatives. "
    "Ordered coordinate words have explicit finite fixed-cutoff Bernstein bounds. "
    "No nonlinear flow, cutoff-uniform comparison, literal NSE-A Sobolev admission, "
    "stopped-bound witness or obstruction root is asserted."
)
DECLARATIONS = [
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply", "theorem"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate", "theorem"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient", "theorem"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM", "definition"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le", "theorem"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate", "definition"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative", "theorem"),
    ("MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound", "theorem"),
]


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object: {path}")
    return value


def save(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
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


def copy_candidate() -> None:
    SOURCE.parent.mkdir(parents=True, exist_ok=True)
    SOURCE.write_bytes((CANDIDATE / "DerivativeRepresentative.lean.txt").read_bytes())
    PACKAGE_DIR.mkdir(parents=True, exist_ok=True)
    (PACKAGE_DIR / "Endpoint.lean").write_bytes((CANDIDATE / "Endpoint.lean.txt").read_bytes())
    (PACKAGE_DIR / "Audit.lean").write_bytes((CANDIDATE / "Audit.lean.txt").read_bytes())


def register_owned(build, source_revision: str) -> None:
    path = MATERIAL / "owned-sources.json"
    data = load(path)
    modules = data.get("modules")
    if not isinstance(modules, list):
        raise RuntimeError("owned-sources modules must be a list")
    imports = build.lean_imports(SOURCE.read_text(encoding="utf-8"))
    record = {
        "module": MODULE,
        "path": SOURCE_REL,
        "sha256": sha256(SOURCE.read_bytes()),
        "imports": imports,
        "origin": {
            "repository": "randogelist/Methboke",
            "revision": source_revision,
            "path": "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_LAYER_CANDIDATE/DerivativeRepresentative.lean.txt",
            "role": "Exact inactive candidate bytes promoted unchanged into the active owned source path. Matching external verification remains mandatory."
        },
        "origin_kind": "new_owned_development_at_exact_source_snapshot"
    }
    existing = [row for row in modules if isinstance(row, dict) and row.get("module") == MODULE]
    if existing:
        if existing != [record]:
            raise RuntimeError("conflicting owned-source registration")
    else:
        modules.append(record)
    save(path, data)


def write_endpoint(source_revision: str) -> None:
    declarations = []
    for name, kind in DECLARATIONS:
        declarations.append({
            "name": name,
            "kind": kind,
            "source_kind": "def" if kind == "definition" else "theorem",
            "source": {
                "repository": "randogelist/Methboke",
                "path": "Material/" + SOURCE_REL,
                "module": MODULE,
                "revision": source_revision,
                "revision_status": "EXACT_INACTIVE_SOURCE_SNAPSHOT_ACTIVATED_PENDING_EXTERNAL_VERIFICATION"
            },
            "scope": SCOPE
        })
    endpoint = {
        "schema_version": 1,
        "id": PACKAGE,
        "endpoint_module": PACKAGE + ".Endpoint",
        "audit_module": PACKAGE + ".Audit",
        "imports": [MODULE],
        "source_roots": [{
            "module": MODULE,
            "path": SOURCE_REL,
            "storage": "owned_source",
            "origin_kind": "new_owned_development_at_exact_source_snapshot",
            "source_snapshot": {
                "repository": "randogelist/Methboke",
                "revision": source_revision,
                "path": "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_LAYER_CANDIDATE/DerivativeRepresentative.lean.txt",
                "role": "Exact candidate bytes activated unchanged; matching registered external verification pending."
            }
        }],
        "declarations": declarations,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "scope": SCOPE
    }
    save(PACKAGE_DIR / "endpoint.json", endpoint)
    (PACKAGE_DIR / "README.md").write_text(
        "# R3 Ehrenfest derivative representative\n\n"
        + SCOPE + "\n\n"
        + "**Status:** active A-tier candidate. Matching cached external compilation, "
          "independent exact-type consumers, fresh named axiom reports, publication and "
          "the full Material acceptance gate remain mandatory. The R3 obstruction root "
          "and stopped-bound witness remain open.\n",
        encoding="utf-8"
    )


def compute_closure(build, source_revision: str) -> tuple[dict, str, int]:
    source_manifest = load(MATERIAL / "_vendor/source-manifest.json")
    baseline = {item["module"]: item for item in source_manifest["files"]}
    index = build.module_index(MATERIAL)
    files, external, drift = build.current_closure(
        MATERIAL, index, [PACKAGE + ".Endpoint", PACKAGE + ".Audit"], baseline
    )
    payload = {
        "roots": [MODULE],
        "files": files,
        "external_imports": external,
    }
    closure_hash = fingerprint(payload)
    closure = {
        "schema_version": 1,
        "endpoint": PACKAGE,
        "source_revision_status": "MATCHING_NATIVE_EXTERNAL_VERIFICATION_PENDING",
        "source_baseline": source_revision,
        "source_preparation_revision": source_revision,
        "lean_toolchain": (MATERIAL / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_commit": source_manifest["mathlib_commit"],
        "source_closure_hash_policy": "SHA256 of compact sorted-key JSON object containing roots, files, external_imports.",
        "validation_boundary": "Static source/import/hash inspection only. Matching external compiler, independent exact-type consumers, standard-only named axiom reports, publication and full Material acceptance are required.",
        "roots": [MODULE],
        "files": files,
        "external_imports": external,
        "source_drift": drift,
        "source_closure_sha256": closure_hash
    }
    save(PACKAGE_DIR / "closure.json", closure)
    return closure, closure_hash, len(files)


def register_endpoint(closure_hash: str, local_source_modules: int) -> None:
    path = MATERIAL / "endpoints.json"
    data = load(path)
    endpoints = data.get("endpoints")
    if not isinstance(endpoints, list):
        raise RuntimeError("endpoints must be a list")
    record = {
        "id": PACKAGE,
        "endpoint_module": PACKAGE + ".Endpoint",
        "audit_module": PACKAGE + ".Audit",
        "manifest": PACKAGE + "/endpoint.json",
        "closure": PACKAGE + "/closure.json",
        "declarations": len(DECLARATIONS),
        "local_source_modules": local_source_modules,
        "source_closure_sha256": closure_hash
    }
    existing = [row for row in endpoints if isinstance(row, dict) and row.get("id") == PACKAGE]
    if existing:
        if existing != [record]:
            raise RuntimeError("conflicting endpoint registration")
    else:
        endpoints.append(record)
    data["endpoint_count"] = len(endpoints)
    data["declaration_count"] = sum(int(row["declarations"]) for row in endpoints)
    data["status"] = "PENDING_EXTERNAL_CI"
    save(path, data)


def update_goal_manifest() -> None:
    path = MATERIAL / "ci/theorem-goals.json"
    data = load(path)
    goals = data.get("goals")
    if not isinstance(goals, list):
        raise RuntimeError("theorem goals must be a list")
    goal = next((row for row in goals if row.get("id") == "SINGULAR_PREMISE_OBSTRUCT_R3"), None)
    if goal is None:
        raise RuntimeError("R3 goal missing")
    packages = goal.get("principal_packages")
    if not isinstance(packages, list):
        raise RuntimeError("R3 principal_packages must be a list")
    if PACKAGE not in packages:
        insert_at = packages.index("R3EhrenfestSmoothRepresentative") + 1
        packages.insert(insert_at, PACKAGE)
    goal["verification_scope"] = (
        "Fresh exact-type and standard-axiom audits of literal R3 Schwartz-data/finite-energy NSE-A contracts, "
        "actual sharp ball Fourier projections, the complete solenoidal bandlimited carrier, bandlimited weak-derivative "
        "foundations, actual smooth representatives, their classical/native derivative coherence and fixed-cutoff ordered "
        "derivative bounds, together with retained domain-independent scalar/commutator helpers. The NSE_A declaration is "
        "a proposition definition, not a proved obstruction or existence theorem. This stage never promotes the OPEN root."
    )
    goal["retained_foundation_scope"] = (
        "Literal target definitions and zero-datum consistency; actual real L2/H1 sharp cutoff and Leray commutation; "
        "complete fixed-point subspace with no finite-dimensional premise; concrete bandlimited gradient/Hessian construction; "
        "strong L2/H1 and compact-trajectory approximation; actual inverse-Fourier representative agreement; smooth bounded "
        "representatives; and classical coordinate derivatives identified with the native cutoff derivative operators, with "
        "finite fixed-cutoff ordered bounds. No regularized nonlinear trajectory, cutoff-uniform comparison, literal closed-slab "
        "admission, stopped-bound witness or R3 obstruction root is supplied."
    )
    save(path, data)


def update_candidate_status(source_revision: str, closure_hash: str) -> None:
    status_path = CANDIDATE / "STATUS.json"
    data = load(status_path)
    data.update({
        "status": "ACTIVATED_PENDING_MATCHING_EXTERNAL_CI",
        "registered_in_active_material": True,
        "included_in_111_named_foundations": False,
        "active_package": PACKAGE,
        "active_module": MODULE,
        "activation_source_revision": source_revision,
        "source_closure_sha256": closure_hash,
        "external_compilation_completed": False,
        "exact_type_and_axiom_acceptance": False,
        "root_proved": False,
        "stopped_witness_constructed": False,
        "activation_requirement": "Obtain matching authorized cached external compiler, exact-type and theorem-level axiom evidence for all eight names before promotion."
    })
    save(status_path, data)


def main() -> None:
    source_revision = os.environ.get("GITHUB_SHA", "")
    if len(source_revision) != 40:
        raise RuntimeError("GITHUB_SHA exact source revision required")
    if SOURCE.exists() or PACKAGE_DIR.exists():
        raise RuntimeError("active derivative package already exists; refusing a second activation")
    build = import_build_module()
    copy_candidate()
    register_owned(build, source_revision)
    write_endpoint(source_revision)
    closure, closure_hash, local_source_modules = compute_closure(build, source_revision)
    register_endpoint(closure_hash, local_source_modules)
    update_goal_manifest()
    update_candidate_status(source_revision, closure_hash)

    # Pure Python source-count refresh; this executes no Lean, Lake or kernel.
    subprocess.run(["python3", "scripts/count_lean_lines.py", "--write-readme"],
                   cwd=ROOT, check=True)

    # Exercise the repository's documented static validation only.
    subprocess.run(["python3", "Material/ci/build.py", "--validate-only"],
                   cwd=ROOT, check=True)
    print(json.dumps({
        "status": "ACTIVATED_PENDING_EXTERNAL_CI",
        "package": PACKAGE,
        "declarations": len(DECLARATIONS),
        "local_source_modules": local_source_modules,
        "source_closure_sha256": closure_hash,
        "root_proved": False,
        "local_lean_executions": 0
    }, indent=2))


if __name__ == "__main__":
    main()
