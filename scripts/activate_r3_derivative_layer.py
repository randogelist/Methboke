#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
TESTED = "dc265b9489dac0504c660255d0a3da02c4e0f484"
RUN_ID = 44880439634
RUN_URL = f"https://github.com/randogelist/Methboke/actions/runs/{RUN_ID}"
MAT_ARTIFACT_ID = 14698327135
GOAL_ARTIFACT_ID = 14697488691
MAT_SHA = "1998d7708c7ead496d2fad9281715cc52ad84be9a4198b74656350126bfb985e"
GOAL_SHA = "87a1e56eb7d86a854af7d0e38ab27a5f250b35ceed21c7b9edaf4ac5ebd0f8e8"
PKG = "R3EhrenfestDerivativeRepresentative"
AUDIT_SHA = "3ec2df80c5169c8372b6d5a736386cdf85d659ce8b80f675915b61132dfc2e80"
DECLS = [
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative",
    "MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound",
]
SCOPE = (
    "Classical coordinate derivatives of the actual smooth sharp-cutoff representative "
    "coincide with the already constructed native Fourier derivative operators. Ordered "
    "coordinate words equal cutoffWordCLM and satisfy finite fixed-cutoff Bernstein bounds. "
    "No nonlinear flow, cutoff-uniform comparison, literal NSE-A Sobolev admission, "
    "stopped-bound witness or obstruction root is asserted."
)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def save(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def replace_required(text: str, old: str, new: str, label: str) -> str:
    if old not in text:
        raise RuntimeError(f"missing replacement anchor {label}: {old!r}")
    return text.replace(old, new)


def extract_json(zip_path: Path, member: str):
    with zipfile.ZipFile(zip_path) as z:
        names = z.namelist()
        candidate = member if member in names else next((n for n in names if n.endswith('/' + member)), None)
        if candidate is None:
            raise RuntimeError(f"{member} missing from {zip_path}")
        return json.loads(z.read(candidate).decode("utf-8"))


def validate_artifacts(mat_zip: Path, goal_zip: Path):
    if sha256(mat_zip) != MAT_SHA:
        raise RuntimeError("material artifact digest mismatch")
    if sha256(goal_zip) != GOAL_SHA:
        raise RuntimeError("goal artifact digest mismatch")
    current = extract_json(mat_zip, "current.json")
    scope = extract_json(goal_zip, "scope-report.json")
    assert current["status"] == "PASS" and current["commit"] == TESTED
    assert scope["audit_status"] == "PASS" and scope["source_revision"] == TESTED
    assert scope["root_status"] == "OPEN_NO_NATIVE_ROOT" and scope["root_declaration"] is None
    endpoint = next(e for e in current["endpoints"] if e["id"] == PKG)
    assert endpoint["status"] == "PASS" and endpoint["declaration_count"] == 8
    assert endpoint["audit_sha256"] == AUDIT_SHA
    assert set(endpoint["axioms"]) == set(DECLS)
    for name in DECLS:
        assert endpoint["axioms"][name] == ["Classical.choice", "Quot.sound", "propext"]
    assert PKG in scope["selected_packages"]
    assert current["metrics"]["module_count"] == 670
    assert current["metrics"]["audit_fresh_count"] == 177
    assert sum(e["declaration_count"] for e in current["endpoints"]) == 2331
    assert scope["fresh_package_count"] == 26 and scope["fresh_named_reports"] == 497
    return current, scope, endpoint


def write_evidence(mat_zip: Path, goal_zip: Path, current, scope, endpoint) -> Path:
    out = ROOT / "audits/r3-ehrenfest-dc265b94-accepted"
    out.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(mat_zip, out / "material-evidence.zip")
    shutil.copyfile(goal_zip, out / "r3-goal-evidence.zip")
    summary = {
        "schema_version": 1,
        "repository": "randogelist/Methboke",
        "branch": "codex/nse-a-r3-ehrenfest",
        "tested_commit": TESTED,
        "run_id": RUN_ID,
        "run_url": RUN_URL,
        "status": "A_TIER_MATCHING_EXTERNAL_ACCEPTED_EXACT_SCOPE",
        "accepted": True,
        "accepted_mid_tier": "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE",
        "package": PKG,
        "new_declarations": 8,
        "cumulative_r3_foundation_declarations": 119,
        "cumulative_r3_foundation_packages": 8,
        "scope": SCOPE,
        "compiler": current["compiler"],
        "toolchain": current["toolchain"],
        "mathlib_commit": current["mathlib_commit"],
        "module_count": current["metrics"]["module_count"],
        "fresh_modules": current["metrics"]["fresh_module_count"],
        "reused_modules": current["metrics"]["reused_module_count"],
        "fresh_package_audits": current["metrics"]["audit_fresh_count"],
        "named_type_axiom_reports": sum(e["declaration_count"] for e in current["endpoints"]),
        "fresh_qfb_cutout": current["cutout"]["status"] == "PASS",
        "package_audit_sha256": endpoint["audit_sha256"],
        "standard_axioms_only": True,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "scoped_r3_replay": {
            "status": scope["audit_status"],
            "fresh_packages": scope["fresh_package_count"],
            "fresh_named_reports": scope["fresh_named_reports"],
            "verified_cached_modules": scope["cache_admission"]["verified_module_count"],
            "dependency_cache_class": scope["cache_admission"]["dependency_cache_class"],
            "project_cache_class": scope["cache_admission"]["project_cache_class"],
            "root_status": scope["root_status"],
            "root_declaration": scope["root_declaration"],
        },
        "artifacts": {
            "material": {"id": MAT_ARTIFACT_ID, "sha256": MAT_SHA, "path": "material-evidence.zip"},
            "r3_goal": {"id": GOAL_ARTIFACT_ID, "sha256": GOAL_SHA, "path": "r3-goal-evidence.zip"},
        },
        "declarations": DECLS,
        "root_proved": False,
        "stopped_witness_constructed": False,
        "local_lean_executions": 0,
        "open_obligations": scope["open_obligations"],
    }
    save(out / "summary.json", summary)
    (out / "README.txt").write_text(
        "R3 DERIVATIVE-REPRESENTATIVE COHERENCE — SOURCE-SPECIFIC ACCEPTANCE\n\n"
        f"Tested source: {TESTED}\nExternal run: {RUN_ID}\n\n"
        "All eight declarations passed matching cached external compilation, independent exact-type consumers, "
        "fresh theorem-level axiom reports, publication, the full Material acceptance gate and the scoped R3 replay. "
        "Only propext, Classical.choice and Quot.sound occur.\n\n"
        "The accepted scope identifies the classical coordinate derivatives of the actual smooth sharp-cutoff "
        "representative with the native Fourier derivative operators and proves finite fixed-cutoff bounds for ordered "
        "coordinate words. The nonlinear regularized flow, cutoff-uniform comparison, literal closed-slab admission, "
        "conditional obstruction root and stopped-bound witness remain open.\n",
        encoding="utf-8",
    )
    return out


def update_implementation_status(summary):
    path = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/IMPLEMENTATION_STATUS.json"
    data = load(path)
    data["candidate_status"] = "119_NAMED_FOUNDATIONS_ACCEPTED_ROOT_OPEN"
    data["accepted_new_declarations"] = 119
    data["accepted_foundation_packages"] = 8
    data["latest_mid_tier_acceptance"] = {
        "id": "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE",
        "status": "A_TIER_MATCHING_EXTERNAL_ACCEPTED_EXACT_SCOPE",
        "tested_commit": TESTED,
        "run_id": RUN_ID,
        "evidence": "audits/r3-ehrenfest-dc265b94-accepted/summary.json",
        "package": PKG,
        "declarations": 8,
        "audit_sha256": AUDIT_SHA,
        "root_proved": False,
    }
    scopes = data.setdefault("accepted_new_scopes", [])
    if not any(s.get("package") == PKG for s in scopes):
        scopes.append({
            "package": PKG,
            "declarations": 8,
            "scope": SCOPE,
            "status": "ACCEPTED_MATCHING_EXTERNAL_CACHED_VERIFICATION",
            "tested_commit": TESTED,
            "run_id": RUN_ID,
            "audit_sha256": AUDIT_SHA,
            "root_proved": False,
        })
    save(path, data)


def update_candidate_status():
    path = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NEXT_LAYER_CANDIDATE/STATUS.json"
    data = load(path)
    data.update({
        "status": "A_TIER_MATCHING_EXTERNAL_ACCEPTED_EXACT_SCOPE",
        "registered_in_active_material": True,
        "included_in_119_named_foundations": True,
        "accepted_mid_tier": "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE",
        "tested_commit": TESTED,
        "run_id": RUN_ID,
        "evidence": "audits/r3-ehrenfest-dc265b94-accepted/summary.json",
        "external_compilation_completed": True,
        "exact_type_and_axiom_acceptance": True,
        "package_audit_sha256": AUDIT_SHA,
        "root_proved": False,
        "stopped_witness_constructed": False,
        "next_endpoint": "R3_FIXED_CUTOFF_NONLINEAR_CONVECTION",
    })
    save(path, data)


def update_native_progress():
    path = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/NSE_A_EHRENFEST_NATIVE_PROGRESS.txt"
    text = path.read_text(encoding="utf-8")
    text = re.sub(r"Version 0\.3 — 21 November 2026", "Version 0.4 — 21 November 2026", text, count=1)
    text = re.sub(r"STATUS: 111 NAMED FOUNDATIONS ACCEPTED; LITERAL ROOT OPEN", "STATUS: 119 NAMED FOUNDATIONS ACCEPTED; LITERAL ROOT OPEN", text, count=1)
    text = re.sub(r"TESTED SOURCE: 1d4a9324f2cfb576f8a389da0e354da29ef7dbde", f"TESTED SOURCE: {TESTED}", text, count=1)
    text = re.sub(r"EXTERNAL RUN: 44875907550", f"EXTERNAL RUN: {RUN_ID}", text, count=1)
    marker = "CURRENT R3 FOUNDATION ACCEPTANCE — LITERAL ROOT REMAINS OPEN\n\n"
    start = text.index(marker) + len(marker)
    end = text.index("\nEXACT ACCEPTED DECLARATIONS\n")
    new_intro = (
        f"Source {TESTED}; Material run {RUN_ID}.\n"
        "All 670 modules passed (668 compatible reuses, 2 fresh compilations).\n"
        "All 177 package audits were fresh: 2,331 named reports plus fresh QFB.\n"
        "Eight R3 packages /119 declarations are accepted, with only the standard\n"
        "axioms propext, Classical.choice and Quot.sound. The scoped R3 replay\n"
        "passed 26 fresh package audits /497 named reports from 71 cached modules.\n"
        "The newly accepted eight-name layer proves derivative-representative\n"
        "coherence and finite fixed-cutoff ordered derivative bounds.\n"
        "Receipt: audits/r3-ehrenfest-dc265b94-accepted/summary.json.\n"
        "The native R3 root remains OPEN_NO_NATIVE_ROOT; canonical nonlinear flow,\n"
        "cutoff-uniform stability and literal closed-slab Sobolev admission remain\n"
        "unproved. No stopped-bound witness is constructed.\n"
    )
    text = text[:start] + new_intro + text[end:]
    package_block = (
        "\nR3EhrenfestDerivativeRepresentative — 8 declarations\n"
        "Classical/native derivative coherence for the actual smooth cutoff representative and finite fixed-cutoff ordered derivative bounds.\n"
        f"Audit SHA256: {AUDIT_SHA}\n" +
        "".join(f"  {name}\n" for name in DECLS) + "\n"
    )
    total_marker = "TOTAL: 111 new named declarations in seven independently audited packages."
    if PKG not in text:
        text = replace_required(text, total_marker, package_block + "TOTAL: 119 new named declarations in eight independently audited packages.", "progress total")
    else:
        text = text.replace(total_marker, "TOTAL: 119 new named declarations in eight independently audited packages.")
    text = text.replace("Canonical full gate: 668 modules, 176 fresh package audits, 2,323 names + QFB.",
                        "Canonical full gate: 670 modules, 177 fresh package audits, 2,331 names + QFB.")
    text = text.replace("R3 scoped gate: 69 cached modules, 25 fresh package audits, 489 names.",
                        "R3 scoped gate: 71 cached modules, 26 fresh package audits, 497 names.")
    next_idx = text.find("NEXT PREPARED LAYER")
    if next_idx >= 0:
        text = text[:next_idx] + (
            "NEXT TARGET\n"
            "R3_FIXED_CUTOFF_NONLINEAR_CONVECTION: construct the actual fixed-cutoff\n"
            "bilinear convection map on the complete carrier, prove its L2 bound,\n"
            "project it back into the carrier, and derive the diagonal ballwise\n"
            "Lipschitz estimate needed by the Banach-space Picard theorem.\n"
            "This target remains unverified until matching external evidence exists.\n"
        )
    path.write_text(text, encoding="utf-8")


def update_obstruction_readme():
    path = ROOT / "R3_NSE/A-Heisenberg-Obstruction/StoppedCommutatorBound/README.md"
    text = path.read_text(encoding="utf-8")
    marker = "## Retained preparation and failed-run history"
    pos = text.index(marker)
    head = (
        "# R3 stopped-commutator construction — accepted foundations, open root\n\n"
        "CURRENT R3 FOUNDATION ACCEPTANCE — LITERAL ROOT REMAINS OPEN\n\n"
        f"Source `{TESTED}`; [Material run {RUN_ID}]({RUN_URL}).\n"
        "All 670 modules passed (668 compatible reuses, two fresh compilations).\n"
        "All 177 package audits were fresh: 2,331 named reports plus fresh QFB.\n"
        "Eight R3 packages /119 declarations are accepted, with only `propext`,\n"
        "`Classical.choice` and `Quot.sound`. The scoped R3 replay passed 26 fresh\n"
        "package audits /497 named reports from 71 cached modules.\n\n"
        "The new `R3EhrenfestDerivativeRepresentative` package identifies classical\n"
        "coordinate derivatives of the actual smooth cutoff representative with the\n"
        "native Fourier derivative operators and proves finite fixed-cutoff ordered\n"
        "derivative bounds. [Exact evidence](../../../audits/r3-ehrenfest-dc265b94-accepted/summary.json).\n\n"
        "The native R3 root remains `OPEN_NO_NATIVE_ROOT`; the actual canonical flow,\n"
        "cutoff-uniform stability, literal closed-slab Sobolev admission and the\n"
        "stopped-bound witness remain open.\n\n"
    )
    text = head + text[pos:]
    row = "| I03 derivative coherence | DerivativeRepresentative | Classical/native derivative identity for the actual smooth cutoff representative and fixed-cutoff ordered bounds |\n"
    table_anchor = "| I03 derivatives | Bandlimited | New real weak derivative witnesses and physical H2 admission; exact delivered scope in the endpoint manifest |\n"
    if row not in text:
        text = replace_required(text, table_anchor, table_anchor + row, "README table")
    text = text.replace(
        "All modules are under Material/MethbokeAddon/R3Ehrenfest/. New statements\nremain candidates until matching external compilation and complete exact\ntype/axiom audits pass. A foundation-stage success does not establish the root.",
        "All active modules are under `Material/MethbokeAddon/R3Ehrenfest/`. The eight\npackages listed above have matching external compilation and complete exact\ntype/axiom evidence. A foundation-stage success does not establish the root."
    )
    path.write_text(text, encoding="utf-8")


def update_top_readme():
    path = ROOT / "README.md"
    text = path.read_text(encoding="utf-8")
    text = text.replace("OPEN; 111 named foundations accepted", "OPEN; 119 named foundations accepted")
    text = text.replace("Seven packages accepted at 1d4a9324/run44875907550; canonical flow, stability, literal admission and conditional root remain open",
                        "Eight packages /119 declarations accepted through dc265b94/run44880439634; canonical flow, stability, literal admission and conditional root remain open")
    text = text.replace("The first seven foundation packages are [externally accepted](audits/r3-ehrenfest-1d4a9324-accepted/summary.json)\nat source `1d4a9324`: 111 new declarations, full Material acceptance and the\nR3 goal audit passed. All 2,212 retained declaration identities are unchanged.",
                        "Eight foundation packages /119 declarations are externally accepted. The original seven-package batch remains pinned at [1d4a9324](audits/r3-ehrenfest-1d4a9324-accepted/summary.json); the derivative-coherence extension is accepted at [dc265b94](audits/r3-ehrenfest-dc265b94-accepted/summary.json), run 44880439634. The literal root remains open.")
    path.write_text(text, encoding="utf-8")


def update_misc_docs(summary):
    gpt = ROOT / "GPT.txt"
    text = gpt.read_text(encoding="utf-8")
    tag = "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE"
    if tag not in text:
        text += (
            "\n\nR3 EHRENFEST CURRENT ACCEPTANCE (2026-11-21)\n"
            f"- !=! {tag}: A-tier at {TESTED}, run {RUN_ID}.\n"
            "- Eight declarations identify classical derivatives of the actual smooth sharp-cutoff representative with native Fourier derivative operators and prove finite fixed-cutoff ordered derivative bounds.\n"
            "- Cumulative R3 foundations: 8 packages /119 declarations. Literal obstruction root and stopped-bound witness remain open.\n"
            "- Evidence: audits/r3-ehrenfest-dc265b94-accepted/summary.json.\n"
        )
        gpt.write_text(text, encoding="utf-8")

    idx = ROOT / "INDEX-WORTHY.txt"
    text = idx.read_text(encoding="utf-8")
    if tag not in text:
        text += (
            f"\n{tag} — !! A-tier exact mid-tier endpoint. At `{TESTED}` / run `{RUN_ID}`, classical coordinate derivatives of the actual R3 sharp-cutoff representative are identified with the native Fourier derivative operators; ordered derivative words have finite fixed-cutoff Bernstein bounds. This is not the nonlinear flow or obstruction root. Evidence: `audits/r3-ehrenfest-dc265b94-accepted/summary.json`.\n"
        )
        idx.write_text(text, encoding="utf-8")

    r3 = ROOT / "R3_NSE/README.md"
    text = r3.read_text(encoding="utf-8")
    note = (f"\n## R3 Ehrenfest derivative coherence\n\nThe eighth R3 foundation package is A-tier accepted at `{TESTED}`, run `{RUN_ID}`. It adds eight classical/native derivative-coherence declarations, bringing the branch foundation total to 119 declarations. The nonlinear flow and literal obstruction root remain open.\n")
    if "## R3 Ehrenfest derivative coherence" not in text:
        text += note
        r3.write_text(text, encoding="utf-8")

    source_status = ROOT / "SOURCE_STATUS.json"
    data = load(source_status)
    data["r3_ehrenfest_current_acceptance"] = {
        "status": "119_NAMED_FOUNDATIONS_ACCEPTED_ROOT_OPEN",
        "tested_commit": TESTED,
        "run_id": RUN_ID,
        "evidence": "audits/r3-ehrenfest-dc265b94-accepted/summary.json",
        "latest_mid_tier": "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE",
        "root_proved": False,
        "stopped_witness_constructed": False,
    }
    save(source_status, data)


def cleanup_and_count():
    for rel in [
        ".github/workflows/activate-r3-derivative-layer.yml",
        "scripts/activate_r3_derivative_layer.py",
    ]:
        p = ROOT / rel
        if p.exists():
            p.unlink()
    subprocess.run(["python3", "scripts/count_lean_lines.py", "--write-readme"], cwd=ROOT, check=True)


def main():
    mat_zip = Path(os.environ.get("MATERIAL_EVIDENCE_ZIP", "/tmp/material-evidence.zip"))
    goal_zip = Path(os.environ.get("R3_GOAL_EVIDENCE_ZIP", "/tmp/r3-goal-evidence.zip"))
    current, scope, endpoint = validate_artifacts(mat_zip, goal_zip)
    out = write_evidence(mat_zip, goal_zip, current, scope, endpoint)
    summary = load(out / "summary.json")
    update_implementation_status(summary)
    update_candidate_status()
    update_native_progress()
    update_obstruction_readme()
    update_top_readme()
    update_misc_docs(summary)
    cleanup_and_count()
    print(json.dumps({
        "status": "FROZEN_ACCEPTED_MID_TIER",
        "mid_tier": "R3_DERIVATIVE_REPRESENTATIVE_COHERENCE",
        "tested_commit": TESTED,
        "run_id": RUN_ID,
        "cumulative_foundation_declarations": 119,
        "root_proved": False,
        "local_lean_executions": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
