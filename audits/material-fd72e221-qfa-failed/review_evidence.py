"""Inspect retained external failure evidence only; never invoke Lean or Lake.

Usage: python3 review_evidence.py REPOSITORY_ROOT EVIDENCE_DIRECTORY
Only JSON, ZIP, gzip, text/hash inspection and immutable git-show reads occur.
"""
import collections
import gzip
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import zipfile

ROOT, OUT = map(pathlib.Path, sys.argv[1:3])
SHA = "fd72e2218553f6eb89532a4548552d42ba8476f8"
TREE = "60af2cec39b3e6e03c2fedfa331b8c9315c6b291"
RUN = 44845844062
HASHES = {
    "evidence.zip": "d1c1493a99b76e8d2372f01865f0b11afdd490397f8a6417c8d9455cdf71dd79",
    "routing-evidence.zip": "68b5597c645f86c3569a5734071df6e674fbd4569b27636603e589ec97603929",
}
NEW = ["QFAHeatSmoothing", "QFALHRestart", "QFAZeroDatum"]
checks = 0


def check(ok, description):
    global checks
    if not ok:
        raise AssertionError(description)
    checks += 1


def digest(data):
    return hashlib.sha256(data).hexdigest()


def frozen(path):
    return subprocess.check_output(["git", "show", SHA + ":" + path], cwd=ROOT)


for name, expected in HASHES.items():
    check(digest((OUT / name).read_bytes()) == expected, name + " original artifact digest")
archive = zipfile.ZipFile(OUT / "evidence.zip")
report_bytes = archive.read("current.json")
report = json.loads(report_bytes)
routing = json.loads(zipfile.ZipFile(OUT / "routing-evidence.zip").read("failure-routing.json"))
run = json.loads((OUT / "workflow-run.json").read_text())
jobs = json.loads((OUT / "workflow-jobs.json").read_text())["jobs"]
check(report["commit"] == SHA and int(report["run_id"]) == RUN, "exact external report identity")
check(report["failure_class"] == "MODULE_COMPILATION_FAILED" and report["failure_phase"] == "compile", "actual source compilation failure")
check(report["compiler_executed"] and report["source_pin_integrity"], "external compiler and source-pin integrity")
check(report["toolchain"] == "leanprover/lean4:v4.33.0", "unchanged compiler pin")
check(report["mathlib_commit"] == "db584cd6d46c92f209a44c0f1c829460d327499d", "unchanged Mathlib pin")
check(report["dependency_cache_class"] == "EXACT", "exact dependency cache")
check(report["endpoints"] == [], "independent package audits not reached")
receipts = report["module_receipts"]
counts = collections.Counter(row["status"] for row in receipts.values())
check(len(receipts) == 520, "complete module plan receipts")
check(counts == {"PASS": 514, "FAIL": 2, "BLOCKED_BY_DEPENDENCY": 4}, "exact receipt outcome counts")
check(sum(row.get("reused", False) for row in receipts.values()) == 512, "all prior accepted modules reused")
check(receipts["MethbokeAddon.QuasiFeffermanA.PhysicalRoot"]["status"] == "PASS" and not receipts["MethbokeAddon.QuasiFeffermanA.PhysicalRoot"]["reused"], "PhysicalRoot source compiled externally")
check(receipts["MethbokeAddon.QuasiFeffermanA.MomentumTranslation"]["status"] == "PASS" and not receipts["MethbokeAddon.QuasiFeffermanA.MomentumTranslation"]["reused"], "MomentumTranslation source compiled externally")
check(routing["commit"] == SHA and int(routing["run_id"]) == RUN, "exact routing identity")
check(routing["failure_class"] == "PROOF_OR_TYPE_FAILURE" and routing["recovery_allowed"] is False, "proof failure routed without recovery")
check(routing["step_outcomes"]["static"] == "success" and routing["step_outcomes"]["verify"] == "failure", "static admission passed and source verification failed")
check(routing["step_outcomes"]["final_evidence"] == "success" and routing["step_outcomes"]["publish_binary"] == "skipped", "failure evidence retained and failed binary not published")
check(run["id"] == RUN and run["head_sha"] == SHA and run["head_commit"]["tree_id"] == TREE, "exact GitHub source and tree")
check(run["status"] == "completed" and run["conclusion"] == "failure", "completed failed run")
for name in ["Fast cached verification", "Material accepted"]:
    job = next(row for row in jobs if row["name"] == name)
    check(job["status"] == "completed" and job["conclusion"] == "failure", name + " failed")
gate = (OUT / "acceptance-job.log").read_text()
check("PRIMARY_FAILURE_CLASS: PROOF_OR_TYPE_FAILURE" in gate and "PRIMARY_ACCEPTED: true" not in gate, "terminal acceptance not granted")
index = json.loads(frozen("Material/endpoints.json"))
check(index["endpoint_count"] == 102 and index["declaration_count"] == 1367, "planned audit registry counts")
packages = []
for package in NEW:
    row = next(row for row in index["endpoints"] if row["id"] == package)
    spec = json.loads(frozen("Material/" + row["manifest"]))
    declarations = spec["declarations"]
    packages.append({"id": package, "names": len(declarations), "theorems": sum(d["kind"] == "theorem" for d in declarations), "definitions_and_structures": sum(d["kind"] != "theorem" for d in declarations), "scope": spec["scope"]})
check(sum(row["names"] for row in packages) == 73 and sum(row["theorems"] for row in packages) == 53, "73 planned new names including 53 theorems")
logs = []
for name in archive.namelist():
    if not name.startswith("logs/modules/"):
        continue
    raw = archive.read(name)
    retained = name.rsplit("/", 1)[-1] + ".gz"
    check(gzip.decompress((OUT / retained).read_bytes()) == raw, retained + " exact decompressed bytes")
    text = raw.decode()
    logs.append({"archive_path": name, "retained_log": retained, "raw_sha256": digest(raw), "raw_bytes": len(raw), "diagnostic_headers": re.findall(r"^.*?:\d+:\d+: (?:error(?:\([^\n]*?\))?|warning):.*$", text, re.M)})
sources = {}
for module, row in receipts.items():
    if row.get("reused", False):
        continue
    path = "Material/" + module.replace(".", "/") + ".lean"
    sources[path] = digest(frozen(path))
summary = {
    "schema_version": 1,
    "status": "CHECKED_MATCHING_EXTERNAL_SOURCE_FAILURE",
    "review_kind": "nonexecuting_text_json_hash_review",
    "tested_commit": SHA, "tree": TREE, "run_id": RUN, "run_url": run["html_url"],
    "compiler": report["compiler"], "mathlib_commit": report["mathlib_commit"],
    "artifact_sha256": HASHES, "report_sha256": digest(report_bytes),
    "checks_passed": checks, "local_lean_executions": 0,
    "module_count": 520, "module_status_counts": dict(counts),
    "reused_passing_modules": 512, "fresh_passing_modules": 2,
    "planned_packages": 102, "planned_named_reports": 1367,
    "fresh_package_audits_completed": 0, "new_names_accepted": 0,
    "new_packages": packages,
    "failure_class": report["failure_class"], "routing_failure_class": routing["failure_class"],
    "failed_modules": [module for module, row in receipts.items() if row["status"] == "FAIL"],
    "blocked_modules": [module for module, row in receipts.items() if row["status"] == "BLOCKED_BY_DEPENDENCY"],
    "candidate_source_sha256": sources, "compiler_logs": logs,
    "scope_limit": "PhysicalRoot and MomentumTranslation compiled, but no new independent package audit completed. This run grants no new A-tier acceptance; the earlier d403c235 acceptance remains the accepted baseline."
}
(OUT / "independent-review.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({key: summary[key] for key in ["status", "checks_passed", "module_status_counts", "new_names_accepted", "failed_modules", "blocked_modules"]}, indent=2))
