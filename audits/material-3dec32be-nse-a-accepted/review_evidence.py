"""Read externally produced JSON/logs/source hashes only. Never invoke Lean.

Usage: python3 review_nse_a_evidence.py REPO EVIDENCE_DIR SHA RUN_ID ZIP_SHA256
The evidence directory must contain evidence.zip, routing-evidence.zip,
acceptance-job.log and the matching workflow/artifact API metadata.
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

ROOT = pathlib.Path(sys.argv[1])
OUT = pathlib.Path(sys.argv[2])
SHA, RUN, ZIP_SHA = sys.argv[3:6]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NEW = ["QFAPhysicalH1", "QFAACBudget", "QFASixChargeBudget", "QFAH1Fourier",
       "QFAH1FourierReverse", "QFAPhysicalH1Budget", "QFASixSectors",
       "QFAEnstrophyCoefficient", "QFASixSectorL2"]
checks = 0


def check(ok, detail):
    global checks
    if not ok:
        raise AssertionError(detail)
    checks += 1


def digest(data):
    return hashlib.sha256(data).hexdigest()


def frozen(path):
    return subprocess.check_output(["git", "show", SHA + ":" + str(path)], cwd=ROOT)


def read_frozen_json(path):
    return json.loads(frozen(path))


archive_bytes = (OUT / "evidence.zip").read_bytes()
check(digest(archive_bytes) == ZIP_SHA, "exact GitHub artifact digest")
archive = zipfile.ZipFile(OUT / "evidence.zip")
report_bytes = archive.read("current.json")
report = json.loads(report_bytes)
check(report["commit"] == SHA and str(report["run_id"]) == RUN, "exact run identity")
check(report["status"] == "PASS", "complete external verification PASS")
check(report["all_endpoints_selected"] and report["fresh_required_audits"], "full fresh scope")
check(report["toolchain"] == "leanprover/lean4:v4.33.0", "compiler pin")
check(report["mathlib_commit"] == "db584cd6d46c92f209a44c0f1c829460d327499d", "Mathlib pin")
check(report["source_pin_integrity"], "source-pin integrity")
check(all(d["tracked_source_clean"] for d in report["verified_dependencies"]), "clean dependencies")
check(report["platform"] == {"machine": "x86_64", "system": "Linux"}, "external platform")
receipts = report["module_receipts"]
check(len(receipts) == 481 and all(r["status"] == "PASS" for r in receipts.values()), "481 PASS modules")
check(report["metrics"]["audit_fresh_count"] == 86, "86 fresh package audits")
check(report["metrics"]["audit_reused_count"] == 0, "no reused package audits")
index = read_frozen_json("Material/endpoints.json")
check(index["endpoint_count"] == 86 and index["declaration_count"] == 853, "exact registry counts")
specs = [read_frozen_json("Material/" + row["manifest"]) for row in index["endpoints"]]
actual = {e["id"]: e for e in report["endpoints"]}
check(len(actual) == len(report["endpoints"]) == len(specs) == 86, "unique package count")
check(set(actual) == {s["id"] for s in specs}, "exact package coverage")
all_names, package_rows, new_names = [], [], []
new_reports = []

for spec in specs:
    package = spec["id"]
    entry = actual[package]
    names = [d["name"] for d in spec["declarations"]]
    all_names += names
    check(entry["status"] == "PASS" and entry["source_drift"] == [], package + " status/source")
    check(set(spec["allowed_axioms"]) == STANDARD, package + " policy")
    check(entry["audit_origin_commit"] == SHA and entry["audit_reused"] is False, package + " freshness")
    check(entry["declaration_count"] == len(names) == len(set(names)), package + " declaration count")
    check(set(entry["types"]) == set(names) == set(entry["axioms"]), package + " named coverage")
    log_bytes = archive.read(entry["audit_log"].removeprefix("registry/"))
    check(digest(log_bytes) == entry["audit_sha256"], package + " raw log hash")
    log = log_bytes.decode()
    check(not re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror(?:\([^\n)]*\))?\s*:", log, re.I), package + " errors/admissions")
    sentinels = re.findall(r"^(TYPE_BEGIN|TYPE_END|AXIOMS_BEGIN|AXIOMS_END):(.*)$", log, re.M)
    expected = [(tag, name) for name in names for tag in ["TYPE_BEGIN", "TYPE_END", "AXIOMS_BEGIN", "AXIOMS_END"]]
    check(sentinels == expected, package + " ordered unique sentinels")
    for name in names:
        match = re.search(r"^TYPE_BEGIN:" + re.escape(name) + r"\n(.*?)\nTYPE_END:" + re.escape(name) + "$", log, re.M | re.S)
        check(match is not None, name + " type block")
        check(" ".join(match.group(1).split()) == " ".join(entry["types"][name].split()), name + " exact type report")
        body = re.search(r"^AXIOMS_BEGIN:" + re.escape(name) + r"\n(.*?)\nAXIOMS_END:" + re.escape(name) + "$", log, re.M | re.S).group(1).strip()
        match = re.fullmatch("'" + re.escape(name) + r"'\s+depends on axioms:\s*\[([^\]]*)\]", body, re.S)
        if match:
            axioms = {re.sub(r"\.\{[^}]*\}", "", a.strip()) for a in match.group(1).split(",") if a.strip()}
        else:
            check(re.fullmatch("'" + re.escape(name) + r"'\s+does not depend on any axioms\.?", body) is not None, name + " axiom grammar")
            axioms = set()
        check(axioms <= STANDARD and axioms == set(entry["axioms"][name]), name + " exact standard-only axioms")
        if package in NEW:
            declaration = next(d for d in spec["declarations"] if d["name"] == name)
            new_reports.append({"package": package, "name": name, "kind": declaration["kind"], "type": entry["types"][name], "axioms": sorted(axioms)})
    row = {"id": package, "declarations": len(names), "audit_sha256": entry["audit_sha256"]}
    if package in NEW:
        new_names += names
        audit_path = "Material/" + package + "/Audit.lean"
        audit_bytes = frozen(audit_path)
        check(audit_bytes == (ROOT / audit_path).read_bytes(), package + " unchanged local audit bytes")
        consumers = len(re.findall(r"^example\b", audit_bytes.decode(), re.M))
        check(consumers >= len(names), package + " full independent consumer coverage")
        check(re.findall(r"^#check @(\S+)", audit_bytes.decode(), re.M) == names, package + " audit name order")
        roots = []
        for source in spec["source_roots"]:
            path = "Material/" + source["path"]
            data = frozen(path)
            check(data == (ROOT / path).read_bytes(), package + " unchanged source bytes")
            roots.append({"path": path, "sha256": digest(data)})
        row.update({"scope": spec["scope"], "source_roots": roots, "audit_source_sha256": digest(audit_bytes), "consumer_examples": consumers,
                    "theorems": sum(d["kind"] == "theorem" for d in spec["declarations"]),
                    "definitions_and_instances": sum(d["kind"] != "theorem" for d in spec["declarations"])})
    package_rows.append(row)

check(len(all_names) == 853, "853 named type/axiom reports")
check(len(new_names) == len(set(new_names)) == 155, "155 unique new names")
check(sum(x["kind"] == "theorem" for x in new_reports) == 126, "126 new theorem declarations")
check(sum(x["kind"] != "theorem" for x in new_reports) == 29, "29 new definitions/instances")
cutout = report["cutout"]
check(cutout["status"] == "PASS" and cutout["audit_origin_commit"] == SHA and cutout["audit_reused"] is False, "fresh standalone QFB cutout")
check(digest(archive.read(cutout["audit_log"].removeprefix("registry/"))) == cutout["audit_sha256"], "QFB raw log identity")
check(all(set(a) <= STANDARD for a in cutout["axioms"].values()), "QFB standard-only audit")
accepted = (OUT / "acceptance-job.log").read_text()
check("PRIMARY_ACCEPTED: true" in accepted and "PRIMARY_RESULT: success" in accepted and "PRIMARY_FAILURE_CLASS: NONE" in accepted, "terminal acceptance gate context")
artifacts = json.loads((OUT / "artifact-metadata.json").read_text())["artifacts"]
routing_meta = next(a for a in artifacts if a["name"].startswith("material-routing-" + SHA + "-" + RUN))
routing_bytes = (OUT / "routing-evidence.zip").read_bytes()
check("sha256:" + digest(routing_bytes) == routing_meta["digest"], "original routing artifact digest")
routing = json.loads(zipfile.ZipFile(OUT / "routing-evidence.zip").read("failure-routing.json"))
check(routing["commit"] == SHA and str(routing["run_id"]) == RUN, "exact routing identity")
check(routing["backend"] == "binary_cache" and routing["failure_class"] == "NONE" and routing["failed_step"] is None, "successful cached worker routing")
for action in ["static", "verify", "verified_evidence", "binary_package", "save_project", "published_dependencies", "published_project", "published_identities", "publish_binary", "final_evidence"]:
    check(routing["step_outcomes"][action] == "success", action + " external step success")
run_record = json.loads((OUT / "workflow-run.json").read_text())
check(run_record["head_sha"] == SHA and str(run_record["id"]) == RUN and run_record["status"] == "completed" and run_record["conclusion"] == "success", "GitHub completed successful run")
jobs = json.loads((OUT / "workflow-jobs.json").read_text())["jobs"]
for job_name in ["Fast cached verification", "Material accepted"]:
    job = next(j for j in jobs if j["name"] == job_name)
    check(job["status"] == "completed" and job["conclusion"] == "success", job_name + " successful job")
for prefix in ["material-binary-", "material-verified-", "material-evidence-"]:
    artifact = next(a for a in artifacts if a["name"].startswith(prefix + SHA + "-" + RUN))
    check(not artifact["expired"] and artifact["size_in_bytes"] > 0 and artifact["workflow_run"]["head_sha"] == SHA, prefix + " published artifact")
binary_entry = json.loads(archive.read("binary-entry.json"))
check(binary_entry["commit"] == SHA and str(binary_entry["run_id"]) == RUN and binary_entry["module_count"] == 481, "published binary preparation identity")
policy = [".github", "Material/ci", "Material/lean-toolchain", "Material/lakefile.lean", "Material/lake-manifest.json", "Material/_vendor/source-manifest.json"]
changed = subprocess.check_output(["git", "diff", "--name-only", "cb3bafdc71c7eb10e57996af6111ba6c24f6865c", SHA, "--", *policy], cwd=ROOT).decode().strip()
check(not changed, "unchanged compiler/dependency/CI/audit policy")
summary = {"schema_version": 1, "status": "CHECKED_MATCHING_EXTERNAL_ACCEPTANCE", "review_kind": "nonexecuting_text_json_hash_review",
           "tested_commit": SHA, "run_id": int(RUN), "run_url": report["run_url"], "artifact_sha256": ZIP_SHA,
           "artifact_bytes": len(archive_bytes), "report_sha256": digest(report_bytes), "checks_passed": checks,
           "module_count": len(receipts), "package_count": 86, "named_reports": len(all_names), "all_package_audits_fresh": True,
           "new_packages": 9, "new_named_declarations": 155, "new_theorems": 126, "new_definitions_and_instances": 29,
           "allowed_axioms": sorted(STANDARD), "compiler": report["compiler"], "toolchain": report["toolchain"],
           "mathlib_commit": report["mathlib_commit"], "metrics": report["metrics"], "total_seconds": report["total_seconds"],
           "dependency_cache_class": report["dependency_cache_class"], "project_cache_class": report["project_cache_class"],
           "final_acceptance_gate": True, "publication_pass": True, "qfb_cutout_pass": True,
           "publication_evidence": "Original structured routing artifact, matching GitHub artifact/run/job metadata and terminal acceptance-job log.",
           "routing_artifact_sha256": digest(routing_bytes),
           "full_worker_console_log_retrieval": "Connector returned Transport closed twice; unauthenticated fallback returned HTTP403. Full compiler/type/axiom logs remain in evidence.zip; exact publication step outcomes remain in routing-evidence.zip.",
           "local_lean_executions": 0, "parent_targets_closed": 0, "physical_qfa_root_proved": False,
           "universal_budget_finiteness_proved": False, "packages": package_rows,
           "scope_limits": ["Acceptance is for the exact nine scoped helper packages; G01--G06 remain open.",
                            "Supplied-gradient Fourier equivalence does not construct arbitrary weighted gradient witnesses.",
                            "Complex L2 projectors do not yet establish the real physical H1/solenoidal lift.",
                            "Scalar and physical-observable budget helpers retain their explicit PDE/path hypotheses.",
                            "Independent B-tier analytical chains are not native Lean verification."]}
(OUT / "independent-review.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
new_report_bytes = (json.dumps(new_reports, indent=2, ensure_ascii=False) + "\n").encode()
(OUT / "new-declaration-evidence.json.gz").write_bytes(gzip.compress(new_report_bytes, mtime=0))
(OUT / "new-declaration-index.json").write_text(json.dumps([
    {"package": row["package"], "name": row["name"], "kind": row["kind"],
     "type_sha256": digest(row["type"].encode()), "axioms": row["axioms"]}
    for row in new_reports], indent=2, ensure_ascii=False) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k not in ["packages", "metrics"]}, indent=2, ensure_ascii=False))
