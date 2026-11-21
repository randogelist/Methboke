"""Independent nonexecuting review of actual L2 Duhamel response, forcing operator and spatial energy.

No Lean, Lake, kernel, repository script, or compiler is executed. This program
only reads immutable Git objects and external ZIP/JSON/text evidence, computes
hashes, and writes only retained evidence/review files in EVIDENCE_DIRECTORY.
No repository proof, manifest, closure, policy or status file is edited.
Usage: python3 qfa_forced_heat_review_evidence.py REPOSITORY EVIDENCE_DIRECTORY SHA RUN_ID TREE
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

if len(sys.argv) != 6:
    raise SystemExit("Usage: qfa_forced_heat_review_evidence.py REPOSITORY EVIDENCE_DIRECTORY SHA RUN_ID TREE")
REPO, OUT = map(pathlib.Path, sys.argv[1:3])
SHA, RUN, TREE = sys.argv[3:6]
if not re.fullmatch(r"[0-9a-f]{40}", SHA) or not re.fullmatch(r"[0-9a-f]{40}", TREE) or not RUN.isdecimal():
    raise ValueError("Exact source SHA, numeric run ID and exact Git tree are required")
POLICY_BASE = "809aadc6da1eeabd5c128eb9c78005a38d3d4935"
NEW = {"QFAHeatDuhamel": 15, "QFAHeatDuhamelOperator": 5, "QFAHeatSpatialEnergy": 4}
NEW_DEFINITIONS = {"QFAHeatDuhamel": 1, "QFAHeatDuhamelOperator": 1, "QFAHeatSpatialEnergy": 0}
NEW_CONSUMERS = {"QFAHeatDuhamel": 17, "QFAHeatDuhamelOperator": 7, "QFAHeatSpatialEnergy": 5}
NEW_SOURCE_MODULES = {
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamel",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator",
    "MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy",
}
NEW_NAMES = {
    "QFAHeatDuhamel": [
        "heatL2_joint_continuous", "duhamelL2", "duhamelL2_integrand_aestronglyMeasurable",
        "duhamelL2_integrand_memLp_two", "duhamelL2_integrand_intervalIntegrable",
        "duhamelL2_zero_time", "duhamelL2_zero_forcing", "duhamelL2_ae_eq", "duhamelL2_add",
        "duhamelL2_smul", "duhamelL2_norm_le_integral_norm", "duhamelL2_norm_le_sqrt_mul",
        "duhamelL2_norm_le_sqrt_horizon", "duhamelL2_norm_le_sqrt_mul_lpNorm", "duhamelL2_continuousOn",
    ],
    "QFAHeatDuhamelOperator": [
        "duhamelL2Operator", "duhamelL2Operator_apply", "duhamelL2Operator_norm_le",
        "duhamelL2Operator_zero_trace", "duhamelL2Operator_toLp_apply",
    ],
    "QFAHeatSpatialEnergy": [
        "physicalH1_gradient_integration_by_parts", "physicalH1H2_laplacian_pairing",
        "physicalH2_laplacian_symmetric", "physicalH2_laplacian_enstrophy",
    ],
}
NEW_NAMES = {package: ["MethbokeAddon.QuasiFeffermanA." + package.removeprefix("QFA") + "." + name
                       for name in names] for package, names in NEW_NAMES.items()}
NEW_DEFINITION_NAMES = {
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator",
}
EXPECTED_MODULES, EXPECTED_PACKAGES, EXPECTED_REPORTS = 534, 109, 1435
EXPECTED_NEW, EXPECTED_THEOREMS, EXPECTED_DEFINITIONS = 24, 22, 2
EXPECTED_NEW_CONSUMERS = 29
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
checks = 0
frozen_cache = {}
baseline_cache = {}


def check(ok, message):
    global checks
    if not ok:
        raise AssertionError(message)
    checks += 1


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fingerprint(value):
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def frozen(path):
    if path not in frozen_cache:
        frozen_cache[path] = subprocess.check_output(
            ["git", "show", SHA + ":" + path], cwd=REPO)
    return frozen_cache[path]


def baseline(path):
    if path not in baseline_cache:
        baseline_cache[path] = subprocess.check_output(
            ["git", "show", POLICY_BASE + ":" + path], cwd=REPO)
    return baseline_cache[path]


def source_json(path):
    return json.loads(frozen(path))


def strip_comments(text):
    # Text parser only: handle nested Lean comments and string contents.
    out, pos, depth, quoted = [], 0, 0, False
    while pos < len(text):
        pair, char = text[pos:pos + 2], text[pos]
        if depth:
            if pair in {"/-", "-/"}:
                depth += 1 if pair == "/-" else -1
                out.append("  ")
                pos += 2
            else:
                out.append("\n" if char == "\n" else " ")
                pos += 1
        elif quoted:
            if char == "\\" and pos + 1 < len(text):
                out.append("  ")
                pos += 2
            else:
                out.append("\n" if char == "\n" else " ")
                quoted = char != '"'
                pos += 1
        elif pair == "/-":
            depth = 1
            out.append("  ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            if end == -1:
                out.append(" " * (len(text) - pos))
                break
            out.append(" " * (end - pos))
            pos = end
        elif char == '"':
            quoted = True
            out.append(" ")
            pos += 1
        else:
            out.append(char)
            pos += 1
    check(not depth and not quoted, "closed source comments/strings")
    return "".join(out)


def imports(data):
    result = []
    for line in strip_comments(data.decode()).splitlines():
        match = re.match(r"^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$", line)
        if match:
            result.extend(match.group(1).split())
    return result


metadata = json.loads((OUT / "artifact-metadata.json").read_text())
artifacts = metadata["artifacts"]
evidence_matches = [a for a in artifacts if a["name"].startswith(
    "material-evidence-" + SHA + "-" + RUN)]
check(len(evidence_matches) == 1, "unique complete evidence artifact for the exact source/run")
evidence_meta = evidence_matches[0]
check(evidence_meta["workflow_run"]["head_sha"] == SHA and
      str(evidence_meta["workflow_run"]["id"]) == RUN and
      evidence_meta["workflow_run"]["head_branch"] == "AC-Integration",
      "authenticated artifact metadata exact source/run/branch")
check(subprocess.check_output(["git", "rev-parse", SHA + "^{tree}"], cwd=REPO).decode().strip() == TREE,
      "independent immutable Git commit/tree identity")
raw_zip = (OUT / "evidence.zip").read_bytes()
check("sha256:" + digest(raw_zip) == evidence_meta["digest"], "original evidence ZIP digest")
check(len(raw_zip) == evidence_meta["size_in_bytes"], "original evidence ZIP byte count")
archive = zipfile.ZipFile(OUT / "evidence.zip")
report_bytes = archive.read("current.json")
report = json.loads(report_bytes)
check(report["commit"] == SHA and str(report["run_id"]) == RUN, "exact tested source/run")

# Every previously accepted proof, audit, manifest and closure is byte-preserved.
# Older closure records can retain declared source history overridden by the
# explicit owned-source registry. Preserve those historical records verbatim;
# reconstruct current actual source/import identities below, without treating
# legacy history hashes as the current native source authority.
changed_material = subprocess.check_output(
    ["git", "diff", "--no-ext-diff", "--name-only", POLICY_BASE, SHA, "--", "Material"],
    cwd=REPO).decode().splitlines()
allowed_new_material = {
    "Material/owned-sources.json", "Material/endpoints.json",
    *["Material/" + module.replace(".", "/") + ".lean" for module in NEW_SOURCE_MODULES],
    *["Material/" + package + "/" + name for package in NEW
      for name in ["Endpoint.lean", "Audit.lean", "endpoint.json", "closure.json"]],
}
check(all(path in allowed_new_material or path.endswith("/README.md") for path in changed_material),
      "prior accepted proof/audit/manifest/closure bytes unchanged from 809aadc6")
base_registry = json.loads(baseline("Material/endpoints.json"))
candidate_registry = source_json("Material/endpoints.json")
base_rows = {row["id"]: row for row in base_registry["endpoints"]}
candidate_rows = {row["id"]: row for row in candidate_registry["endpoints"]}
check(base_registry["endpoint_count"] == 106 and base_registry["declaration_count"] == 1411,
      "exact accepted generator registry basis")
check(set(candidate_rows) - set(base_rows) == set(NEW) and set(base_rows) <= set(candidate_rows),
      "only the three expected Duhamel/operator/spatial-energy packages are added")
for package, row in base_rows.items():
    check(candidate_rows[package] == row, package + " exact prior registry row retained")
base_owned = {row["module"]: row for row in json.loads(baseline("Material/owned-sources.json"))["modules"]}
candidate_owned = {row["module"]: row for row in source_json("Material/owned-sources.json")["modules"]}
check(set(candidate_owned) - set(base_owned) == NEW_SOURCE_MODULES,
      "only the three expected owned sources are added")
for module, row in base_owned.items():
    check(candidate_owned.get(module) == row, module + " exact prior owned-source identity retained")

if report["status"] == "FAIL":
    # Failed external runs are retained as failures, never partial acceptance.
    index = source_json("Material/endpoints.json")
    check(index["endpoint_count"] == EXPECTED_PACKAGES and index["declaration_count"] == EXPECTED_REPORTS,
          "failed candidate has the exact expected registry scope")
    specs_by_id = {row["id"]: source_json("Material/" + row["manifest"]) for row in index["endpoints"]}
    run_record = json.loads((OUT / "workflow-run.json").read_text())
    check(run_record["head_sha"] == SHA and str(run_record["id"]) == RUN and
          run_record["head_commit"]["tree_id"] == TREE, "failed run exact commit/tree identity")
    check(run_record["head_branch"] == "AC-Integration", "failed run exact branch")
    check(run_record["status"] == "completed" and run_record["conclusion"] in {"failure", "cancelled"},
          "failed run finished with no acceptance")
    receipts = report.get("module_receipts", {})
    check(len(receipts) <= EXPECTED_MODULES, "failed source-module receipt count")
    counts = collections.Counter(row["status"] for row in receipts.values())
    fresh_names = []
    passed_packages = []
    for entry in report.get("endpoints", []):
        package = entry["id"]
        spec = specs_by_id[package]
        names = [row["name"] for row in spec["declarations"]]
        check(entry["status"] == "PASS" and entry["audit_origin_commit"] == SHA and
              entry["audit_reused"] is False, package + " partial fresh passing receipt")
        check(set(entry["types"]) == set(names) == set(entry["axioms"]), package + " partial exact coverage")
        log_bytes = archive.read(entry["audit_log"].removeprefix("registry/"))
        check(digest(log_bytes) == entry["audit_sha256"], package + " partial raw-log digest")
        log = log_bytes.decode()
        check(not re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror(?:\([^\n)]*\))?\s*:", log, re.I),
              package + " partial audit has no error/admission")
        sentinels = re.findall(r"^(TYPE_BEGIN|TYPE_END|AXIOMS_BEGIN|AXIOMS_END):(.*)$", log, re.M)
        check(sentinels == [(tag, name) for name in names for tag in
                           ["TYPE_BEGIN", "TYPE_END", "AXIOMS_BEGIN", "AXIOMS_END"]],
              package + " partial exact ordered sentinels")
        for name in names:
            body = re.search(r"^TYPE_BEGIN:" + re.escape(name) + r"\n(.*?)\nTYPE_END:" + re.escape(name) + "$", log, re.M | re.S).group(1)
            check(" ".join(body.split()) == " ".join(entry["types"][name].split()), name + " partial exact type")
            body = re.search(r"^AXIOMS_BEGIN:" + re.escape(name) + r"\n(.*?)\nAXIOMS_END:" + re.escape(name) + "$", log, re.M | re.S).group(1).strip()
            some = re.fullmatch("'" + re.escape(name) + r"'\s+depends on axioms:\s*\[([^\]]*)\]", body, re.S)
            if some:
                axioms = {re.sub(r"\.\{[^}]*\}", "", a.strip()) for a in some.group(1).split(",") if a.strip()}
            else:
                check(re.fullmatch("'" + re.escape(name) + r"'\s+does not depend on any axioms\.?", body) is not None,
                      name + " partial exact axiom grammar")
                axioms = set()
            check(axioms <= STANDARD and axioms == set(entry["axioms"][name]), name + " partial standard-only axioms")
        fresh_names.extend(names)
        passed_packages.append(package)
    check(len(fresh_names) == len(set(fresh_names)), "partial named reports unique")
    diagnostics = []
    retained = []
    error_pattern = re.compile(r"\berror(?:\([^\n)]*\))?\s*:|\bsorryAx\b|\bwarning\s*:.*\bsorry\b", re.I)
    for name in archive.namelist():
        if not name.endswith(".log"):
            continue
        data = archive.read(name)
        lines = data.decode(errors="replace").splitlines()
        matches = [{"line": n + 1, "text": "\n".join(lines[max(0, n - 1):min(len(lines), n + 6)])}
                   for n, line in enumerate(lines) if error_pattern.search(line)]
        if matches:
            retained_name = name.replace("/", "__") + ".gz"
            (OUT / retained_name).write_bytes(gzip.compress(data, mtime=0))
            retained.append({"archive_path": name, "retained_log": retained_name, "raw_sha256": digest(data)})
            diagnostics.append({"archive_path": name, "diagnostics": matches})
    policy_paths = [".github", "Material/ci", "Material/lean-toolchain", "Material/lakefile.lean",
                    "Material/lake-manifest.json", "Material/_vendor/source-manifest.json",
                    "Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean",
                    "Material/MethbokeAddon/QuasiFeffermanA/PhysicalRoot.lean",
                    "LEAN_CUTOUTS/Cutouts.lean"]
    changed = subprocess.check_output(["git", "diff", "--name-only", POLICY_BASE, SHA, "--", *policy_paths],
                                      cwd=REPO).decode().strip()
    check(not changed, "failed candidate preserves root contract/cutoff and verification policy")
    summary = {
        "schema_version": 1, "status": "CHECKED_MATCHING_EXTERNAL_FAILURE_NO_ACCEPTANCE",
        "review_kind": "nonexecuting_text_json_hash_review", "tested_commit": SHA, "tree": TREE,
        "prior_policy_basis": POLICY_BASE, "run_id": int(RUN), "run_url": run_record["html_url"],
        "artifact_id": evidence_meta["id"], "artifact_sha256": digest(raw_zip), "artifact_bytes": len(raw_zip),
        "report_sha256": digest(report_bytes), "expected_module_count": EXPECTED_MODULES,
        "expected_package_count": EXPECTED_PACKAGES, "expected_named_reports": EXPECTED_REPORTS,
        "module_count": len(receipts), "module_counts": dict(counts),
        "failed_sources": [m for m, row in receipts.items() if row["status"] == "FAIL"],
        "blocked_sources": [m for m, row in receipts.items() if row["status"] == "BLOCKED_BY_DEPENDENCY"],
        "package_count": len(passed_packages), "named_reports": len(fresh_names),
        "passed_package_receipts": passed_packages, "all_package_audits_fresh": False,
        "complete_audit_coverage": False, "final_acceptance_gate": False, "publication_pass": False,
        "qfb_cutout_pass": report.get("cutout", {}).get("status") == "PASS",
        "new_a_tier_acceptance": False, "physical_qfa_root_proved": False, "wfa_proved": False,
        "prior_accepted_source_audits_and_closures_byte_preserved": True,
        "failure_phase": report.get("failure_phase"), "failure_class": report.get("failure_class"),
        "error": report.get("error"), "diagnostics": diagnostics, "retained_diagnostic_logs": retained,
        "checks_passed": checks, "local_lean_executions": 0,
        "scope_note": "Passing individual source or partial named audit receipts do not establish acceptance of this batch."
    }
    (OUT / "independent-review.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k not in ["diagnostics", "retained_diagnostic_logs"]},
                     indent=2, ensure_ascii=False))
    sys.exit(0)

check(report["status"] == "PASS", "complete external verification PASS")
check(report["all_endpoints_selected"] and report["fresh_required_audits"], "complete fresh audit selection")
check(report["toolchain"] == "leanprover/lean4:v4.33.0", "compiler toolchain pin")
check(report["mathlib_commit"] == "db584cd6d46c92f209a44c0f1c829460d327499d", "Mathlib revision pin")
check(report["compiler_executed"] and report["source_pin_integrity"], "external compiler/source pin receipt")
check(all(x["tracked_source_clean"] for x in report["verified_dependencies"]), "clean external dependencies")
check(report["platform"] == {"system": "Linux", "machine": "x86_64"}, "external platform identity")

registry = source_json("Material/endpoints.json")
check(registry["endpoint_count"] == 109 and registry["declaration_count"] == 1435, "exact registry scope")
specs = [source_json("Material/" + row["manifest"]) for row in registry["endpoints"]]
actual = {entry["id"]: entry for entry in report["endpoints"]}
check(len(actual) == len(report["endpoints"]) == 109, "unique complete package count")
check(set(actual) == {s["id"] for s in specs}, "exact package coverage")
check(report["metrics"]["audit_fresh_count"] == 109 and report["metrics"]["audit_reused_count"] == 0,
      "all 109 package audits fresh")

owned = {x["module"]: x for x in source_json("Material/owned-sources.json")["modules"]}
paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", SHA, "--", "Material"], cwd=REPO).decode().splitlines()
records = {}
for path in paths:
    rel = pathlib.PurePosixPath(path).relative_to("Material")
    if rel.suffix != ".lean" or rel.name == "lakefile.lean" or any(
            p in {".lake", ".standalone", "registry", "tests", "provenance", "ci"} for p in rel.parts):
        continue
    logical = rel.parts[1:] if rel.parts[0] == "_vendor" else rel.parts
    module = ".".join([*logical[:-1], pathlib.PurePosixPath(logical[-1]).stem])
    data = frozen(path)
    check(module not in records, "unique source module " + module)
    records[module] = {"module": module, "path": rel.as_posix(), "sha256": digest(data), "imports": imports(data)}
for module, row in owned.items():
    check(records[module]["sha256"] == row["sha256"] and records[module]["imports"] == row["imports"],
          "owned source bytes/imports " + module)

config = {p: digest(frozen("Material/" + p)) for p in
          ["lean-toolchain", "lake-manifest.json", "ci/build.py", "lakefile.lean"]}
check(report["build_configuration"] == config, "exact source build configuration")
context = report["compile_context"]
check(context["configuration"] == config and context["lock"] == config["lake-manifest.json"], "exact receipt source configuration")
for key, path in [("driver", "ci/native_build.py"), ("receipt_adapter", "ci/receipt_compatibility.py"),
                  ("launcher_policy", "ci/verify-external.sh")]:
    check(context[key] == digest(frozen("Material/" + path)), "exact receipt " + key)
check(context["compiler"] == report["compiler"] and context["platform"] == report["platform"], "receipt compiler/platform identity")
check(context["external_objects"] == report["external_objects"], "receipt dependency-object identity")

all_audits = {s["audit_module"] for s in specs}
selected_modules = set()
plans = {}
for spec in specs:
    pending = [spec["endpoint_module"], spec["audit_module"]]
    seen, external = set(), set()
    while pending:
        module = pending.pop()
        if module in seen or module in external:
            continue
        if module not in records:
            check(module.split(".")[0] in {"Init", "Lean", "Std", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible"},
                  "recognized external import " + module)
            external.add(module)
        else:
            seen.add(module)
            pending.extend(records[module]["imports"])
    files = [records[name] for name in sorted(seen)]
    selected_modules.update(seen - all_audits)
    payload = {"id": spec["id"], "config": config, "files": files,
               "spec_sha256": digest(frozen("Material/" + spec["id"] + "/endpoint.json")),
               "external_imports": sorted(external),
               "owned_sources": {x["module"]: owned[x["module"]] for x in files if x["module"] in owned},
               "platform": report["platform"]}
    identity = fingerprint({"input": fingerprint(payload), "compiler": report["compiler"], "context": context})
    check(actual[spec["id"]]["input_hash"] == identity, "independent exact audit source identity " + spec["id"])
    plans[spec["id"]] = files

receipts = report["module_receipts"]
check(len(receipts) == 534 and set(receipts) == selected_modules, "all 534 exact source modules selected")
check(all(x["status"] == "PASS" for x in receipts.values()), "all 534 source modules PASS")
check(report["metrics"]["module_count"] == EXPECTED_MODULES and
      all(type(row["reused"]) is bool for row in receipts.values()), "exact module/cache receipt metrics")
check(report["metrics"]["reused_module_count"] == sum(row["reused"] for row in receipts.values()) and
      report["metrics"]["fresh_module_count"] == sum(not row["reused"] for row in receipts.values()),
      "fresh/reused module counts agree with all matching receipts")
for module, receipt in receipts.items():
    dependencies = {i: receipts[i] for i in records[module]["imports"] if i in receipts}
    identity = fingerprint({"context": context, "source": records[module]["sha256"], "module": module,
                            "imports": {i: {"identity": x["identity"], "objects": x["object_files"]}
                                        for i, x in dependencies.items()}})
    check(receipt["identity"] == identity, "independent exact module source/import identity " + module)

all_names, new_reports, package_rows = [], [], []
for spec in specs:
    package = spec["id"]
    entry = actual[package]
    names = [d["name"] for d in spec["declarations"]]
    all_names.extend(names)
    check(entry["status"] == "PASS" and entry["source_drift"] == [], package + " source/audit PASS")
    check(set(spec["allowed_axioms"]) <= STANDARD and spec["allowed_axioms"], package + " standard-only policy")
    check(entry["audit_origin_commit"] == SHA and entry["audit_reused"] is False, package + " fresh matching audit")
    check(entry["declaration_count"] == len(names) == len(set(names)), package + " exact declaration count")
    check(set(entry["types"]) == set(names) == set(entry["axioms"]), package + " complete named coverage")
    log_bytes = archive.read(entry["audit_log"].removeprefix("registry/"))
    check(digest(log_bytes) == entry["audit_sha256"], package + " original raw-log hash")
    log = log_bytes.decode()
    check(not re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror(?:\([^\n)]*\))?\s*:", log, re.I), package + " no error/admission")
    sentinels = re.findall(r"^(TYPE_BEGIN|TYPE_END|AXIOMS_BEGIN|AXIOMS_END):(.*)$", log, re.M)
    check(sentinels == [(tag, name) for name in names for tag in ["TYPE_BEGIN", "TYPE_END", "AXIOMS_BEGIN", "AXIOMS_END"]],
          package + " exact ordered unique sentinels")
    for name in names:
        type_match = re.search(r"^TYPE_BEGIN:" + re.escape(name) + r"\n(.*?)\nTYPE_END:" + re.escape(name) + "$", log, re.M | re.S)
        check(type_match is not None, name + " literal type block")
        check(" ".join(type_match.group(1).split()) == " ".join(entry["types"][name].split()), name + " exact reported type")
        body = re.search(r"^AXIOMS_BEGIN:" + re.escape(name) + r"\n(.*?)\nAXIOMS_END:" + re.escape(name) + "$", log, re.M | re.S).group(1).strip()
        some = re.fullmatch("'" + re.escape(name) + r"'\s+depends on axioms:\s*\[([^\]]*)\]", body, re.S)
        if some:
            axioms = {re.sub(r"\.\{[^}]*\}", "", a.strip()) for a in some.group(1).split(",") if a.strip()}
        else:
            check(re.fullmatch("'" + re.escape(name) + r"'\s+does not depend on any axioms\.?", body) is not None,
                  name + " exact axiom-record grammar")
            axioms = set()
        check(axioms <= STANDARD and axioms == set(entry["axioms"][name]), name + " exact standard-only named axioms")
        if package in NEW:
            decl = next(d for d in spec["declarations"] if d["name"] == name)
            new_reports.append({"package": package, "name": name, "kind": decl["kind"],
                                 "type": entry["types"][name], "axioms": sorted(axioms)})
    audit_source = frozen("Material/" + package + "/Audit.lean")
    check(re.findall(r"^#check\s+@?(\S+)", audit_source.decode(), re.M) == names, package + " exact source audit-target order")
    row = {"id": package, "declarations": len(names), "audit_sha256": entry["audit_sha256"],
           "audit_source_sha256": digest(audit_source), "input_hash": entry["input_hash"]}
    if package in NEW:
        consumers = len(re.findall(r"^example\b", audit_source.decode(), re.M))
        check(consumers == NEW_CONSUMERS[package], package + " exact independent literal consumer count")
        (OUT / (package + ".log.gz")).write_bytes(gzip.compress(log_bytes, mtime=0))
        row.update({"retained_log": package + ".log.gz", "consumer_examples": consumers,
                    "scope": spec["scope"], "supports_proposed_endpoints": spec.get("supports_proposed_endpoints", [])})
    package_rows.append(row)
check(len(all_names) == len(set(all_names)) == 1435, "all 1435 unique named reports")
check(len(new_reports) == EXPECTED_NEW and {r["package"] for r in new_reports} == set(NEW),
      "exact three-package Duhamel/operator/spatial-energy scope")
check(sum(r["kind"] == "theorem" for r in new_reports) == EXPECTED_THEOREMS and
      sum(r["kind"] == "definition" for r in new_reports) == EXPECTED_DEFINITIONS,
      "22 new theorems and two new definitions")
check(sum(row.get("consumer_examples", 0) for row in package_rows) == EXPECTED_NEW_CONSUMERS,
      "exact 29 new independent literal consumers")
for package, expected in NEW.items():
    rows = [r for r in new_reports if r["package"] == package]
    check(len(rows) == expected, package + " exact new count")
    check(sum(row["kind"] == "definition" for row in rows) == NEW_DEFINITIONS[package] and
          sum(row["kind"] == "theorem" for row in rows) == expected - NEW_DEFINITIONS[package],
          package + " exact theorem/definition split")
    check({row["name"] for row in rows} == set(NEW_NAMES[package]), package + " exact independently expected new names")
    check(all(row["kind"] == ("definition" if row["name"] in NEW_DEFINITION_NAMES else "theorem") for row in rows),
          package + " exact intended theorem/definition identities")
    spec = next(s for s in specs if s["id"] == package)
    closure = source_json("Material/" + package + "/closure.json")
    check(closure["endpoint"] == package and
          closure["roots"] == [source["module"] for source in spec["source_roots"]],
          package + " exact native closure roots")
    closure_hash = fingerprint({key: closure[key] for key in ["roots", "files", "external_imports"]})
    check(closure_hash == closure["source_closure_sha256"] == candidate_rows[package]["source_closure_sha256"],
          package + " independently reconstructed native closure digest")
    check(len(closure["files"]) == closure["local_module_count"] == candidate_rows[package]["local_source_modules"],
          package + " exact native closure file count")
    check({item["module"] for item in closure["files"]} ==
          {item["module"] for item in plans[package]} - {spec["endpoint_module"], spec["audit_module"]},
          package + " exact transitive native source closure coverage")
    for item in closure["files"]:
        check(digest(frozen("Material/" + item["path"])) == item["sha256"],
              package + " immutable closure source " + item["path"])
        check(all(item[key] == records[item["module"]][key] for key in ["module", "path", "sha256", "imports"]),
              package + " exact closure source path/hash/imports " + item["module"])
    for source in spec["source_roots"]:
        check(source["derivation_basis"]["revision"] == POLICY_BASE,
              package + " exact accepted source/plan basis")

cutout = report["cutout"]
check(cutout["status"] == "PASS" and cutout["audit_origin_commit"] == SHA and cutout["audit_reused"] is False,
      "fresh standalone QFB cutout PASS")
cutout_bytes = archive.read(cutout["audit_log"].removeprefix("registry/"))
check(digest(cutout_bytes) == cutout["audit_sha256"], "original QFB cutout log hash")
check(cutout["source_sha256"] == digest(frozen("LEAN_CUTOUTS/Cutouts.lean")), "exact original cutout source")
check(all(set(ax) <= STANDARD for ax in cutout["axioms"].values()), "QFB standard-only named axioms")
(OUT / "QFB-cutout.log").write_bytes(cutout_bytes)

run = json.loads((OUT / "workflow-run.json").read_text())
jobs = json.loads((OUT / "workflow-jobs.json").read_text())["jobs"]
check(run["head_sha"] == SHA and str(run["id"]) == RUN and run["status"] == "completed" and run["conclusion"] == "success",
      "completed successful matching GitHub run")
check(run["head_commit"]["tree_id"] == TREE, "exact submitted Git tree")
check(run["head_branch"] == "AC-Integration", "exact accepted branch")
for name in ["Fast cached verification", "Material accepted"]:
    job = next(j for j in jobs if j["name"] == name)
    check(job["status"] == "completed" and job["conclusion"] == "success", name + " job PASS")
gate = (OUT / "acceptance-job.log").read_text()
check("PRIMARY_ACCEPTED: true" in gate and "PRIMARY_RESULT: success" in gate and "PRIMARY_FAILURE_CLASS: NONE" in gate,
      "terminal acceptance gate context")
routing_meta = next(a for a in artifacts if a["name"].startswith("material-routing-" + SHA + "-" + RUN))
routing_bytes = (OUT / "routing-evidence.zip").read_bytes()
check("sha256:" + digest(routing_bytes) == routing_meta["digest"], "original routing artifact digest")
check(len(routing_bytes) == routing_meta["size_in_bytes"] and
      routing_meta["workflow_run"]["head_sha"] == SHA and str(routing_meta["workflow_run"]["id"]) == RUN,
      "matching routing artifact bytes and source/run identity")
routing = json.loads(zipfile.ZipFile(OUT / "routing-evidence.zip").read("failure-routing.json"))
check(routing["commit"] == SHA and str(routing["run_id"]) == RUN, "exact routing source/run")
check(routing["backend"] == "binary_cache" and routing["failure_class"] == "NONE" and routing["failed_step"] is None,
      "successful cached-worker routing")
for step in ["static", "verify", "verified_evidence", "binary_package", "save_project", "published_dependencies",
             "published_project", "published_identities", "publish_binary", "final_evidence"]:
    check(routing["step_outcomes"][step] == "success", "complete external publication " + step)
for prefix in ["material-binary-", "material-verified-", "material-evidence-"]:
    artifact = next(a for a in artifacts if a["name"].startswith(prefix + SHA + "-" + RUN))
    check(not artifact["expired"] and artifact["size_in_bytes"] > 0 and artifact["workflow_run"]["head_sha"] == SHA,
          "matching published " + prefix)
    check(str(artifact["workflow_run"]["id"]) == RUN and
          artifact["workflow_run"]["head_branch"] == "AC-Integration", "matching publication run/branch " + prefix)
binary = json.loads(archive.read("binary-entry.json"))
check(binary["commit"] == SHA and str(binary["run_id"]) == RUN and binary["module_count"] == 534,
      "matching complete binary publication identity")

preserved_paths = ["Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean",
                   "Material/MethbokeAddon/QuasiFeffermanA/PhysicalRoot.lean",
                   "Material/MethbokeAddon/QuasiFeffermanA/Energy.lean",
                   "LEAN_CUTOUTS/Cutouts.lean",
                   ".github", "Material/ci", "Material/lean-toolchain", "Material/lakefile.lean",
                   "Material/lake-manifest.json", "Material/_vendor/source-manifest.json"]
changes = subprocess.check_output(["git", "diff", "--name-only", POLICY_BASE,
                                   SHA, "--", *preserved_paths], cwd=REPO).decode().strip()
check(not changes, "byte-preserved physical LH/root/cutoff, all accepted generator/heat-time proof bytes and verification policy")
key_names = [
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_ae_eq",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_norm_le_sqrt_mul_lpNorm",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamel.duhamelL2_continuousOn",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le",
    "MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply",
    "MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1_gradient_integration_by_parts",
    "MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH1H2_laplacian_pairing",
    "MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_symmetric",
    "MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy.physicalH2_laplacian_enstrophy",
]
key_reports = {name: next(r for r in new_reports if r["name"] == name) for name in key_names}
check(len(key_reports) == 9, "nine concrete physical endpoint reports")
summary = {
    "schema_version": 1, "status": "CHECKED_MATCHING_EXTERNAL_ACCEPTANCE",
    "review_kind": "nonexecuting_text_json_hash_review", "tested_commit": SHA, "tree": TREE,
    "prior_policy_basis": POLICY_BASE, "run_id": int(RUN), "run_url": run["html_url"],
    "artifact_id": evidence_meta["id"], "artifact_sha256": digest(raw_zip), "artifact_bytes": len(raw_zip),
    "report_sha256": digest(report_bytes), "routing_artifact_sha256": digest(routing_bytes),
    "module_count": EXPECTED_MODULES, "package_count": EXPECTED_PACKAGES, "named_reports": EXPECTED_REPORTS,
    "all_package_audits_fresh": True, "metrics": report["metrics"],
    "new_packages": len(NEW), "new_named_declarations": EXPECTED_NEW,
    "new_theorems": EXPECTED_THEOREMS, "new_definitions": EXPECTED_DEFINITIONS,
    "new_literal_consumers": sum(r.get("consumer_examples", 0) for r in package_rows),
    "new_package_counts": {
        package: {"declarations": count, "theorems": count - NEW_DEFINITIONS[package],
                  "definitions": NEW_DEFINITIONS[package], "consumer_examples": NEW_CONSUMERS[package]}
        for package, count in NEW.items()
    },
    "key_endpoint_reports": key_reports,
    "physical_root_and_cutoff_byte_preserved": True,
    "prior_accepted_source_audits_and_closures_byte_preserved": True,
    "new_source_closure_independently_reconstructed": True,
    "compiler_dependencies_and_verification_policy_unchanged": True,
    "compiler": report["compiler"], "toolchain": report["toolchain"],
    "mathlib_commit": report["mathlib_commit"], "allowed_axioms": sorted(STANDARD),
    "final_acceptance_gate": True, "publication_pass": True, "qfb_cutout_pass": True,
    "physical_L2_duhamel_response_constructed": True,
    "physical_L2_duhamel_continuous_zero_trace_proved": True,
    "physical_L2_duhamel_ae_invariance_and_linearity_proved": True,
    "physical_L2_duhamel_sqrt_time_forcing_bound_proved": True,
    "physical_L2_duhamel_forcing_quotient_CLM_proved": True,
    "physical_L2_duhamel_operator_norm_bound_proved": True,
    "physical_H1_gradient_integration_by_parts_proved": True,
    "physical_H1_H2_green_pairing_proved": True,
    "physical_H2_laplacian_symmetric_pairing_proved": True,
    "physical_H2_laplacian_negative_enstrophy_pairing_proved": True,
    "forced_heat_time_derivative_equation_proved": False,
    "unbounded_laplacian_self_adjointness_proved": False,
    "forced_heat_maximal_regularity_proved": False,
    "nonlinear_H1_local_theory_proved": False,
    "new_full_ten_step_items_closed": [],
    "physical_qfa_root_proved": False, "wfa_proved": False,
    "new_parent_targets_closed": [], "parent_targets_remaining_open": ["G01", "G02", "G03", "G04", "G06"],
    "independently_reconstructed_module_source_identities": EXPECTED_MODULES,
    "independently_reconstructed_audit_source_identities": EXPECTED_PACKAGES,
    "checks_passed": checks, "local_lean_executions": 0,
    "scope_limits": [
        "The Duhamel construction applies to actual finite-window time-L2 spatial-L2 forcing, with nonnegative viscosity; it does not claim an arbitrary time-L1 forcing theorem.",
        "The literal retarded Bochner integral is invariant under time-a.e. equality, linear on admissible forcing, continuous on the closed finite window and has exactly zero initial trace, including T=0.",
        "The forcing bound uses sqrt(T) times the norm of the actual Bochner-L2 forcing class, and the integral of the forcing norm. The response is a constructed continuous linear map into continuous physical L2 paths, with no supplied operator or response witness.",
        "Spatial integration by parts and the H1-H2 Green identity are for actual physical graphs; the Laplacian symmetry is the explicit bilinear pairing identity, not a self-adjoint unbounded-operator domain theorem.",
        "The Laplacian enstrophy pairing is exactly the negative actual H1 enstrophy, with no hidden one-half normalization or supplied integration-by-parts premise.",
        "Forced heat maximal regularity and the inhomogeneous time-derivative equation remain open; nonlinear H1 theory, general LH existence, physical weak-strong comparison, sharp Sobolev admission and general QFA/WFA are not concluded.",
        "External Linux compiler evidence is retained; no local Lean, Lake, kernel or native-Windows verification was performed."
    ],
    "packages": package_rows
}
(OUT / "independent-review.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
(OUT / "new-declaration-evidence.json.gz").write_bytes(gzip.compress(
    (json.dumps(new_reports, indent=2, ensure_ascii=False) + "\n").encode(), mtime=0))
(OUT / "new-declaration-index.json").write_text(json.dumps([
    {"package": r["package"], "name": r["name"], "kind": r["kind"],
     "type_sha256": digest(r["type"].encode()), "axioms": r["axioms"]}
    for r in new_reports], indent=2) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k not in ["packages", "metrics", "key_endpoint_reports"]},
                 indent=2, ensure_ascii=False))
