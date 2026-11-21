"""Independent read-only review of external FDSN_R3 evidence.

No Lean, Lake, kernel, repository script, or compiler is executed. This program
only reads immutable Git objects and external ZIP/JSON/text evidence, computes
hashes, and writes its review outside the repository.
Usage: python3 review_evidence.py REPOSITORY EVIDENCE_DIRECTORY
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

REPO, OUT = map(pathlib.Path, sys.argv[1:3])
SHA = "572fd9ee69a6b641f435cbfb2ef74e034809c583"
TREE = "d5b0e6baa53c68c2d4c97e4f2f0843b76047eb07"
RUN = "44848985720"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
checks = 0
frozen_cache = {}


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
evidence_meta = next(a for a in artifacts if a["name"].startswith(
    "material-evidence-" + SHA + "-" + RUN))
raw_zip = (OUT / "evidence.zip").read_bytes()
check("sha256:" + digest(raw_zip) == evidence_meta["digest"], "original evidence ZIP digest")
check(len(raw_zip) == evidence_meta["size_in_bytes"], "original evidence ZIP byte count")
archive = zipfile.ZipFile(OUT / "evidence.zip")
report_bytes = archive.read("current.json")
report = json.loads(report_bytes)
check(report["commit"] == SHA and str(report["run_id"]) == RUN, "exact tested source/run")
check(report["status"] == "PASS", "complete external verification PASS")
check(report["all_endpoints_selected"] and report["fresh_required_audits"], "complete fresh audit selection")
check(report["toolchain"] == "leanprover/lean4:v4.33.0", "compiler toolchain pin")
check(report["mathlib_commit"] == "db584cd6d46c92f209a44c0f1c829460d327499d", "Mathlib revision pin")
check(report["compiler_executed"] and report["source_pin_integrity"], "external compiler/source pin receipt")
check(all(x["tracked_source_clean"] for x in report["verified_dependencies"]), "clean external dependencies")
check(report["platform"] == {"system": "Linux", "machine": "x86_64"}, "external platform identity")

registry = source_json("Material/endpoints.json")
check(registry["endpoint_count"] == 137 and registry["declaration_count"] == 1320, "exact registry scope")
specs = [source_json("Material/" + row["manifest"]) for row in registry["endpoints"]]
actual = {entry["id"]: entry for entry in report["endpoints"]}
check(len(actual) == len(report["endpoints"]) == 137, "unique complete package count")
check(set(actual) == {s["id"] for s in specs}, "exact package coverage")
check(report["metrics"]["audit_fresh_count"] == 137 and report["metrics"]["audit_reused_count"] == 0,
      "all 137 package audits fresh")

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
check(len(receipts) == 548 and set(receipts) == selected_modules, "all 548 exact source modules selected")
check(all(x["status"] == "PASS" for x in receipts.values()), "all 548 source modules PASS")
for module, receipt in receipts.items():
    dependencies = {i: receipts[i] for i in records[module]["imports"] if i in receipts}
    identity = fingerprint({"context": context, "source": records[module]["sha256"], "module": module,
                            "imports": {i: {"identity": x["identity"], "objects": x["object_files"]}
                                        for i, x in dependencies.items()}})
    check(receipt["identity"] == identity, "independent exact module source/import identity " + module)

all_names, fdsn_reports, package_rows = [], [], []
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
        if package.startswith("FDSNR3"):
            decl = next(d for d in spec["declarations"] if d["name"] == name)
            fdsn_reports.append({"package": package, "name": name, "kind": decl["kind"],
                                 "type": entry["types"][name], "axioms": sorted(axioms)})
    audit_source = frozen("Material/" + package + "/Audit.lean")
    check(re.findall(r"^#check @(\S+)", audit_source.decode(), re.M) == names, package + " exact source audit-target order")
    row = {"id": package, "declarations": len(names), "audit_sha256": entry["audit_sha256"],
           "audit_source_sha256": digest(audit_source), "input_hash": entry["input_hash"]}
    if package.startswith("FDSNR3"):
        consumers = len(re.findall(r"^example\b", audit_source.decode(), re.M))
        check(consumers >= len(names), package + " independent literal consumers")
        (OUT / (package + ".log.gz")).write_bytes(gzip.compress(log_bytes, mtime=0))
        row.update({"retained_log": package + ".log.gz", "consumer_examples": consumers,
                    "scope": spec["scope"], "supports_proposed_endpoints": spec.get("supports_proposed_endpoints", [])})
    package_rows.append(row)
check(len(all_names) == len(set(all_names)) == 1320, "all 1320 unique named reports")
check(len(fdsn_reports) == 493 and len({r["package"] for r in fdsn_reports}) == 26, "exact FDSNR3 scope")
check(collections.Counter(r["kind"] for r in fdsn_reports) == {"theorem": 391, "def": 97, "abbrev": 2, "structure": 3},
      "exact FDSNR3 declaration kinds")
check(sum(r.get("consumer_examples", 0) for r in package_rows) == 497, "all 497 independent FDSNR3 consumers")

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
for name in ["Fast cached verification", "Material accepted"]:
    job = next(j for j in jobs if j["name"] == name)
    check(job["status"] == "completed" and job["conclusion"] == "success", name + " job PASS")
gate = (OUT / "acceptance-job.log").read_text()
check("PRIMARY_ACCEPTED: true" in gate and "PRIMARY_RESULT: success" in gate and "PRIMARY_FAILURE_CLASS: NONE" in gate,
      "terminal acceptance gate context")
routing_meta = next(a for a in artifacts if a["name"].startswith("material-routing-" + SHA + "-" + RUN))
routing_bytes = (OUT / "routing-evidence.zip").read_bytes()
check("sha256:" + digest(routing_bytes) == routing_meta["digest"], "original routing artifact digest")
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
binary = json.loads(archive.read("binary-entry.json"))
check(binary["commit"] == SHA and str(binary["run_id"]) == RUN and binary["module_count"] == 548,
      "matching complete binary publication identity")

root = next(r for r in fdsn_reports if r["name"] == "MethbokeAddon.FDSNR3.FDSN_R3")
check("MethbokeAddon.FDSNR3.Seed" in root["type"] and "MethbokeAddon.FDSNR3.Family" in root["type"],
      "original Seed-to-Family root report")
preserved_paths = ["Material/MethbokeAddon/FDSNR3/Contracts.lean", "Material/FDSNR3Contracts/Audit.lean",
                   ".github", "Material/ci", "Material/lean-toolchain", "Material/lakefile.lean",
                   "Material/lake-manifest.json", "Material/_vendor/source-manifest.json"]
changes = subprocess.check_output(["git", "diff", "--name-only", "4d00e260e82368b9d9abbec7e14ce32844f8f7dc",
                                   SHA, "--", *preserved_paths], cwd=REPO).decode().strip()
check(not changes, "byte-preserved original Seed/Family contracts, literal contract audit, and verification policy")
previously_accepted = {"FDSNR3Contracts", "FDSNR3CompactSchwartz", "FDSNR3Phase"}
new_reports = [r for r in fdsn_reports if r["package"] not in previously_accepted]
check(len(new_reports) == 421 and sum(r["kind"] == "theorem" for r in new_reports) == 354,
      "421 newly accepted names beyond the prior 72-name foundation")
endpoint_map = collections.defaultdict(list)
for row in package_rows:
    for endpoint in row.get("supports_proposed_endpoints", []):
        endpoint_map[endpoint].append(row["id"])
check(set(endpoint_map) == {f"R3-{n:02d}" for n in range(1, 17)}, "all sixteen mathematical endpoints mapped")
summary = {
    "schema_version": 1, "status": "CHECKED_MATCHING_EXTERNAL_ACCEPTANCE",
    "review_kind": "nonexecuting_text_json_hash_review", "tested_commit": SHA, "tree": TREE,
    "run_id": int(RUN), "run_url": run["html_url"], "artifact_id": evidence_meta["id"],
    "artifact_sha256": digest(raw_zip), "artifact_bytes": len(raw_zip),
    "report_sha256": digest(report_bytes), "routing_artifact_sha256": digest(routing_bytes),
    "module_count": 548, "package_count": 137, "named_reports": 1320,
    "all_package_audits_fresh": True, "metrics": report["metrics"],
    "fdsn_r3_packages": 26, "fdsn_r3_named_declarations": 493,
    "fdsn_r3_theorems": 391, "fdsn_r3_definitions_abbreviations_structures": 102,
    "fdsn_r3_literal_consumers": 497, "root_declaration": root["name"],
    "fdsn_r3_new_packages": 23, "fdsn_r3_new_named_declarations": 421,
    "fdsn_r3_new_theorems": 354, "fdsn_r3_new_definitions_abbreviations_structures": 67,
    "original_seed_family_contracts_byte_preserved": True,
    "compiler_dependencies_and_verification_policy_unchanged": True,
    "root_type": root["type"], "root_axioms": root["axioms"],
    "compiler": report["compiler"], "toolchain": report["toolchain"],
    "mathlib_commit": report["mathlib_commit"], "allowed_axioms": sorted(STANDARD),
    "final_acceptance_gate": True, "publication_pass": True, "qfb_cutout_pass": True,
    "native_fdsn_r3_conditional_root_accepted": True, "seed_existence_proved": False,
    "mathematical_endpoints_accepted": sorted(endpoint_map),
    "mathematical_endpoint_packages": dict(sorted(endpoint_map.items())),
    "independently_reconstructed_module_source_identities": 548,
    "independently_reconstructed_audit_source_identities": 137,
    "checks_passed": checks, "local_lean_executions": 0,
    "scope_limits": [
        "The accepted root assumes the original explicit local-Schwartz compact-local-blowup Seed; it does not construct such a seed.",
        "One actual physical velocity/force family satisfies every original Family clause; parameter-dependent forces retain the same pressure and terminal tail.",
        "Rapid spatial Schwartz decay is proved; compact spatial support of the force is not asserted.",
        "This is not the separate stronger prescribed-site same-force family root, and it does not close general QFA or WFA.",
        "External Linux compiler evidence is retained; no local Lean or native-Windows verification was performed."
    ],
    "packages": package_rows
}
(OUT / "independent-review.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n")
(OUT / "fdsn-declaration-evidence.json.gz").write_bytes(gzip.compress(
    (json.dumps(fdsn_reports, indent=2, ensure_ascii=False) + "\n").encode(), mtime=0))
(OUT / "fdsn-declaration-index.json").write_text(json.dumps([
    {"package": r["package"], "name": r["name"], "kind": r["kind"],
     "type_sha256": digest(r["type"].encode()), "axioms": r["axioms"]}
    for r in fdsn_reports], indent=2) + "\n")
print(json.dumps({k: v for k, v in summary.items() if k not in ["packages", "metrics", "mathematical_endpoint_packages"]},
                 indent=2, ensure_ascii=False))
