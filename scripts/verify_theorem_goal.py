#!/usr/bin/env python3
"""Fresh, goal-scoped audits of receipt-verified Material objects in external CI.

This is not a compiler/cache-publication replacement for material.yml.  It never
compiles project modules, hydrates dependencies, mutates the canonical PASS
report, migrates receipts, or promotes an open mathematical root.  All commands,
including plan/admit, are reserved for the routed GitHub Actions workflow.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time


REPOSITORY = "randogelist/Methboke"
UPSTREAM_WORKFLOW = "Material / cached verification and passed objects"
GOAL_IDS = (
    "WFA", "WFB", "QFA", "QFB", "NSE_A_SINGLE_INPUT_OBSTRUCTION",
    "NSE_B_SINGLE_INPUT_OBSTRUCTION",
)
ROOT_STATUSES = {
    "OPEN", "OPEN_GENERAL_DATA", "OPEN_NO_NATIVE_ROOT",
    "CONDITIONAL_FULL_BUDGET", "CONDITIONAL_REDUCTION_WITNESS_OPEN",
    "EXACT_ROOT_ESTABLISHED",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ROOT = Path(__file__).resolve().parents[1]
SHA = re.compile(r"[0-9a-f]{40}")


class ScopeError(RuntimeError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def require(condition: bool, code: str, message: str) -> None:
    if not condition:
        raise ScopeError(code, message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint(value: object) -> str:
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def read_object(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), "INVALID_JSON", f"Expected a JSON object: {path.name}")
    return value


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def external_envelope(environment: dict[str, str]) -> None:
    require(environment.get("CI", "").lower() == "true"
            and environment.get("GITHUB_ACTIONS", "").lower() == "true"
            and environment.get("GITHUB_REPOSITORY") == REPOSITORY
            and environment.get("RUNNER_ENVIRONMENT") == "github-hosted"
            and environment.get("RUNNER_OS") == "Linux"
            and environment.get("RUNNER_ARCH") == "X64",
            "EXTERNAL_CI_REQUIRED", "Only the authorized hosted Linux GitHub Actions route may run this command.")
    for name in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        require(environment.get(name, "").isdigit() and int(environment[name]) > 0,
                "ROUTE_REJECTED", f"Missing positive {name}.")


def validate_route(environment: dict[str, str], event: dict, revision: str) -> dict:
    """Pure routing check; the workflow_run source may differ from GITHUB_SHA."""
    external_envelope(environment)
    require(bool(SHA.fullmatch(revision)), "ROUTE_REJECTED", "An exact lowercase source SHA is required.")
    require(event.get("repository", {}).get("full_name") == REPOSITORY,
            "ROUTE_REJECTED", "The triggering event belongs to another repository.")
    event_name = environment.get("GITHUB_EVENT_NAME")
    upstream = None
    if event_name == "workflow_run":
        run = event.get("workflow_run", {})
        require(run.get("name") == UPSTREAM_WORKFLOW
                and run.get("path") == ".github/workflows/material.yml"
                and run.get("status") == "completed" and run.get("conclusion") == "success"
                and run.get("head_branch") == "main"
                and run.get("head_repository", {}).get("full_name") == REPOSITORY
                and run.get("head_sha") == revision,
                "ROUTE_REJECTED", "Require a successful same-repository Material run for this exact main source.")
        require(isinstance(run.get("id"), int) and run["id"] > 0,
                "ROUTE_REJECTED", "The upstream Material run ID is missing.")
        upstream = {"run_id": str(run["id"]), "attempt": run.get("run_attempt"),
                    "source_revision": revision,
                    "url": f"https://github.com/{REPOSITORY}/actions/runs/{run['id']}"}
    elif event_name == "workflow_dispatch":
        require(environment.get("GITHUB_REF") == "refs/heads/main"
                and environment.get("GITHUB_SHA") == revision,
                "ROUTE_REJECTED", "Manual scoped verification must use the exact dispatched main revision.")
    else:
        raise ScopeError("ROUTE_REJECTED", "Only workflow_run and manual main dispatch are supported.")
    return {"event": event_name, "branch": "main", "upstream": upstream,
            "audit_run_id": environment["GITHUB_RUN_ID"],
            "audit_run_attempt": environment["GITHUB_RUN_ATTEMPT"],
            "audit_run_url": f"https://github.com/{REPOSITORY}/actions/runs/{environment['GITHUB_RUN_ID']}"}


def validate_checkout_sha(actual: str, revision: str) -> None:
    require(actual.strip() == revision, "SOURCE_REVISION_MISMATCH",
            "The actual checked-out Git HEAD differs from the routed source revision.")


def check_checkout(root: Path, revision: str, environment: dict[str, str]) -> None:
    require(Path(environment.get("GITHUB_WORKSPACE", "")).resolve() == root,
            "SOURCE_REVISION_MISMATCH", "The script must run from the checked-out GitHub workspace.")
    actual = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                            check=True, capture_output=True, text=True).stdout
    validate_checkout_sha(actual, revision)
    changed = subprocess.run(["git", "-C", str(root), "status", "--porcelain", "--untracked-files=no"],
                             check=True, capture_output=True, text=True).stdout
    require(not changed.strip(), "SOURCE_REVISION_MISMATCH", "Tracked checkout files have been modified.")


def load_drivers(root: Path):
    directory = root / "Material/ci"
    sys.path.insert(0, str(directory))
    modules = [importlib.import_module(name) for name in ("build", "native_build", "native_registry")]
    for name, module in zip(("build", "native_build", "native_registry"), modules):
        require(Path(module.__file__).resolve() == (directory / (name + ".py")).resolve(),
                "DRIVER_IDENTITY_MISMATCH", "A canonical driver was imported from outside this checkout.")
    return modules


def validate_manifest(manifest: dict, entries: list[dict]) -> dict[str, dict]:
    require(manifest.get("schema_version") == 1 and manifest.get("repository") == REPOSITORY
            and manifest.get("audit_dependency_packages") is True,
            "SCOPE_MANIFEST_REJECTED", "Unsupported goal manifest or disabled dependency-package audits.")
    rows = manifest.get("goals")
    require(isinstance(rows, list) and len(rows) == len(GOAL_IDS)
            and all(isinstance(row, dict) for row in rows),
            "SCOPE_MANIFEST_REJECTED", "Exactly six goal records are required.")
    ids = [row.get("id") for row in rows]
    require(len(set(ids)) == len(GOAL_IDS) and set(ids) == set(GOAL_IDS),
            "SCOPE_MANIFEST_REJECTED", "Goal IDs must be the six distinct registered IDs.")
    available = {entry["id"] for entry in entries}
    for row in rows:
        status = row.get("root_status")
        packages = row.get("principal_packages")
        obligations = row.get("open_obligations")
        require(row.get("domain") == ("R3" if row["id"] in
                {"WFA", "QFA", "NSE_A_SINGLE_INPUT_OBSTRUCTION"} else "T3")
                and isinstance(row.get("name"), str) and bool(row["name"].strip())
                and isinstance(row.get("verification_scope"), str) and bool(row["verification_scope"].strip())
                and status in ROOT_STATUSES and isinstance(row.get("standalone_qfb"), bool),
                "SCOPE_MANIFEST_REJECTED", "Invalid domain, status or verification boundary: " + row["id"])
        require(isinstance(packages, list) and bool(packages)
                and all(isinstance(p, str) for p in packages)
                and len(packages) == len(set(packages)) and set(packages) <= available,
                "SCOPE_MANIFEST_REJECTED", "Missing, duplicate or unknown principal packages: " + row["id"])
        require(isinstance(obligations, list)
                and all(isinstance(x, str) and bool(x.strip()) for x in obligations),
                "SCOPE_MANIFEST_REJECTED", "Open obligations must be explicit text entries.")
        if status.startswith("OPEN"):
            require(row.get("root_declaration") is None and bool(obligations),
                    "SCOPE_MANIFEST_REJECTED", "An open root must remain absent and have named obligations.")
        elif status.startswith("CONDITIONAL"):
            require(isinstance(row.get("root_declaration"), str) and bool(row["root_declaration"])
                    and bool(obligations), "SCOPE_MANIFEST_REJECTED",
                    "A conditional reduction needs its theorem and retained obligations.")
        else:
            require(isinstance(row.get("root_declaration"), str) and bool(row["root_declaration"])
                    and not obligations, "SCOPE_MANIFEST_REJECTED",
                    "An established exact root needs a named theorem with its exact completed scope.")
        require(row["standalone_qfb"] == (row["id"] == "QFB"),
                "SCOPE_MANIFEST_REJECTED", "The QFB lane alone owns the additional standalone QFB audit.")
    return {row["id"]: row for row in rows}


def select_scope(entries: list[dict], goal: dict) -> list[str]:
    by_id = {entry["id"]: entry for entry in entries}
    principal = set(goal["principal_packages"])
    modules = {record["module"] for identifier in principal for record in by_id[identifier]["files"]}
    dependency_packages = {entry["id"] for entry in entries
                           if entry["spec"].get("imports")
                           and set(entry["spec"]["imports"]) <= modules}
    return sorted(principal | dependency_packages)


def root_contract(goal: dict, selected_entries: list[dict]) -> dict:
    declarations: dict[str, list[tuple[str, str]]] = {}
    for entry in selected_entries:
        for declaration in entry["spec"]["declarations"]:
            declarations.setdefault(declaration["name"], []).append((entry["id"], declaration.get("kind")))
    root_name = goal.get("root_declaration")
    if root_name is not None:
        matches = declarations.get(root_name, [])
        require(bool(matches) and all(kind == "theorem" for _, kind in matches),
                "SCOPE_MANIFEST_REJECTED", "The configured root is absent or is not a theorem declaration.")
    target = goal.get("target_definition")
    if target is not None:
        matches = declarations.get(target, [])
        require(target != root_name and bool(matches) and all(kind == "definition" for _, kind in matches),
                "SCOPE_MANIFEST_REJECTED", "A target proposition must be audited as a definition, never as a proved root.")
    if goal["id"] == "QFA":
        require(isinstance(target, str) and bool(target), "SCOPE_MANIFEST_REJECTED",
                "The QFA lane must retain its separately named target proposition definition.")
    return {"root_declaration": root_name,
            "root_packages": [package for package, _ in declarations.get(root_name, [])],
            "target_definition": target,
            "target_definition_packages": [package for package, _ in declarations.get(target, [])],
            "target_definition_is_proof": False}


def make_plan(root: Path, goal_id: str, revision: str, route: dict, drivers) -> tuple[dict, dict]:
    build, native, registry = drivers
    full = build.validate(root / "Material")
    require(all(not e["source_drift"] for e in full["endpoints"]),
            "SOURCE_DRIFT", "A registered source differs from its retained manifest.")
    manifest_path = root / "Material/ci/theorem-goals.json"
    manifest = read_object(manifest_path)
    goals = validate_manifest(manifest, full["endpoints"])
    goal = goals[goal_id]
    ids = select_scope(full["endpoints"], goal)
    selected = build.validate(root / "Material", ids)
    contract = root_contract(goal, selected["endpoints"])
    records = native.local_records(selected)
    names = [declaration["name"] for entry in selected["endpoints"]
             for declaration in entry["spec"]["declarations"]]
    plan = {"schema_version": 1, "repository": REPOSITORY, "goal": goal,
            "source_revision": revision, "route": route, "report_scope": "goal_only",
            "all_project_endpoints_verified_by_this_job": False,
            "selected_packages": ids, "selected_package_count": len(ids),
            "principal_package_count": len(goal["principal_packages"]),
            "required_named_reports": len(names), "unique_declaration_count": len(set(names)),
            "selected_module_count": len(records), "root_contract": contract,
            "toolchain": selected["toolchain"], "mathlib_commit": selected["mathlib_commit"],
            "build_configuration": selected["config"],
            "endpoint_input_hashes": {e["id"]: e["input_plan_hash"] for e in selected["endpoints"]},
            "source_closure_sha256": fingerprint([records[name] for name in sorted(records)]),
            "audit_policy_sha256": fingerprint({e["id"]: e["spec"] for e in selected["endpoints"]}),
            "source_manifest_sha256": digest((root / "Material/_vendor/source-manifest.json").read_bytes()),
            "owned_source_manifest_sha256": digest((root / "Material/owned-sources.json").read_bytes()),
            "goal_manifest_sha256": digest(manifest_path.read_bytes()),
            "orchestrator_sha256": digest(Path(__file__).read_bytes()),
            "canonical_cache_keys": registry.cache_keys(root),
            "fresh_required_audits": True, "module_compilation_allowed": False,
            "dependency_hydration_allowed": False, "cache_publication_allowed": False,
            "local_lean_allowed": False, "root_status_automatically_promoted": False}
    plan["plan_sha256"] = fingerprint(plan)
    return plan, selected


def check_stored_plan(output: Path, plan: dict) -> None:
    require(read_object(output / "scope-plan.json") == plan,
            "INPUT_CHANGED", "The routed source, scope or verifier inputs changed after planning.")


def check_cache_flags(plan: dict, environment: dict[str, str]) -> dict:
    keys = plan["canonical_cache_keys"]
    dependency = environment.get("DEPENDENCY_MATCHED", "")
    project = environment.get("PROJECT_MATCHED", "")
    require(environment.get("DEPENDENCY_HIT") == "true" and bool(project),
            "CACHE_SCOPE_NOT_READY", "Exact compatible dependencies and a passed project cache are required.")
    require(dependency == keys["dependency_key"] or dependency.startswith(keys["dependency_key"] + "-recovered-"),
            "CACHE_SCOPE_NOT_READY", "The dependency cache is outside the pinned compatibility identity.")
    require(project.startswith(keys["project_prefix"]), "CACHE_SCOPE_NOT_READY",
            "The project cache is outside the pinned compatibility identity.")
    return {"dependency_cache_class": "EXACT", "dependency_matched_key": dependency,
            "project_cache_class": "EXACT" if environment.get("PROJECT_HIT") == "true" else "PREFIX",
            "project_matched_key": project}


def validate_donor(donor: dict, plan: dict) -> None:
    require(donor.get("status") == "PASS" and donor.get("repository") == REPOSITORY
            and donor.get("compiler_executed") is True
            and donor.get("all_endpoints_selected") is True
            and donor.get("fresh_required_audits") is True
            and donor.get("source_pin_integrity") is True
            and bool(SHA.fullmatch(str(donor.get("commit", ""))))
            and donor.get("toolchain") == plan["toolchain"]
            and donor.get("mathlib_commit") == plan["mathlib_commit"]
            and donor.get("build_configuration") == plan["build_configuration"],
            "CACHE_SCOPE_NOT_READY", "A complete compatible canonical PASS report is required.")
    run_id = str(donor.get("run_id", ""))
    require(run_id.isdigit() and donor.get("run_url") == f"https://github.com/{REPOSITORY}/actions/runs/{run_id}",
            "CACHE_SCOPE_NOT_READY", "The donor source/run provenance is incomplete.")
    receipts = donor.get("module_receipts")
    endpoints = donor.get("endpoints")
    require(isinstance(receipts, dict) and bool(receipts)
            and all(isinstance(r, dict) and r.get("status") == "PASS" for r in receipts.values())
            and isinstance(endpoints, list) and bool(endpoints)
            and all(isinstance(e, dict) for e in endpoints)
            and len({e.get("id") for e in endpoints}) == len(endpoints),
            "CACHE_SCOPE_NOT_READY", "The full donor report has incomplete module or endpoint evidence.")
    for record in endpoints + [donor.get("cutout", {})]:
        require(record.get("status") == "PASS" and record.get("audit_reused") is False
                and record.get("audit_origin_commit") == donor["commit"]
                and isinstance(record.get("types"), dict) and bool(record["types"])
                and isinstance(record.get("axioms"), dict)
                and set(record["types"]) == set(record["axioms"]),
                "CACHE_SCOPE_NOT_READY", "The donor lacks complete fresh named audit evidence.")
        require(all(isinstance(axioms, list) and set(axioms) <= STANDARD_AXIOMS
                    for axioms in record["axioms"].values()),
                "CACHE_SCOPE_NOT_READY", "A donor declaration has an unapproved axiom.")
        if record is not donor.get("cutout"):
            require(record.get("declaration_count") == len(record["types"]),
                    "CACHE_SCOPE_NOT_READY", "The donor package report count is inconsistent.")


def validate_receipts(records: dict, old: dict, context: dict, output: Path, receipt_matches) -> dict:
    """Pure file/receipt inspection: no subprocess, migration or object writes."""
    pending, verified = set(records), {}
    while pending:
        ready = sorted(name for name in pending if not any(i in pending for i in records[name]["imports"]))
        require(bool(ready), "CACHE_SCOPE_NOT_READY", "The selected local import closure is cyclic.")
        for name in ready:
            pending.remove(name)
            dependencies = {i: verified[i] for i in records[name]["imports"] if i in records}
            identity = fingerprint({"context": context, "source": records[name]["sha256"],
                                    "module": name, "imports": {
                                        i: {"identity": record["identity"], "objects": record["object_files"]}
                                        for i, record in dependencies.items()}})
            artifact = output.joinpath(*name.split(".")).with_suffix(".olean")
            require(artifact.resolve().is_relative_to(output.resolve())
                    and not any(p.is_symlink() for p in (artifact, *artifact.parents)),
                    "CACHE_SCOPE_NOT_READY", "A selected cached object escapes its object directory.")
            require(not any(p.is_symlink() for p in artifact.parent.glob(artifact.name + "*")),
                    "CACHE_SCOPE_NOT_READY", "A cached object companion is a symlink.")
            receipt = old.get(name)
            require(isinstance(receipt, dict) and receipt.get("status") == "PASS"
                    and receipt_matches(receipt, identity, artifact),
                    "CACHE_SCOPE_NOT_READY", "Missing or mismatched source/import/object receipt: " + name)
            verified[name] = receipt
    return verified


def cached_preflight(root: Path, plan: dict, selected: dict, environment: dict[str, str], drivers) -> tuple[dict, dict, dict]:
    """Reject stale objects before compiler setup/probing or any fresh audit."""
    _, native, _ = drivers
    cache = check_cache_flags(plan, environment)
    report_path = root / "Material/registry/current.json"
    require(report_path.is_file() and not report_path.is_symlink(), "CACHE_SCOPE_NOT_READY",
            "The restored canonical PASS report is absent.")
    raw = report_path.read_bytes()
    donor = json.loads(raw)
    require(isinstance(donor, dict), "CACHE_SCOPE_NOT_READY", "The donor report is not an object.")
    validate_donor(donor, plan)
    compiler = donor.get("compiler")
    expected_version = plan["toolchain"].rsplit(":v", 1)[-1]
    require(isinstance(compiler, str)
            and bool(re.search(r"\bversion\s+" + re.escape(expected_version) + r"(?:,|\s|\))", compiler)),
            "CACHE_SCOPE_NOT_READY", "The donor compiler differs from the pinned version.")
    external = native.dependency_outputs(root / "Material")
    context = {"compiler": compiler,
               "lock": digest((root / "Material/lake-manifest.json").read_bytes()),
               "configuration": plan["build_configuration"],
               "driver": digest((root / "Material/ci/native_build.py").read_bytes()),
               "receipt_adapter": digest((root / "Material/ci/receipt_compatibility.py").read_bytes()),
               "launcher_policy": digest((root / "Material/ci/verify-external.sh").read_bytes()),
               "external_objects": external,
               "platform": {"system": platform.system(), "machine": platform.machine()}}
    require(context["platform"] == {"system": "Linux", "machine": "x86_64"}
            and donor.get("compile_context") == context
            and donor.get("external_objects") == external and donor.get("platform") == context["platform"],
            "CACHE_SCOPE_NOT_READY", "Canonical compiler/dependency/driver context is not an exact match; no migration is allowed.")
    records = native.local_records(selected)
    verified = validate_receipts(records, donor["module_receipts"], context,
                                 root / "Material/.lake/build/lib/lean", native.receipt_matches)
    admission = {"schema_version": 1, "status": "ADMITTED_CACHED_SCOPE", "plan_sha256": plan["plan_sha256"],
                 "source_revision": plan["source_revision"], "goal_id": plan["goal"]["id"],
                 "donor_source_revision": donor["commit"], "donor_run_url": donor["run_url"],
                 "donor_report_sha256": digest(raw), "verified_module_count": len(verified),
                 "canonical_context_sha256": fingerprint(context), "external_objects": external,
                 "compiler_executed": False, "module_compilation_allowed": False, **cache}
    return admission, donor, context


def base_report(plan: dict) -> dict:
    goal = plan["goal"]
    return {"schema_version": 1, "repository": REPOSITORY, "report_scope": "goal_only",
            "goal_id": goal["id"], "goal_name": goal["name"], "domain": goal["domain"],
            "source_revision": plan["source_revision"], "route": plan["route"],
            "plan_sha256": plan["plan_sha256"], "audit_status": "NOT_STARTED",
            "root_status": goal["root_status"], "root_declaration": goal.get("root_declaration"),
            "target_definition": goal.get("target_definition"), "target_definition_is_proof": False,
            "verification_scope": goal["verification_scope"], "open_obligations": goal["open_obligations"],
            "root_status_automatically_promoted": False, "full_project_acceptance": False,
            "root_status_source": "Explicit checked-in goal manifest; never inferred from audit success.",
            "selected_packages": plan["selected_packages"], "required_package_count": plan["selected_package_count"],
            "required_named_reports": plan["required_named_reports"], "endpoints": [],
            "fresh_required_audits": True, "compiler_executed": False,
            "module_compilation_allowed": False, "cache_publication_allowed": False,
            "local_lean_allowed": False, "orchestrator_sha256": plan["orchestrator_sha256"],
            "audit_policy_sha256": plan["audit_policy_sha256"],
            "source_closure_sha256": plan["source_closure_sha256"]}


def verify_goal(root: Path, output: Path, plan: dict, selected: dict,
                environment: dict[str, str], drivers, report: dict) -> dict:
    build, _, _ = drivers
    started = time.monotonic()
    admission, donor, context = cached_preflight(root, plan, selected, environment, drivers)
    require(read_object(output / "cache-admission.json") == admission,
            "INPUT_CHANGED", "The admitted donor cache or selected source changed before verification.")
    report.update(cache_admission=admission, donor_source_revision=donor["commit"], donor_run_url=donor["run_url"])
    material, logs = root / "Material", output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    report["failure_phase"] = "dependency_identity"
    verified_dependencies = build.verify_dependencies(material, selected["dependency_lock"], environment, logs, True)
    required_mathlib = sorted({module for entry in selected["endpoints"] for module in entry["external_imports"]
                              if module == "Mathlib" or module.startswith("Mathlib.")})
    dependency_env = dict(environment, MATERIAL_RESTORE_MODE="actions_passed_cache")
    ready, reason = build.retained_dependency_cache_ready(material, selected, donor, required_mathlib,
                                                         verified_dependencies, dependency_env)
    require(ready, "CACHE_SCOPE_NOT_READY", "Required official dependency objects are unavailable: " + reason)
    report["verified_dependencies"] = verified_dependencies
    report["failure_phase"] = "compiler_identity"
    report["compiler_executed"] = True
    compiler, _ = build.execute(["lake", "env", "lean", "--version"], material, logs / "compiler-version.log", environment)
    require(compiler.strip() == context["compiler"], "COMPILER_IDENTITY_MISMATCH",
            "The freshly queried compiler does not match the receipt-bound compiler.")
    report["compiler"] = compiler.strip()
    report["canonical_compile_context"] = context
    report["module_workers"] = 0
    report["audit_workers"] = 2
    require(environment.get("LEAN_NUM_THREADS", "2") == "2", "AUDIT_POLICY_MISMATCH",
            "The scoped audit lane retains two Lean threads.")
    audit_env = dict(environment, LEAN_NUM_THREADS="2")
    report["failure_phase"] = "fresh_audits"

    def audit(entry):
        identifier = entry["id"]
        identity = fingerprint({"input": entry["input_plan_hash"], "compiler": compiler.strip(),
                                "context": context, "orchestrator": plan["orchestrator_sha256"]})
        log = logs / (identifier + "-" + identity + ".log")
        record = {"id": identifier, "status": "FAIL", "audit_reused": False,
                  "audit_origin_commit": plan["source_revision"], "input_hash": identity,
                  "audit_log": log.relative_to(output).as_posix(),
                  "declaration_count": len(entry["spec"]["declarations"])}
        try:
            text, seconds = build.execute(["lake", "env", "lean", identifier + "/Audit.lean"],
                                           material, log, audit_env)
            parsed = build.parse_audit(text, [d["name"] for d in entry["spec"]["declarations"]],
                                       set(entry["spec"]["allowed_axioms"]))
            record.update(status="PASS", audit_seconds=seconds, audit_sha256=digest(log.read_bytes()), **parsed)
        except Exception as exc:
            record["error"] = str(exc)
            if log.is_file():
                record["audit_sha256"] = digest(log.read_bytes())
        return record

    with ThreadPoolExecutor(max_workers=2) as pool:
        report["endpoints"] = list(pool.map(audit, selected["endpoints"]))
    if plan["goal"]["standalone_qfb"]:
        source, log = root / "LEAN_CUTOUTS/Cutouts.lean", logs / "standalone-qfb.log"
        record = {"status": "FAIL", "audit_reused": False, "audit_origin_commit": plan["source_revision"],
                  "audit_log": log.relative_to(output).as_posix(), "source_sha256": digest(source.read_bytes())}
        try:
            text, seconds = build.execute(["lake", "env", "lean", "--root=" + str(root), str(source)],
                                           material, log, audit_env)
            parsed = build.parse_audit(text, ["QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED"])
            record.update(status="PASS", audit_seconds=seconds, audit_sha256=digest(log.read_bytes()), **parsed)
        except Exception as exc:
            record["error"] = str(exc)
            if log.is_file():
                record["audit_sha256"] = digest(log.read_bytes())
        report["standalone_qfb"] = record
    require(len(report["endpoints"]) == plan["selected_package_count"]
            and [e["id"] for e in report["endpoints"]] == plan["selected_packages"],
            "AUDIT_COVERAGE_MISMATCH", "Scoped package coverage differs from the planned package set.")
    passed = [e for e in report["endpoints"] if e["status"] == "PASS"]
    report["fresh_package_count"] = len(passed)
    report["fresh_named_reports"] = sum(len(e["types"]) for e in passed)
    report["audit_reused_count"] = 0
    all_passed = len(passed) == plan["selected_package_count"]
    all_passed = all_passed and (not plan["goal"]["standalone_qfb"] or report["standalone_qfb"]["status"] == "PASS")
    require(not all_passed or report["fresh_named_reports"] == plan["required_named_reports"],
            "AUDIT_COVERAGE_MISMATCH", "Fresh named report coverage is incomplete.")
    # No project module or canonical report may change during an audit-only run.
    check_checkout(root, plan["source_revision"], environment)
    current_plan, _ = make_plan(root, plan["goal"]["id"], plan["source_revision"], plan["route"], drivers)
    require(current_plan == plan, "INPUT_CHANGED", "The checked source/scope changed during fresh audits.")
    final_admission, _, _ = cached_preflight(root, plan, selected, environment, drivers)
    require(final_admission == admission, "INPUT_CHANGED", "The original donor report or receipt-bound objects changed during auditing.")
    root_name = plan["goal"].get("root_declaration")
    report["root_declaration_freshly_audited"] = bool(root_name) and all_passed and any(
        root_name in e["types"] for e in passed)
    report["audit_status"] = "PASS" if all_passed else "FAIL"
    if all_passed:
        report.pop("failure_phase", None)
    else:
        report["failure_class"] = "FRESH_AUDIT_FAILED"
        report["error"] = "At least one required fresh exact-type/axiom audit failed; see the individual logs."
    report["total_seconds"] = round(time.monotonic() - started, 3)
    return report


def append_summary(report: dict, environment: dict[str, str]) -> None:
    path = environment.get("GITHUB_STEP_SUMMARY")
    if not path:
        return
    lines = ["", "## " + report.get("goal_id", "Unknown goal") + " — scoped verification", "",
             "| Field | Result |", "|---|---|",
             "| Audit result | " + report.get("audit_status", "NOT_STARTED") + " |",
             "| Mathematical root status | " + report.get("root_status", "UNRESOLVED") + " |",
             "| Exact checked source | `" + report.get("source_revision", "unknown") + "` |",
             "| Fresh packages / named reports | " + str(report.get("fresh_package_count", 0)) +
             " / " + str(report.get("fresh_named_reports", 0)) + " |", "",
             report.get("verification_scope", "No mathematical scope was accepted."), "",
             "Audit success verifies this configured scope. It does not construct an absent root, "
             "discharge a retained premise, or replace complete Material acceptance."]
    if report.get("donor_source_revision"):
        lines += ["", "Object donor: `" + report["donor_source_revision"] + "` — " + report["donor_run_url"] + "."]
    if report.get("error"):
        lines += ["", "Failure: " + str(report.get("failure_class", "VERIFICATION_FAILURE")) +
                  " — " + str(report["error"]).replace("\n", " ")]
    if report.get("open_obligations"):
        lines += ["", "Remaining obligations:", ""] + ["- " + x for x in report["open_obligations"]]
    with Path(path).open("a", encoding="utf-8") as stream:
        stream.write("\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("plan", "admit", "verify"))
    parser.add_argument("--goal", choices=GOAL_IDS, required=True)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--github-output", type=Path)
    args = parser.parse_args()
    environment = dict(os.environ)
    output = None
    report = {"schema_version": 1, "goal_id": args.goal, "source_revision": args.revision,
              "audit_status": "NOT_STARTED", "root_status_automatically_promoted": False,
              "full_project_acceptance": False, "compiler_executed": False,
              "local_lean_allowed": False}
    try:
        # Refuse local execution before creating any artifacts or loading drivers.
        external_envelope(environment)
        root = ROOT.resolve()
        output = args.output.resolve()
        require(not output.is_relative_to(root) and not root.is_relative_to(output),
                "OUTPUT_PATH_REJECTED", "Scoped evidence must be outside the checked-out repository.")
        output.mkdir(parents=True, exist_ok=True)
        event = read_object(Path(environment["GITHUB_EVENT_PATH"]))
        route = validate_route(environment, event, args.revision)
        check_checkout(root, args.revision, environment)
        drivers = load_drivers(root)
        plan, selected = make_plan(root, args.goal, args.revision, route, drivers)
        report = base_report(plan)
        if args.command == "plan":
            atomic_json(output / "scope-plan.json", plan)
            if args.github_output:
                values = {**plan["canonical_cache_keys"], "source_revision": args.revision,
                          "goal_id": args.goal, "selected_package_count": str(plan["selected_package_count"]),
                          "required_named_reports": str(plan["required_named_reports"]),
                          "plan_sha256": plan["plan_sha256"]}
                with args.github_output.open("a", encoding="utf-8") as stream:
                    for key, value in values.items():
                        require("\n" not in value and "\r" not in value, "OUTPUT_VALUE_REJECTED", "Invalid workflow output value.")
                        stream.write(f"{key}={value}\n")
        else:
            check_stored_plan(output, plan)
            if args.command == "admit":
                admission, _, _ = cached_preflight(root, plan, selected, environment, drivers)
                atomic_json(output / "cache-admission.json", admission)
                report["cache_admission"] = admission
            else:
                report = verify_goal(root, output, plan, selected, environment, drivers, report)
                append_summary(report, environment)
        atomic_json(output / "scope-report.json", report)
        print(json.dumps({"goal": args.goal, "stage": args.command, "audit_status": report["audit_status"],
                          "root_status": report["root_status"], "source_revision": args.revision}, sort_keys=True))
        return 1 if report["audit_status"] == "FAIL" else 0
    except Exception as exc:
        report.update(audit_status="FAIL", failure_class=getattr(exc, "code", "SCOPED_VERIFICATION_FAILURE"),
                      failure_phase=report.get("failure_phase", args.command), error=str(exc))
        if (output is not None and output.is_dir() and not output.is_relative_to(ROOT.resolve())
                and not ROOT.resolve().is_relative_to(output)):
            atomic_json(output / "scope-report.json", report)
            append_summary(report, environment)
        print("THEOREM_GOAL_FAILURE " + json.dumps(report, sort_keys=True), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
