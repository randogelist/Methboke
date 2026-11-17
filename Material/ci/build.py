#!/usr/bin/env python3
"""Exact-source Material build/audit driver. Lean runs only in CI or native Windows.

--validate-only is a pure filesystem validation: no subprocess, Lean, Lake, git,
network, compiler, cache retrieval or theorem-status promotion is performed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXTERNAL_PREFIXES = frozenset({
    "Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "ImportGraph", "LeanSearchClient", "Plausible",
})
SENTINEL_PREFIXES = ("TYPE_BEGIN:", "TYPE_END:", "AXIOMS_BEGIN:", "AXIOMS_END:")
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


class BuildError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint(value: object) -> str:
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def atomic_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def read_json(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise BuildError(f"expected JSON object: {path.name}")
    return value


def inside(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise BuildError(f"path escapes Material: {relative}")
    return path


def strip_lean_comments(text: str) -> str:
    """Remove nested comments and string contents while preserving line positions."""
    result: list[str] = []
    pos = 0
    depth = 0
    string = False
    while pos < len(text):
        pair = text[pos:pos + 2]
        char = text[pos]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                pos += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                pos += 1
        elif string:
            if char == "\\" and pos + 1 < len(text):
                result.extend("  ")
                pos += 2
            else:
                result.append("\n" if char == "\n" else " ")
                string = char != '"'
                pos += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            pos += 2
        elif pair == "--":
            end = text.find("\n", pos)
            if end == -1:
                result.extend(" " * (len(text) - pos))
                break
            result.extend(" " * (end - pos))
            pos = end
        elif char == '"':
            string = True
            result.append(" ")
            pos += 1
        else:
            result.append(char)
            pos += 1
    if depth or string:
        raise BuildError("unterminated Lean comment/string in current source")
    return "".join(result)


def lean_imports(text: str) -> list[str]:
    result: list[str] = []
    for line in strip_lean_comments(text).splitlines():
        match = re.match(r"^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$", line)
        if not match:
            continue
        for name in match.group(1).split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
                raise BuildError(f"unsupported import token: {name}")
            result.append(name)
    return result


def module_index(root: Path) -> dict[str, Path]:
    result: dict[str, Path] = {}
    for path in root.rglob("*.lean"):
        parts = path.relative_to(root).parts
        if any(x in {".lake", ".standalone", "registry", "tests", "provenance", "ci"}
               for x in parts):
            continue
        if path.name == "lakefile.lean":
            continue
        logical = parts[1:] if parts[0] == "_vendor" else parts
        name = ".".join((*logical[:-1], Path(logical[-1]).stem))
        if name in result:
            raise BuildError(f"duplicate module name: {name}")
        resolved = path.resolve()
        if not resolved.is_relative_to(root.resolve()):
            raise BuildError(f"source symlink escapes Material: {path}")
        result[name] = path
    return result


def current_closure(root: Path, index: dict[str, Path], roots: list[str],
                    baseline: dict[str, dict]) -> tuple[list[dict], list[str], list[dict]]:
    pending = list(roots)
    seen: set[str] = set()
    external: set[str] = set()
    records: list[dict] = []
    drift: list[dict] = []
    while pending:
        name = pending.pop()
        if name in seen or name in external:
            continue
        if name not in index:
            if name.split(".", 1)[0] in EXTERNAL_PREFIXES:
                external.add(name)
                continue
            raise BuildError(f"missing current local import: {name}")
        seen.add(name)
        path = index[name]
        data = path.read_bytes()
        text = data.decode("utf-8")
        imports = lean_imports(text)
        pending.extend(imports)
        item = {"module": name, "path": str(path.relative_to(root)).replace("\\", "/"),
                "sha256": sha256(data), "imports": imports}
        records.append(item)
        if item["path"].startswith("_vendor/"):
            old = baseline.get(name)
            expected = None if old is None else old["sha256"]
            if expected != item["sha256"]:
                drift.append({"module": name, "path": item["path"],
                              "baseline_sha256": expected, "current_sha256": item["sha256"]})
    return (sorted(records, key=lambda x: x["module"]), sorted(external),
            sorted(drift, key=lambda x: x["module"]))


def parse_audit(text: str, names: list[str], allowed: set[str] | frozenset[str] = STANDARD_AXIOMS) -> dict:
    if not allowed.issubset(STANDARD_AXIOMS):
        raise BuildError("endpoint manifest may not widen the standard axiom allowlist")
    clean = ANSI.sub("", text).replace("\r\n", "\n")
    if re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror\s*:", clean, re.I):
        raise BuildError("compiler/audit output contains an error or sorry admission")
    if not names or len(set(names)) != len(names):
        raise BuildError("nonempty unique declaration list required")
    lines = clean.splitlines()
    found = [line.strip() for line in lines if line.strip().startswith(SENTINEL_PREFIXES)]
    expected = [prefix + name for name in names for prefix in SENTINEL_PREFIXES]
    if found != expected:
        raise BuildError("missing, duplicate, reordered or unexpected audit sentinel")
    types: dict[str, str] = {}
    axioms: dict[str, list[str]] = {}
    cursor = 0
    for name in names:
        positions: list[int] = []
        for prefix in SENTINEL_PREFIXES:
            target = prefix + name
            position = next((i for i in range(cursor, len(lines)) if lines[i].strip() == target), -1)
            if position < 0:
                raise BuildError(f"audit sentinel absent: {target}")
            positions.append(position)
            cursor = position + 1
        ty = "\n".join(line.rstrip() for line in lines[positions[0] + 1:positions[1]]).strip()
        if not ty or ":" not in ty or name not in ty:
            raise BuildError(f"empty or unidentified exact type record: {name}")
        body = "\n".join(lines[positions[2] + 1:positions[3]]).strip()
        escaped = re.escape(name)
        none = re.fullmatch(r"'" + escaped + r"'\s+does not depend on any axioms\.?", body)
        some = re.fullmatch(r"'" + escaped + r"'\s+depends on axioms:\s*\[([^\]]*)\]", body, re.S)
        if none:
            deps: list[str] = []
        elif some:
            deps = [x.strip() for x in some.group(1).split(",") if x.strip()]
        else:
            raise BuildError(f"invalid axiom record: {name}")
        unapproved = set(deps) - set(allowed)
        if unapproved:
            raise BuildError(f"unapproved axioms for {name}: {sorted(unapproved)}")
        types[name] = ty
        axioms[name] = sorted(set(deps))
    return {"types": types, "axioms": axioms}


def validate(root: Path, selected: list[str] | None = None) -> dict:
    root = root.resolve()
    source_manifest = read_json(root / "_vendor/source-manifest.json")
    baseline = {item["module"]: item for item in source_manifest["files"]}
    for item in baseline.values():
        path = inside(root, item.get("local_path", item.get("path", "")))
        if not path.is_file():
            raise BuildError(f"missing retained source: {item['module']}")
    config_paths = ["lean-toolchain", "lake-manifest.json", "ci/build.py"]
    config_paths.append("lakefile.lean" if (root / "lakefile.lean").exists() else "lakefile.toml")
    config = {path: sha256((root / path).read_bytes()) for path in config_paths}
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != source_manifest["lean_toolchain"]:
        raise BuildError("toolchain differs from retained source manifest")
    lock = read_json(root / "lake-manifest.json")
    mathlib = [p for p in lock.get("packages", []) if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != source_manifest["mathlib_commit"]:
        raise BuildError("mathlib dependency lock does not match the retained source pin")
    index = module_index(root)
    available = {p.parent.name: p for p in root.glob("*/endpoint.json")}
    identifiers = sorted(available) if not selected else sorted(set(selected))
    if not identifiers or set(identifiers) - set(available):
        raise BuildError("unknown endpoint or empty endpoint selection")
    entries: list[dict] = []
    for identifier in identifiers:
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", identifier):
            raise BuildError("endpoint identifier is not a simple Lean namespace")
        spec_path = available[identifier]
        spec = read_json(spec_path)
        if spec.get("id") != identifier:
            raise BuildError(f"endpoint id/path mismatch: {identifier}")
        for field, suffix in (("endpoint_module", ".Endpoint"), ("audit_module", ".Audit")):
            if spec.get(field) != identifier + suffix:
                raise BuildError(f"unexpected endpoint module identity: {identifier}")
        allowed = set(spec.get("allowed_axioms", []))
        if not allowed or not allowed.issubset(STANDARD_AXIOMS):
            raise BuildError(f"invalid axiom policy: {identifier}")
        names = [x["name"] for x in spec.get("declarations", [])]
        if not names or len(names) != len(set(names)):
            raise BuildError(f"empty/duplicate declaration list: {identifier}")
        direct = lean_imports((root / identifier / "Endpoint.lean").read_text(encoding="utf-8"))
        if direct != spec.get("imports"):
            raise BuildError(f"endpoint imports differ from endpoint.json: {identifier}")
        files, external, drift = current_closure(
            root, index, [spec["endpoint_module"], spec["audit_module"]], baseline)
        audit = (root / identifier / "Audit.lean").read_text(encoding="utf-8")
        for name in names:
            for prefix in SENTINEL_PREFIXES:
                if audit.count('"' + prefix + name + '"') != 1:
                    raise BuildError(f"audit source lacks unique sentinel: {identifier}:{name}")
        payload = {"id": identifier, "config": config, "files": files,
                   "spec_sha256": sha256(spec_path.read_bytes()), "external_imports": external,
                   "platform": {"system": platform.system(), "machine": platform.machine()}}
        entries.append({"id": identifier, "spec": spec, "input_plan_hash": fingerprint(payload),
                        "files": files, "external_imports": external, "source_drift": drift})
    return {"toolchain": toolchain, "mathlib_commit": source_manifest["mathlib_commit"],
            "config": config, "dependency_lock": lock, "endpoints": entries,
            "all_endpoint_ids": sorted(available)}


def execute(command: list[str], root: Path, log_path: Path, environment: dict[str, str]) -> tuple[str, float]:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    print("MATERIAL_COMMAND " + json.dumps(command), flush=True)
    started = time.monotonic()
    timeout = int(environment.get("MATERIAL_COMMAND_TIMEOUT", "7200"))
    result = subprocess.run(command, cwd=root, env=environment, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    output = result.stdout or ""
    log_path.write_text(output, encoding="utf-8")
    if output:
        print(output, end="" if output.endswith("\n") else "\n", flush=True)
    elapsed = round(time.monotonic() - started, 3)
    if result.returncode:
        raise BuildError(f"command exited {result.returncode}; evidence: {log_path.name}")
    if re.search(r"\bwarning\s*:.*\bsorry\b|\bsorryAx\b", output, re.I):
        raise BuildError(f"sorry admission in compiler output: {log_path.name}")
    return output, elapsed


def verify_dependencies(root: Path, lock: dict, environment: dict[str, str], logs: Path,
                        require_all: bool) -> list[dict]:
    result = []
    for package in lock.get("packages", []):
        if package.get("type") != "git":
            raise BuildError(f"unapproved non-git dependency lock entry: {package.get('name')}")
        name = package["name"]
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", name):
            raise BuildError("invalid locked package name")
        path = root / ".lake/packages" / name
        if not path.exists() and not require_all:
            continue
        if not path.is_dir():
            raise BuildError(f"locked dependency missing after cache hydration: {name}")
        head, _ = execute(["git", "-C", str(path), "rev-parse", "HEAD"], root,
                          logs / ("pin-" + name + ".log"), environment)
        if head.strip() != package["rev"]:
            raise BuildError(f"locked dependency commit mismatch: {name}")
        status, _ = execute(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"],
                            root, logs / ("source-status-" + name + ".log"), environment)
        if status.strip():
            raise BuildError(f"locked dependency has modified tracked sources: {name}")
        result.append({"name": name, "commit": head.strip(), "tracked_source_clean": True})
    return result


def reuse_audit(root: Path, old: dict | None, entry: dict, input_hash: str) -> dict | None:
    if not old or old.get("status") != "PASS" or old.get("input_hash") != input_hash:
        return None
    expected = f"registry/audits/{entry['id']}-{input_hash}.log"
    if old.get("audit_log") != expected:
        return None
    path = inside(root, expected)
    if not path.is_file() or sha256(path.read_bytes()) != old.get("audit_sha256"):
        return None
    try:
        parsed = parse_audit(path.read_text(encoding="utf-8"),
                             [x["name"] for x in entry["spec"]["declarations"]],
                             set(entry["spec"]["allowed_axioms"]))
    except BuildError:
        return None
    return {**parsed, "audit_log": expected, "audit_sha256": old["audit_sha256"],
            "audit_reused": True, "audit_origin_commit": old.get("audit_origin_commit", old.get("commit"))}


def run_build(root: Path, report_path: Path, selected: list[str] | None, native: bool,
              validate_only: bool, environment: dict[str, str] | None = None) -> int:
    environment = dict(os.environ if environment is None else environment)
    report: dict = {"schema_version": 1, "status": "FAIL", "endpoints": [],
                    "started_at": datetime.now(timezone.utc).isoformat(),
                    "new_finite_cap_theorem_included": False}
    started = time.monotonic()
    try:
        plan = validate(root, selected)
        supplied_commit = environment.get("GITHUB_SHA") or environment.get("MATERIAL_SOURCE_COMMIT")
        if supplied_commit and not re.fullmatch(r"[0-9a-fA-F]{40}", supplied_commit):
            raise BuildError("source commit environment must contain an exact 40-character SHA")
        report["commit"] = supplied_commit or "local:" + fingerprint(
            [x["input_plan_hash"] for x in plan["endpoints"]])
        report.update(toolchain=plan["toolchain"], mathlib_commit=plan["mathlib_commit"],
                      selected_endpoint_ids=[x["id"] for x in plan["endpoints"]],
                      all_endpoints_selected=sorted(x["id"] for x in plan["endpoints"]) == plan["all_endpoint_ids"],
                      platform={"system": platform.system(), "machine": platform.machine()},
                      source_pin_integrity=all(not x["source_drift"] for x in plan["endpoints"]))
        if validate_only:
            report.update(status="VALIDATED_ONLY", compiler_executed=False,
                          endpoint_plans=[{k: e[k] for k in ("id", "input_plan_hash", "source_drift")}
                                          for e in plan["endpoints"]])
            # Validation must not overwrite the last passed evidence by default.
            print(json.dumps(report, indent=2))
            return 0
        if native:
            if platform.system() != "Windows":
                raise BuildError("--native execution is reserved for the user's external native Windows compiler")
        elif environment.get("CI", "").lower() != "true":
            raise BuildError("Lean execution requires external CI=true or explicit --native on Windows")
        previous: dict = {}
        if report_path.is_file():
            try:
                previous = read_json(report_path)
            except (ValueError, OSError, BuildError):
                previous = {}
        old_entries = ({x.get("id"): x for x in previous.get("endpoints", []) if isinstance(x, dict)}
                       if previous.get("status") == "PASS" else {})
        jobs = environment.get("MATERIAL_JOBS", "2")
        if not jobs.isdigit() or not 1 <= int(jobs) <= 4:
            raise BuildError("MATERIAL_JOBS must be between 1 and 4")
        environment["LEAN_NUM_THREADS"] = jobs
        report["lean_num_threads"] = int(jobs)
        logs = root / "registry/logs"
        logs.mkdir(parents=True, exist_ok=True)
        report["compiler_executed"] = True
        before_lock = (root / "lake-manifest.json").read_bytes()
        verify_dependencies(root, plan["dependency_lock"], environment, logs, require_all=False)
        cache_modules = sorted({m for e in plan["endpoints"] for m in e["external_imports"]
                                if m == "Mathlib" or m.startswith("Mathlib.")})
        _, cache_seconds = execute(["lake", "exe", "cache", "get", *cache_modules], root,
                                   logs / "cache-get.log", environment)
        if (root / "lake-manifest.json").read_bytes() != before_lock:
            raise BuildError("Lake changed the locked dependency manifest; no promotion")
        report["verified_dependencies"] = verify_dependencies(
            root, plan["dependency_lock"], environment, logs, require_all=True)
        version, _ = execute(["lake", "env", "lean", "--version"], root,
                             logs / "lean-version.log", environment)
        expected_version = plan["toolchain"].rsplit(":v", 1)[-1]
        if not re.search(r"\bversion\s+" + re.escape(expected_version) + r"(?:,|\s|\))", version):
            raise BuildError("external compiler version differs from the pinned toolchain")
        report["compiler"] = version.strip()
        targets = [x["id"] for x in plan["endpoints"]]
        _, build_seconds = execute(["lake", "build", *targets], root, logs / "build-first.log", environment)
        audit_started = time.monotonic()
        for entry in plan["endpoints"]:
            identity = fingerprint({"source": entry["input_plan_hash"], "compiler": version.strip()})
            record = {"id": entry["id"], "input_hash": identity, "status": "FAIL",
                      "commit": report["commit"], "source_drift": entry["source_drift"],
                      "local_dependency_modules": len(entry["files"]),
                      "declaration_count": len(entry["spec"]["declarations"])}
            report["endpoints"].append(record)
            evidence = reuse_audit(root, old_entries.get(entry["id"]), entry, identity)
            if evidence is None:
                relative_log = f"registry/audits/{entry['id']}-{identity}.log"
                output, seconds = execute(["lake", "env", "lean", entry["id"] + "/Audit.lean"],
                                          root, root / relative_log, environment)
                parsed = parse_audit(output, [x["name"] for x in entry["spec"]["declarations"]],
                                     set(entry["spec"]["allowed_axioms"]))
                evidence = {**parsed, "audit_log": relative_log,
                            "audit_sha256": sha256((root / relative_log).read_bytes()), "audit_reused": False,
                            "audit_origin_commit": report["commit"], "audit_seconds": seconds}
            record.update(evidence)
            record["status"] = "PASS"
        audit_seconds = round(time.monotonic() - audit_started, 3)
        _, rerun_seconds = execute(["lake", "build", *targets], root, logs / "build-rerun.log", environment)
        report["metrics"] = {"cache_get_seconds": cache_seconds, "build_first_seconds": build_seconds,
                             "audit_seconds": audit_seconds, "build_rerun_seconds": rerun_seconds,
                             "audit_reused_count": sum(x["audit_reused"] for x in report["endpoints"]),
                             "audit_fresh_count": sum(not x["audit_reused"] for x in report["endpoints"]),
                             "rerun_to_first_ratio": None if build_seconds == 0 else round(rerun_seconds / build_seconds, 5)}
        report["status"] = "PASS"
        report["finished_at"] = datetime.now(timezone.utc).isoformat()
        report["total_seconds"] = round(time.monotonic() - started, 3)
        atomic_json(report_path, report)
        print(json.dumps({"status": report["status"], "commit": report["commit"],
                          "endpoints": len(report["endpoints"]), "metrics": report["metrics"]}, indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError, BuildError, subprocess.SubprocessError) as exc:
        report.update(status="FAIL", error=str(exc), total_seconds=round(time.monotonic() - started, 3))
        if not validate_only:
            atomic_json(report_path, report)
        print("MATERIAL_FAILURE " + str(exc), file=sys.stderr, flush=True)
        return 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", action="append", default=None)
    parser.add_argument("--report", type=Path, default=None)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--root", type=Path, default=ROOT)
    args = parser.parse_args()
    root = args.root.resolve()
    report = (root / "registry/current.json") if args.report is None else args.report.resolve()
    return run_build(root, report, args.endpoint, args.native, args.validate_only)


if __name__ == "__main__":
    raise SystemExit(main())
