#!/usr/bin/env python3
"""Exact-pinned Fefferman D verification; compiler execution is external-CI-only.

The only Lake build-like operation is the official Mathlib cache bootstrap.
Proof compilation uses direct Lean commands on the selected upstream closure and
our wrapper. Missing dependency objects fail; no Mathlib source rebuild occurs.
This runner is isolated from Material's Lean 4.33 objects, sources and workflow.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time
import urllib.request

UPSTREAM = "https://github.com/openai/NavierStokesAndEuler.git"
REVISION = "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
MATHLIB = "85e3a25e006c35636f0e53b0e9296caca2685bc0"
COMPILER_URL = "https://github.com/leanprover/lean4/releases/download/v4.34.0-rc2/lean-4.34.0-rc2-linux.tar.zst"
COMPILER_ARCHIVE_SHA256 = "3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8"
ROOT_MODULE = "NavierStokes.ComparatorTheorem"
WRAPPER_MODULE = "MethbokeFeffermanD.Endpoint"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PREFIXES = ("TYPE_BEGIN:", "TYPE_END:", "AXIOMS_BEGIN:", "AXIOMS_END:")
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


class VerificationError(RuntimeError):
    pass


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fingerprint(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def file_sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def save(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def guard() -> None:
    if os.environ.get("GITHUB_ACTIONS") != "true":
        raise VerificationError("This runner is reserved for authorized external GitHub Actions.")
    if os.environ.get("GITHUB_REPOSITORY") != "randogelist/Methboke":
        raise VerificationError("Unexpected repository identity")
    for name in ("GITHUB_SHA", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
        if not os.environ.get(name):
            raise VerificationError("Missing external run identity: " + name)
    if not re.fullmatch(r"[a-f0-9]{40}", os.environ["GITHUB_SHA"]):
        raise VerificationError("Invalid tested checkout identity")
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise VerificationError("This compiler archive requires Linux x86_64")


def run(command: list[str], cwd: Path, log: Path, env=None, timeout=1200) -> tuple[str, float]:
    log.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with log.open("w") as stream:
        stream.write("COMMAND " + json.dumps(command) + "\n")
        stream.flush()
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            returncode = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired as exc:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=10)
            stream.write("\nCOMMAND_TIMEOUT\n")
            raise VerificationError("Command timeout: " + log.name) from exc
    text = log.read_text(errors="replace")
    if returncode:
        raise VerificationError(f"Command exited {returncode}: {log.name}")
    if re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b", text, re.I):
        raise VerificationError("Sorry admission in " + log.name)
    # The command line is provenance, not compiler/audit output.
    return text.split("\n", 1)[1], round(time.monotonic() - started, 3)


def strip_comments(text: str) -> str:
    """Remove nested Lean comments without interpreting source as executable code."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-": depth, i = depth + 1, i + 2
            elif pair == "-/": depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i + 1]); i += 2
            else:
                if text[i] == '"': quoted = False
                i += 1
        elif pair == "/-": depth, i = 1, i + 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'; out.append(text[i]); i += 1
    if depth:
        raise VerificationError("Unclosed source comment")
    return "".join(out)


def imports(text: str) -> list[str]:
    found = []
    for line in strip_comments(text).splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*$", line)
        if match:
            for name in match.group(1).split():
                if name == "all": continue
                if not re.fullmatch(r"[\w.]+", name):
                    raise VerificationError("Unsupported import spelling: " + name)
                found.append(name)
    return found


def git_clean(src: Path, logs: Path, label: str) -> None:
    head, _ = run(["git", "rev-parse", "HEAD"], src, logs / (label + "-head.log"))
    if head.strip() != REVISION:
        raise VerificationError("Upstream checkout revision drift")
    dirty, _ = run(["git", "status", "--porcelain", "--untracked-files=no"],
                   src, logs / (label + "-status.log"))
    if dirty.strip():
        raise VerificationError("Tracked upstream source drift")


def source_plan(src: Path, task: Path) -> dict:
    records, external, visiting = {}, set(), set()
    def visit(name):
        if name in records or name in external: return
        if name in visiting: raise VerificationError("Import cycle: " + name)
        path = src / (name.replace(".", "/") + ".lean")
        if not name.startswith(("NavierStokes.", "MethbokeFeffermanD.")):
            if name.split(".")[0] not in {"Mathlib", "Batteries", "Aesop", "Qq", "Lean", "Init", "Std", "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient"}:
                raise VerificationError("Unexpected dependency namespace: " + name)
            external.add(name); return
        if not path.is_file(): raise VerificationError("Missing own source: " + name)
        visiting.add(name)
        text = path.read_text(); deps = imports(text)
        for dep in deps: visit(dep)
        visiting.remove(name)
        records[name] = {"module": name, "path": path.relative_to(src).as_posix(),
                         "sha256": sha(path.read_bytes()), "imports": deps}
    visit(ROOT_MODULE)
    visit(WRAPPER_MODULE)
    audit_imports = imports((task / "Audit.lean").read_text())
    for name in audit_imports: visit(name)
    if WRAPPER_MODULE not in audit_imports:
        raise VerificationError("Audit must import the exact local wrapper")
    if ROOT_MODULE not in records[WRAPPER_MODULE]["imports"]:
        raise VerificationError("Wrapper must import the fixed periodic theorem")
    return {"modules": records, "external_imports": sorted(external),
            "source_closure_sha256": fingerprint(records)}


def prepare(task: Path, work: Path, evidence: Path) -> None:
    src = work / "upstream"; logs = evidence / "logs"
    src.mkdir(parents=True, exist_ok=True)
    if not (src / ".git").is_dir():
        run(["git", "init"], src, logs / "git-init.log")
        run(["git", "remote", "add", "origin", UPSTREAM], src, logs / "git-remote.log")
    run(["git", "fetch", "--depth=1", "origin", REVISION], src, logs / "git-fetch.log")
    run(["git", "checkout", "--detach", "FETCH_HEAD"], src, logs / "git-checkout.log")
    git_clean(src, logs, "prepare")
    if (src / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise VerificationError("Upstream toolchain pin mismatch")
    lock = json.loads((src / "lake-manifest.json").read_text())
    if [p["rev"] for p in lock["packages"] if p["name"] == "mathlib"] != [MATHLIB]:
        raise VerificationError("Upstream Mathlib pin mismatch")
    for name in ("Endpoint.lean", "Audit.lean", "audit-manifest.json"):
        if not (task / name).is_file(): raise VerificationError("Missing audit input: " + name)
    target = src / "MethbokeFeffermanD"; target.mkdir(exist_ok=True)
    for name in ("Endpoint.lean", "Audit.lean"):
        shutil.copyfile(task / name, target / name)
    plan = source_plan(src, task)
    upstream_count = sum(name.startswith("NavierStokes.") for name in plan["modules"])
    if upstream_count != 604 or len(plan["modules"]) != 605:
        raise VerificationError("Unexpected exact-pinned periodic theorem closure")
    workflow = task.parents[2] / ".github/workflows/fefferman-d-upstream.yml"
    plan.update({"schema_version": 1, "repository": os.environ["GITHUB_REPOSITORY"],
        "tested_commit": os.environ["GITHUB_SHA"], "upstream_repository": UPSTREAM,
        "upstream_revision": REVISION, "toolchain": TOOLCHAIN, "mathlib_revision": MATHLIB,
        "compiler_archive_sha256": COMPILER_ARCHIVE_SHA256,
        "workflow_sha256": file_sha(workflow),
        "build_configuration": {name: file_sha(src / name) for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")},
        "local_inputs": {name: file_sha(task / name) for name in ("Endpoint.lean", "Audit.lean", "audit-manifest.json", "ci/verify.py")},
        "module_workers": 2, "lean_threads": 2, "local_lean_allowed": False,
        "mathlib_source_build_allowed": False, "fresh_required_audits": True})
    dep = fingerprint({"platform": "linux-x86_64", "compiler": COMPILER_ARCHIVE_SHA256,
                       "toolchain": TOOLCHAIN, "configuration": plan["build_configuration"]})
    own = fingerprint({"dependency": dep, "source_closure": plan["source_closure_sha256"],
                       "local_inputs": plan["local_inputs"], "workflow": plan["workflow_sha256"],
                       "upstream": REVISION})
    plan["cache_keys"] = {"compiler": "fefferman-d-compiler-v1-" + COMPILER_ARCHIVE_SHA256,
        "dependency": "fefferman-d-dependency-v1-" + dep, "project": "fefferman-d-project-v1-" + own}
    save(work / "plan.json", plan); save(evidence / "plan.json", plan)
    output = os.environ.get("GITHUB_OUTPUT")
    if output:
        with open(output, "a") as stream:
            for name, value in plan["cache_keys"].items(): stream.write(name + "_key=" + value + "\n")
    print(json.dumps({"phase": "prepared", "own_modules": len(plan["modules"]),
                      "external_imports": len(plan["external_imports"]), "cache_keys": plan["cache_keys"]}))


def install(work: Path, evidence: Path) -> None:
    dest = work / "toolchain"
    marker = dest / "verified-release.json"
    expected = {"toolchain": TOOLCHAIN, "archive_sha256": COMPILER_ARCHIVE_SHA256}
    if marker.is_file():
        retained = json.loads(marker.read_text())
        if any(retained.get(k) != v for k, v in expected.items()):
            raise VerificationError("Restored compiler pin mismatch")
        actual = {p.relative_to(dest).as_posix(): file_sha(p) for p in sorted(dest.rglob("*"))
                  if p.is_file() and p != marker}
        if actual != retained.get("files") or not (dest / "bin/lean").is_file() or not (dest / "bin/lake").is_file():
            raise VerificationError("Restored compiler file identity mismatch")
        save(evidence / "compiler-release.json", {**expected, "installed_file_count": len(actual),
             "installed_files_sha256": fingerprint(actual), "cache_reused": True})
        return
    if dest.exists() and any(dest.iterdir()):
        raise VerificationError("Restored compiler has no matching release marker")
    archive = work / "compiler.tar.zst"
    with urllib.request.urlopen(COMPILER_URL, timeout=120) as response, archive.open("wb") as stream:
        shutil.copyfileobj(response, stream)
    if file_sha(archive) != COMPILER_ARCHIVE_SHA256:
        raise VerificationError("Official compiler archive digest mismatch")
    dest.mkdir(parents=True, exist_ok=True)
    run(["tar", "--zstd", "-xf", str(archive), "--strip-components=1", "-C", str(dest)],
        work, evidence / "logs/compiler-extract.log")
    actual = {p.relative_to(dest).as_posix(): file_sha(p) for p in sorted(dest.rglob("*"))
              if p.is_file() and p != marker}
    save(marker, {**expected, "files": actual})
    save(evidence / "compiler-release.json", {**expected, "installed_file_count": len(actual),
         "installed_files_sha256": fingerprint(actual), "cache_reused": False})
    archive.unlink()


def verify_dependencies(src: Path, lock: dict, logs: Path, label: str) -> list[dict]:
    result = []
    for package in lock["packages"]:
        name = package["name"]
        if package["type"] != "git" or not re.fullmatch(r"[\w.-]+", name):
            raise VerificationError("Unsupported dependency lock entry")
        path = src / ".lake/packages" / name
        if not (path / ".git").exists(): raise VerificationError("Missing locked dependency: " + name)
        head, _ = run(["git", "rev-parse", "HEAD"], path, logs / (label + "-" + name + "-head.log"))
        dirty, _ = run(["git", "status", "--porcelain", "--untracked-files=no"], path, logs / (label + "-" + name + "-status.log"))
        if head.strip() != package["rev"] or dirty.strip():
            raise VerificationError("Dependency revision/source mismatch: " + name)
        result.append({"name": name, "commit": head.strip(), "tracked_source_clean": True})
    return result


def object_files(path: Path) -> dict[str, str]:
    return {str(p): file_sha(p) for p in sorted(path.parent.glob(path.name + "*"))
            if p.is_file() and (p.name == path.name or p.name.startswith(path.name + "."))}


def parse_audit(text: str, names: list[str], allowed: set[str]) -> dict:
    if not allowed <= STANDARD or not names or len(set(names)) != len(names):
        raise VerificationError("Invalid declaration or axiom policy")
    clean = ANSI.sub("", text).replace("\r\n", "\n")
    if re.search(r"\bsorryAx\b|\bwarning\s*:.*\bsorry\b|\berror(?:\([^\n)]*\))?\s*:", clean, re.I):
        raise VerificationError("Audit contains error or sorry admission")
    lines = clean.splitlines()
    found = [line.strip() for line in lines if line.strip().startswith(PREFIXES)]
    if found != [prefix + name for name in names for prefix in PREFIXES]:
        raise VerificationError("Missing, duplicate, reordered or unexpected audit sentinel")
    types, axioms, cursor = {}, {}, 0
    for name in names:
        positions = []
        for prefix in PREFIXES:
            target = prefix + name
            pos = next((i for i in range(cursor, len(lines)) if lines[i].strip() == target), -1)
            if pos < 0: raise VerificationError("Absent audit sentinel: " + target)
            positions.append(pos); cursor = pos + 1
        ty = "\n".join(lines[positions[0] + 1:positions[1]]).strip()
        if not ty or ":" not in ty or name not in ty:
            raise VerificationError("Invalid type report: " + name)
        body = "\n".join(lines[positions[2] + 1:positions[3]]).strip()
        empty = re.fullmatch(r"'" + re.escape(name) + r"'\s+does not depend on any axioms\.?", body)
        nonempty = re.fullmatch(r"'" + re.escape(name) + r"'\s+depends on axioms:\s*\[([^\]]*)\]", body, re.S)
        if empty: dependencies = []
        elif nonempty:
            dependencies = [re.sub(r"\.\{[^{}]*\}", "", n.strip()) for n in nonempty.group(1).split(",") if n.strip()]
        else: raise VerificationError("Malformed axiom report: " + name)
        if not set(dependencies) <= allowed:
            raise VerificationError("Unapproved axioms: " + name)
        types[name] = ty; axioms[name] = sorted(set(dependencies))
    return {"types": types, "axioms": axioms}


def verify(task: Path, work: Path, evidence: Path, budget: int) -> None:
    started = time.monotonic(); deadline = started + budget
    src, logs = work / "upstream", evidence / "logs"
    plan = json.loads((work / "plan.json").read_text())
    report = {"schema_version": 1, "status": "RUNNING", "tested_commit": os.environ["GITHUB_SHA"],
        "run_id": os.environ["GITHUB_RUN_ID"], "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
        "run_url": f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
        "upstream_revision": REVISION, "toolchain": TOOLCHAIN, "mathlib_revision": MATHLIB,
        "local_lean_executions": 0, "fresh_required_audits": True, "module_workers": 2, "lean_threads": 2,
        "source_closure_sha256": plan["source_closure_sha256"], "local_inputs": plan["local_inputs"],
        "workflow_sha256": plan["workflow_sha256"],
        "dependency_cache_class": "EXACT" if os.environ.get("DEPENDENCY_CACHE_HIT") == "true" else "MISS",
        "project_cache_class": "EXACT" if os.environ.get("PROJECT_CACHE_HIT") == "true" else "MISS",
        "module_receipts": {}}
    receipts_path = work / "receipts.json"
    old = json.loads(receipts_path.read_text()) if receipts_path.is_file() else {}
    env = os.environ.copy(); env["PATH"] = str(work / "toolchain/bin") + os.pathsep + env.get("PATH", "")
    env["LEAN_NUM_THREADS"] = "2"; env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env["LEAN_PATH"] = str(src / ".lake/build/lib/lean")
    lake = str(work / "toolchain/bin/lake")
    def execute(args, log, maximum=1200):
        remaining = deadline - time.monotonic()
        if remaining <= 0: raise VerificationError("Verification time budget exhausted")
        return run(args, src, log, env, min(maximum, remaining))
    try:
        if plan["tested_commit"] != os.environ["GITHUB_SHA"]:
            raise VerificationError("Plan checkout identity mismatch")
        if file_sha(task.parents[2] / ".github/workflows/fefferman-d-upstream.yml") != plan["workflow_sha256"]:
            raise VerificationError("Workflow policy drift")
        for name, digest in plan["local_inputs"].items():
            if file_sha(task / name) != digest: raise VerificationError("Local audit policy/source drift: " + name)
        git_clean(src, logs, "before")
        lock_path = src / "lake-manifest.json"; lock_before = file_sha(lock_path)
        cache_start = time.monotonic()
        execute([lake, "exe", "cache", "get", "Mathlib"], logs / "official-cache-get.log", 1800)
        if file_sha(lock_path) != lock_before: raise VerificationError("Dependency lock changed during cache retrieval")
        report["verified_dependencies"] = verify_dependencies(src, json.loads(lock_path.read_text()), logs, "before")
        report["cache_seconds"] = round(time.monotonic() - cache_start, 3)
        compiler, _ = execute([lake, "env", "lean", "--version"], logs / "compiler-version.log")
        if "version 4.34.0-rc2," not in compiler:
            raise VerificationError("Wrong external compiler")
        report["compiler"] = compiler.strip()
        report["compiler_binary_sha256"] = file_sha(work / "toolchain/bin/lean")
        report["lake_binary_sha256"] = file_sha(work / "toolchain/bin/lake")
        report["compiler_release"] = json.loads((evidence / "compiler-release.json").read_text())
        dependencies = sorted((src / ".lake/packages").glob("*/.lake/build/lib/lean/**/*.olean*"))
        object_manifest = {p.relative_to(src).as_posix(): file_sha(p) for p in dependencies if p.is_file()}
        if not object_manifest: raise VerificationError("Official dependency objects absent; rebuild forbidden")
        save(evidence / "dependency-objects.json", object_manifest)
        report["external_object_count"] = len(object_manifest)
        report["external_object_digest"] = fingerprint(object_manifest)
        probe = src / "MethbokeFeffermanD/DependencyProbe.lean"
        probe.write_text("\n".join("import " + n for n in plan["external_imports"]) + "\n")
        execute([lake, "env", "lean", str(probe)], logs / "dependency-import-probe.log")
        context = fingerprint({"compiler": compiler.strip(), "configuration": plan["build_configuration"],
            "external_objects": report["external_object_digest"],
            "compiler_binary": report["compiler_binary_sha256"], "compiler_files": report["compiler_release"]["installed_files_sha256"],
            "policy": plan["local_inputs"]["ci/verify.py"], "workflow": plan["workflow_sha256"]})
        report["compile_context"] = context
        records = plan["modules"]
        waiting = set(records); completed, failed, futures = set(), set(), {}
        out = src / ".lake/build/lib/lean"
        build_start = time.monotonic()
        def compile_one(name):
            record = records[name]; source = src / record["path"]
            if file_sha(source) != record["sha256"]: raise VerificationError("Own source drift: " + name)
            artifact = out / (name.replace(".", "/") + ".olean")
            imported = {n: report["module_receipts"][n]["object_digest"] for n in record["imports"] if n in records}
            identity = fingerprint({"source": record["sha256"], "context": context, "imports": imported})
            prior = old.get("modules", {}).get(name) if old.get("status") == "PASS" else None
            existing = object_files(artifact) if artifact.is_file() else {}
            normalized = {Path(k).relative_to(src).as_posix(): v for k, v in existing.items()}
            if prior and prior.get("identity") == identity and prior.get("objects") == normalized and normalized:
                return {**prior, "reused": True, "seconds": 0.0, "status": "PASS"}
            artifact.parent.mkdir(parents=True, exist_ok=True)
            _, seconds = execute([lake, "env", "lean", "--root=" + str(src), "-o", str(artifact), str(source)],
                                 logs / "modules" / (name + ".log"))
            if not artifact.is_file(): raise VerificationError("Missing own compiler object: " + name)
            objects = {Path(k).relative_to(src).as_posix(): v for k, v in object_files(artifact).items()}
            return {"status": "PASS", "source_sha256": record["sha256"], "identity": identity,
                    "objects": objects, "object_digest": fingerprint(objects), "reused": False, "seconds": seconds}
        with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
            while waiting or futures:
                blocked = {n for n in waiting if any(d in failed for d in records[n]["imports"])}
                for name in blocked:
                    waiting.remove(name); failed.add(name)
                    report["module_receipts"][name] = {"status": "BLOCKED_BY_DEPENDENCY"}
                ready = sorted(n for n in waiting if all(d not in records or d in completed for d in records[n]["imports"]))
                while ready and len(futures) < 2:
                    name = ready.pop(0); waiting.remove(name); futures[pool.submit(compile_one, name)] = name
                if not futures:
                    if waiting: raise VerificationError("Unresolved own dependency graph")
                    break
                done, _ = concurrent.futures.wait(futures, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in done:
                    name = futures.pop(future)
                    try:
                        receipt = future.result(); completed.add(name)
                    except Exception as exc:
                        receipt = {"status": "FAIL", "error": str(exc)}; failed.add(name)
                    report["module_receipts"][name] = receipt
                    print(json.dumps({"module": name, "status": receipt["status"],
                        "reused": receipt.get("reused"), "completed": len(completed), "total": len(records)}), flush=True)
                save(evidence / "current.json", report)
        report["build_seconds"] = round(time.monotonic() - build_start, 3)
        if failed: raise VerificationError("Own module compilation failed; inspect retained logs")
        manifest = json.loads((task / "audit-manifest.json").read_text())
        names = [d["name"] if isinstance(d, dict) else d for d in manifest["declarations"]]
        text, seconds = execute([lake, "env", "lean", str(src / "MethbokeFeffermanD/Audit.lean")], logs / "audit.log")
        report["audit"] = {**parse_audit(text, names, set(manifest["allowed_axioms"])),
            "seconds": seconds, "fresh": True, "source_sha256": file_sha(task / "Audit.lean"),
            "log_sha256": file_sha(logs / "audit.log"), "origin_commit": os.environ["GITHUB_SHA"]}
        git_clean(src, logs, "after")
        report["verified_dependencies_after"] = verify_dependencies(src, json.loads(lock_path.read_text()), logs, "after")
        if file_sha(lock_path) != lock_before: raise VerificationError("Dependency lock changed")
        if source_plan(src, task)["source_closure_sha256"] != plan["source_closure_sha256"]:
            raise VerificationError("Source closure changed during verification")
        report["status"] = "PASS"
        save(receipts_path, {"status": "PASS", "compile_context": context,
            "upstream_revision": REVISION, "tested_commit": os.environ["GITHUB_SHA"],
            "audit_input_sha256": file_sha(task / "Audit.lean"), "modules": report["module_receipts"]})
    except Exception as exc:
        report["status"] = "FAIL"; report["error"] = str(exc)
        raise
    finally:
        values = list(report["module_receipts"].values())
        report["metrics"] = {"module_count": len(plan["modules"]),
            "passed_modules": sum(v["status"] == "PASS" for v in values),
            "fresh_modules": sum(v["status"] == "PASS" and not v.get("reused", False) for v in values),
            "reused_modules": sum(v["status"] == "PASS" and v.get("reused", False) for v in values),
            "source_lines": sum(len((src / record["path"]).read_text().splitlines()) for record in plan["modules"].values()),
            "verification_seconds": round(time.monotonic() - started, 3)}
        save(evidence / "current.json", report)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["prepare", "install", "verify"])
    parser.add_argument("--task", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--time-budget-seconds", type=int, default=9000)
    args = parser.parse_args()
    guard()  # Must run before any executable compiler or dependency operation.
    task, work, evidence = args.task.resolve(), args.work.resolve(), args.evidence.resolve()
    work.mkdir(parents=True, exist_ok=True); evidence.mkdir(parents=True, exist_ok=True)
    try:
        if args.phase == "prepare": prepare(task, work, evidence)
        elif args.phase == "install": install(work, evidence)
        else: verify(task, work, evidence, args.time_budget_seconds)
    except Exception as exc:
        save(evidence / (args.phase + "-failure.json"), {"status": "FAIL", "phase": args.phase, "error": str(exc), "local_lean_executions": 0})
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
