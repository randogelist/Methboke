#!/usr/bin/env python3
"""Export one complete endpoint source package without executing Lean or Lake."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import shutil
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.33.0"
MATHLIB_REV = "db584cd6d46c92f209a44c0f1c829460d327499d"
EXTERNAL_ROOTS = {
    "Mathlib", "Lean", "Init", "Std", "Batteries", "Aesop", "Qq",
    "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli",
}
IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


class ExportError(ValueError):
    """An input is incomplete, stale, unpinned or outside the source package."""


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def contained_file(root: Path, relative: str) -> Path:
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts:
        raise ExportError(f"Invalid package-relative path: {relative}")
    path = root / rel
    if not path.resolve().is_relative_to(root.resolve()) or not path.is_file():
        raise ExportError(f"Missing or external package file: {relative}")
    return path


def strip_lean_comments_and_strings(text: str) -> str:
    """Retain line boundaries while removing nested comments and literals."""
    out: list[str] = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\":
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ExportError("Unterminated Lean comment or string in source input")
    return "".join(out)


def imports_of(data: bytes) -> list[str]:
    clean = strip_lean_comments_and_strings(data.decode("utf-8"))
    result: list[str] = []
    for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", clean, re.MULTILINE):
        for token in line.split():
            if not MODULE.fullmatch(token):
                raise ExportError(f"Unsupported import token: {token}")
            if token not in result:
                result.append(token)
    return result


def verified_graph(root: Path, endpoint: dict, closure: dict, manifest: dict,
                   owned_manifest: dict | None = None) -> list[dict]:
    """Check recorded closure against recursively parsed current source bytes."""
    records = {row["module"]: row for row in manifest["files"]}
    if len(records) != len(manifest["files"]):
        raise ExportError("Duplicate modules in source-manifest.json")
    owned: set[str] = set()
    if owned_manifest is not None:
        if owned_manifest.get("schema_version") != 1 or not isinstance(owned_manifest.get("modules"), list):
            raise ExportError("Invalid owned-sources.json schema")
        for row in owned_manifest["modules"]:
            if not isinstance(row, dict):
                raise ExportError("Invalid owned source record")
            module = row.get("module")
            if not isinstance(module, str) or not MODULE.fullmatch(module):
                raise ExportError("Invalid owned module name")
            if module in records:
                raise ExportError(f"Duplicate vendor/owned module: {module}")
            relative = row.get("path")
            if relative != module.replace(".", "/") + ".lean":
                raise ExportError(f"Owned source path does not match module name: {module}")
            if module.split(".")[0] in EXTERNAL_ROOTS | {"_vendor", "ci", "registry", "tests", "provenance"}:
                raise ExportError(f"Reserved owned module namespace: {module}")
            origin = row.get("origin", {})
            if (not isinstance(origin, dict) or origin.get("repository") != "randogelist/Methboke"
                    or not isinstance(origin.get("path"), str)
                    or not origin["path"] or not isinstance(origin.get("revision"), str)
                    or not re.fullmatch("[0-9a-f]{40}", origin["revision"])):
                raise ExportError(f"Missing exact owned source provenance: {module}")
            if (not isinstance(row.get("imports"), list) or not isinstance(row.get("sha256"), str)
                    or not re.fullmatch("[0-9a-f]{64}", row["sha256"])):
                raise ExportError(f"Invalid owned source identity: {module}")
            records[module] = row
            owned.add(module)
    endpoint_path = endpoint["endpoint_module"].replace(".", "/") + ".lean"
    actual_roots = imports_of(contained_file(root, endpoint_path).read_bytes())
    if set(actual_roots) != set(endpoint["imports"]) or set(actual_roots) != set(closure["roots"]):
        raise ExportError("Endpoint imports and recorded closure roots disagree")
    selected: dict[str, dict] = {}
    audit_path = endpoint["audit_module"].replace(".", "/") + ".lean"
    audit_imports = imports_of(contained_file(root, audit_path).read_bytes())
    if endpoint["endpoint_module"] not in audit_imports:
        raise ExportError("The audit does not import its exact endpoint module")
    pending = list(actual_roots) + [module for module in audit_imports
                                  if module != endpoint["endpoint_module"]]
    while pending:
        module = pending.pop()
        if module in selected:
            continue
        row = records.get(module)
        if row is None:
            if module.split(".")[0] not in EXTERNAL_ROOTS:
                raise ExportError(f"Missing transitive local module: {module}")
            continue
        relative = row.get("path", row.get("local_path"))
        if module not in owned:
            if not isinstance(relative, str) or not relative.startswith("_vendor/"):
                raise ExportError(f"Invalid vendor source path for {module}")
            if relative != "_vendor/" + module.replace(".", "/") + ".lean":
                raise ExportError(f"Vendor source path does not match module name: {module}")
        data = contained_file(root, relative).read_bytes()
        if (sha256(data) != row["sha256"]
                or (module not in owned and git_blob_sha(data) != row["git_blob_sha"])
                or ("git_blob_sha" in row and git_blob_sha(data) != row["git_blob_sha"])):
            raise ExportError(f"Source content hash mismatch: {module}")
        actual_imports = imports_of(data)
        if set(actual_imports) != set(row["imports"]):
            raise ExportError(f"Stale import manifest: {module}")
        selected[module] = {**row, "source_kind": "owned" if module in owned else "vendor"}
        pending.extend(actual_imports)
    recorded = {row["module"]: row for row in closure["files"]}
    if len(recorded) != len(closure["files"]) or set(recorded) != set(selected):
        raise ExportError("Recorded endpoint closure is incomplete or stale")
    for module, row in selected.items():
        other = recorded[module]
        if (other["sha256"] != row["sha256"]
                or (module not in owned and other.get("git_blob_sha") != row["git_blob_sha"])
                or (module in owned and other.get("path", other.get("local_path")) != row["path"])
                or ("git_blob_sha" in other and other["git_blob_sha"] != row.get("git_blob_sha"))):
            raise ExportError(f"Endpoint closure hash mismatch: {module}")
    return [copy.deepcopy(selected[name]) for name in sorted(selected)]


def lakefile(endpoint_id: str, files: list[dict]) -> str:
    lines = [
        "import Lake", "open Lake DSL", "", "package material_endpoint where",
        '  version := v!"0.1.0"', "",
        'require mathlib from git "https://github.com/leanprover-community/mathlib4" '
        f'@ "{MATHLIB_REV}"', "",
    ]
    namespace_roots: dict[str, str] = {}
    for row in files:
        namespace = row["module"].split(".")[0]
        source_root = "." if row.get("source_kind") == "owned" else "_vendor"
        if namespace in namespace_roots and namespace_roots[namespace] != source_root:
            raise ExportError(f"Namespace spans vendor and owned roots: {namespace}")
        namespace_roots[namespace] = source_root
    for namespace, source_root in sorted(namespace_roots.items()):
        if not IDENTIFIER.fullmatch(namespace):
            raise ExportError(f"Invalid local namespace: {namespace}")
        lines.extend([
            f"lean_lib {namespace} where", f'  srcDir := "{source_root}"',
            f"  globs := #[.submodules `{namespace}]", "",
        ])
    lines.extend([
        "@[default_target]", f"lean_lib {endpoint_id} where",
        f"  roots := #[`{endpoint_id}.Endpoint]", "",
    ])
    return "\n".join(lines)


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def copy_exact(root: Path, staging: Path, relative: str) -> None:
    source = contained_file(root, relative)
    destination = staging / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source.read_bytes())


def make_zip(source: Path, destination: Path) -> None:
    if destination.exists():
        raise ExportError(f"ZIP destination already exists: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in sorted(source.rglob("*")):
            if not path.is_file():
                continue
            info = zipfile.ZipInfo(f"{source.name}/{path.relative_to(source).as_posix()}")
            info.date_time = (1980, 1, 1, 0, 0, 0)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = (0o100755 if path.name == "run.sh" else 0o100644) << 16
            archive.writestr(info, path.read_bytes())


def export_endpoint(endpoint_id: str, output: Path, zip_path: Path | None = None,
                    *, root: Path = ROOT) -> dict:
    if not IDENTIFIER.fullmatch(endpoint_id):
        raise ExportError(f"Invalid endpoint ID: {endpoint_id}")
    root = root.resolve()
    output = output.absolute()
    if output.is_symlink() or output.resolve() == root:
        raise ExportError("Output cannot replace or alias the source package")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise ExportError(f"Output directory must be absent or empty: {output}")
    if zip_path is not None:
        zip_path = zip_path.absolute()
        if zip_path.exists() or zip_path.resolve().is_relative_to(output.resolve()):
            raise ExportError("ZIP must be a new file outside the export directory")
    index = load_json(contained_file(root, "endpoints.json"))
    matches = [row for row in index["endpoints"] if row["id"] == endpoint_id]
    if len(matches) != 1:
        raise ExportError(f"Endpoint is absent or duplicated in index: {endpoint_id}")
    entry = matches[0]
    endpoint = load_json(contained_file(root, entry["manifest"]))
    closure = load_json(contained_file(root, entry["closure"]))
    source_manifest = load_json(contained_file(root, "_vendor/source-manifest.json"))
    owned_path = root / "owned-sources.json"
    owned_manifest = load_json(contained_file(root, "owned-sources.json")) if owned_path.exists() else None
    if endpoint["id"] != endpoint_id or closure["endpoint"] != endpoint_id:
        raise ExportError("Endpoint identifiers disagree")
    for module_key in ("endpoint_module", "audit_module"):
        if endpoint[module_key] != f"{endpoint_id}.{module_key.split('_')[0].capitalize()}":
            raise ExportError(f"Unsupported {module_key}: {endpoint[module_key]}")
    if closure["lean_toolchain"] != TOOLCHAIN or closure["mathlib_commit"] != MATHLIB_REV:
        raise ExportError("Endpoint compiler/dependency pin differs from the export contract")
    actual_toolchain = contained_file(root, "lean-toolchain").read_text(encoding="utf-8").strip()
    if actual_toolchain != TOOLCHAIN:
        raise ExportError("Source package toolchain differs from the locked endpoint")
    lock = load_json(contained_file(root, "lake-manifest.json"))
    mathlib = [row for row in lock["packages"] if row["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REV:
        raise ExportError("Source package Mathlib lock differs from the endpoint")
    files = verified_graph(root, endpoint, closure, source_manifest, owned_manifest)
    contained_file(root, "ci/build.py")
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{endpoint_id}-export-", dir=output.parent))
    try:
        for relative in (entry["manifest"], entry["closure"], f"{endpoint_id}/Endpoint.lean",
                         f"{endpoint_id}/Audit.lean", "lean-toolchain", "ci/build.py"):
            copy_exact(root, staging, relative)
        for optional in (f"{endpoint_id}/README.md", "_vendor/README.md"):
            if (root / optional).is_file():
                copy_exact(root, staging, optional)
        for row in files:
            copy_exact(root, staging, row.get("path", row.get("local_path")))
        for provenance in source_manifest.get("provenance", []):
            copy_exact(root, staging, provenance["local_path"])
        reduced_manifest = copy.deepcopy(source_manifest)
        vendor_files = [{k: v for k, v in row.items() if k != "source_kind"}
                        for row in files if row["source_kind"] == "vendor"]
        owned_files = [{k: v for k, v in row.items() if k != "source_kind"}
                       for row in files if row["source_kind"] == "owned"]
        reduced_manifest["files"] = vendor_files
        reduced_manifest["local_module_count"] = len(vendor_files)
        reduced_manifest["static_validation"] = {
            "source_blob_matches": len(vendor_files), "missing_local_imports": [],
            "recursive_imports_rechecked_at_export": True,
        }
        write_json(staging / "_vendor/source-manifest.json", reduced_manifest)
        if owned_manifest is not None:
            reduced_owned = copy.deepcopy(owned_manifest)
            reduced_owned["modules"] = owned_files
            if "module_count" in reduced_owned:
                reduced_owned["module_count"] = len(owned_files)
            write_json(staging / "owned-sources.json", reduced_owned)
        reduced_index = copy.deepcopy(index)
        reduced_index.update({"endpoints": [entry], "endpoint_count": 1,
                              "declaration_count": len(endpoint["declarations"]),
                              "status": "PENDING_EXTERNAL_COMPILER"})
        write_json(staging / "endpoints.json", reduced_index)
        lock["name"] = "material_endpoint"
        write_json(staging / "lake-manifest.json", lock)
        (staging / "lakefile.lean").write_text(lakefile(endpoint_id, files), encoding="utf-8")
        (staging / "registry").mkdir()
        (staging / "registry/README.md").write_text(
            "# External compiler evidence\n\n`current.json` is generated only by an external build/audit.\n"
            "No passed theorem container is asserted by this source export.\n", encoding="utf-8")
        (staging / "run.cmd").write_bytes((
            "@echo off\r\nsetlocal\r\ncd /d \"%~dp0\"\r\n"
            "where py >nul 2>nul\r\nif errorlevel 1 goto use_python\r\n"
            f"py -3 ci\\build.py --native --endpoint {endpoint_id} --report registry\\current.json\r\n"
            "exit /b %errorlevel%\r\n:use_python\r\n"
            f"python ci\\build.py --native --endpoint {endpoint_id} --report registry\\current.json\r\n"
            "exit /b %errorlevel%\r\n").encode("utf-8"))
        shell = staging / "run.sh"
        shell.write_text(
            "#!/usr/bin/env bash\nset -euo pipefail\ncd -- \"$(dirname -- \"$0\")\"\n"
            'if [[ "${CI:-}" != "true" ]]; then\n'
            '  echo "External CI required; native Windows execution uses run.cmd." >&2\n'
            "  exit 2\nfi\n"
            f"python3 ci/build.py --endpoint {endpoint_id} --report registry/current.json\n",
            encoding="utf-8")
        shell.chmod(0o755)
        (staging / "README.md").write_text(
            f"# {endpoint_id}: standalone source cutout\n\n"
            f"`local modules = {len(files)}` · `Lean = 4.33.0`\n\n"
            f"`Mathlib = {MATHLIB_REV}`\n\n"
            "Source package: complete recursive local proof sources, exact endpoint imports, "
            "theorem type/axiom audit, and locked public dependencies. No private Methlib fetch "
            "or parent repository is required. Mathlib and its locked dependencies are obtained "
            "through Lake; their compiled cache is requested by the build driver.\n\n"
            "External native Windows: Python 3, Git, and the specified elan/Lean toolchain must "
            "be available. Execute `run.cmd`. External Unix CI: execute `./run.sh` in the "
            "actual CI environment; the script rejects non-CI Unix execution. The build driver "
            "requests the matching cache before compiling this endpoint and records exact "
            "types, allowed-axiom checks, timing, compiler platform and content fingerprints "
            "under `registry/`. Existing build outputs are retained for subsequent runs.\n\n"
            "`export status = PREPARED`\n\n`compiler pass = NOT ASSERTED`\n\n"
            "`A_TIER promotion = matching external compiler and theorem-level axiom evidence required`\n",
            encoding="utf-8")
        inventory = {
            str(path.relative_to(staging)).replace("\\", "/"): sha256(path.read_bytes())
            for path in sorted(staging.rglob("*")) if path.is_file()
        }
        package_hash = sha256(json.dumps(inventory, sort_keys=True, separators=(",", ":")).encode())
        export_info = {
            "schema_version": 1, "endpoint": endpoint_id, "status": "PREPARED",
            "local_module_count": len(files), "lean_toolchain": TOOLCHAIN,
            "mathlib_commit": MATHLIB_REV, "package_input_sha256": package_hash,
            "files_sha256": inventory, "local_lean_executions": 0,
            "external_compiler_evidence": None, "theorem_axiom_audit": None,
        }
        write_json(staging / "export.json", export_info)
        if output.exists():
            output.rmdir()
        staging.rename(output)
    except Exception:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    if zip_path is not None:
        make_zip(output, zip_path)
    return {"endpoint": endpoint_id, "output": str(output),
            "zip": str(zip_path) if zip_path else None, "local_modules": len(files),
            "package_input_sha256": package_hash, "status": "PREPARED"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("endpoint", help="Exact endpoint ID from Material/endpoints.json")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--zip", dest="zip_path", type=Path)
    args = parser.parse_args()
    try:
        result = export_endpoint(args.endpoint, args.output, args.zip_path)
    except (ExportError, OSError, KeyError, json.JSONDecodeError) as error:
        parser.exit(2, f"Export failed: {error}\n")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
