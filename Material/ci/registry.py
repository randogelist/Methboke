#!/usr/bin/env python3
"""Passed-container registry; all Lean execution is delegated to external CI.

No credential enters the build container. A mutable compatibility pointer is
updated only after compile/audit PASS and forward along the current branch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request


LABEL_PREFIX = "io.methboke.material."
PLATFORM = "linux/amd64"
GIB = 1024 ** 3
MIB = 1024 ** 2
COMPATIBILITY_FILES = (
    "Material/lean-toolchain",
    "Material/lake-manifest.json",
    "Material/ci/Dockerfile",
    "Material/ci/cache-contract.json",
)


def execute(argv: list[str], *, capture: bool = False, check: bool = True,
            timeout: float | None = None):
    result = subprocess.run(argv, text=True, capture_output=capture, timeout=timeout)
    if check and result.returncode:
        detail = result.stderr[-3000:] if capture else ""
        raise RuntimeError(f"command failed ({result.returncode}): {argv[0]} {argv[1]} {detail}")
    return result


def save(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    temp.replace(path)


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def parse_meminfo(text: str) -> dict[str, int]:
    values = {}
    for line in text.splitlines():
        match = re.fullmatch(r"([A-Za-z_]+):\s+(\d+)\s+kB", line.strip())
        if match:
            values[match.group(1)] = int(match.group(2)) * 1024
    return values


def host_resources(root: Path, docker_root: str | None = None) -> dict:
    memory = parse_meminfo(Path("/proc/meminfo").read_text())
    paths = {"workspace": root, "docker": Path(docker_root or "/var/lib/docker")}
    disk = {}
    for name, path in paths.items():
        try:
            usage = shutil.disk_usage(path)
            disk[name] = {"path": str(path), "total_bytes": usage.total,
                          "free_bytes": usage.free, "used_bytes": usage.used}
        except OSError as exc:
            disk[name] = {"path": str(path), "error": str(exc)}
    return {"timestamp": time.time(), "cpu_count": os.cpu_count() or 1,
            "memory_total_bytes": memory.get("MemTotal", 0),
            "memory_available_bytes": memory.get("MemAvailable", 0), "disk": disk}


def resource_limits(snapshot: dict) -> dict:
    """Conservative cgroup limits; reserve >=2 GiB for the runner host."""
    total = snapshot["memory_total_bytes"]
    available = snapshot["memory_available_bytes"]
    limit = min(5 * GIB, total - 2 * GIB, available - GIB)
    limit = (limit // MIB) * MIB
    if limit < 2 * GIB:
        raise ValueError("insufficient available RAM for a bounded build plus runner reserve")
    return {"memory_bytes": limit, "memory_swap_bytes": limit,
            "host_memory_reserve_bytes": total - limit,
            "cpus": min(2, snapshot["cpu_count"]), "pids_limit": 512,
            "policy": "min(5GiB,total-2GiB,available-1GiB); no container swap"}


def preflight(root: Path, stage: str, minimum_disk_gib: int) -> tuple[dict, dict]:
    info_result = execute(["docker", "info", "--format", "{{json .}}"], capture=True, timeout=30)
    info = json.loads(info_result.stdout)
    snapshot = host_resources(root, info.get("DockerRootDir"))
    snapshot["docker_controls"] = {key: info.get(key) for key in
                                   ("MemoryLimit", "SwapLimit", "CpuCfsQuota", "CgroupVersion")}
    snapshot["stage"] = stage
    snapshot["minimum_disk_free_bytes"] = minimum_disk_gib * GIB
    save(root / "Material/registry" / ("resources-" + stage + ".json"), snapshot)
    print("MATERIAL_RESOURCES " + json.dumps(snapshot, sort_keys=True), flush=True)
    for name, entry in snapshot["disk"].items():
        if "free_bytes" not in entry:
            raise ValueError(f"cannot inspect {name} filesystem capacity")
        if entry["free_bytes"] < minimum_disk_gib * GIB:
            raise ValueError(f"insufficient {name} free disk: requires {minimum_disk_gib} GiB; no cleanup performed")
    if not info.get("MemoryLimit") or not info.get("SwapLimit") or not info.get("CpuCfsQuota"):
        raise ValueError("Docker must expose memory, swap and CPU quota controls for runner protection")
    return snapshot, resource_limits(snapshot)


def container_exit_metadata(info: dict) -> dict:
    state = info.get("State") or {}
    config = info.get("HostConfig") or {}
    return {"container_exit_code": state.get("ExitCode"),
            "container_oom_killed": bool(state.get("OOMKilled", False)),
            "container_state": state.get("Status"), "container_running": bool(state.get("Running", False)),
            "container_error": state.get("Error", ""),
            "container_started_at": state.get("StartedAt"), "container_finished_at": state.get("FinishedAt"),
            "enforced_resources": {name: config.get(name) for name in
                                   ("Memory", "MemorySwap", "NanoCpus", "PidsLimit")}}


def monitor_resources(root: Path, container: str, stop: threading.Event,
                      failures: list[str], docker_root: str) -> None:
    """Persist progress without reading credentials or stopping unrelated resources."""
    path = root / "Material/registry/host-monitor.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    while not stop.is_set():
        try:
            sample = host_resources(root, docker_root)
            stats = execute(["docker", "stats", "--no-stream", "--format", "{{json .}}", container],
                            capture=True, check=False, timeout=15)
            sample["container_stats"] = stats.stdout.strip()
            low_disk = any(item.get("free_bytes", 0) < GIB for item in sample["disk"].values())
            low_memory = sample["memory_available_bytes"] < 256 * MIB
            if low_disk or low_memory:
                reason = "host_disk_below_1GiB" if low_disk else "host_available_memory_below_256MiB"
                failures.append(reason)
                sample["resource_abort"] = reason
                # Only this workflow's named container is stopped.
                execute(["docker", "stop", "--time", "15", container], check=False, timeout=30)
            with path.open("a") as stream:
                stream.write(json.dumps(sample, sort_keys=True) + "\n")
                stream.flush()
            print("MATERIAL_RESOURCE_SAMPLE " + json.dumps(sample, sort_keys=True), flush=True)
            if failures:
                return
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
            print("::warning::Resource sampling unavailable: " + str(exc), flush=True)
        stop.wait(30)


def compatibility(root: Path) -> str:
    digest = hashlib.sha256()
    for name in COMPATIBILITY_FILES:
        data = (root / name).read_bytes()
        digest.update(name.encode() + b"\0" + data + b"\0")
    return digest.hexdigest()


def slug(value: str, maximum: int = 32) -> str:
    clean = re.sub(r"[^a-z0-9_.-]+", "-", value.lower()).strip("-.")
    return (clean or "branch")[:maximum]


def metadata(root: Path, environ: dict[str, str]) -> dict:
    repository = environ["GITHUB_REPOSITORY"]
    if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
        raise ValueError("invalid GitHub repository")
    commit = environ["GITHUB_SHA"]
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("an exact 40-character source commit is required")
    run_id = environ["GITHUB_RUN_ID"]
    attempt = environ.get("GITHUB_RUN_ATTEMPT", "1")
    if not run_id.isdigit() or not attempt.isdigit():
        raise ValueError("invalid numeric run identity")
    branch = environ["GITHUB_REF_NAME"]
    key = compatibility(root)
    image = "ghcr.io/" + repository.lower() + "-material"
    branch_key = slug(branch, 24) + "-" + hashlib.sha256(branch.encode()).hexdigest()[:8]
    return {
        "schema": 1,
        "repository": repository,
        "commit": commit,
        "branch": branch,
        "run_id": run_id,
        "attempt": attempt,
        "compatibility_key": key,
        "platform": PLATFORM,
        "image_repository": image,
        "pointer": f"{image}:latest-{branch_key}-{key[:16]}",
        "immutable_tag": f"{image}:passed-{commit[:12]}-{run_id}-{attempt}",
        "container": f"material-{run_id}-{attempt}",
    }


def compatible_image(info: dict, state: dict) -> bool:
    labels = info.get("Config", {}).get("Labels") or {}
    return (
        info.get("Os") == "linux"
        and info.get("Architecture") == "amd64"
        and labels.get(LABEL_PREFIX + "status") == "PASS"
        and labels.get(LABEL_PREFIX + "compatibility") == state["compatibility_key"]
        and labels.get("org.opencontainers.image.source")
        == "https://github.com/" + state["repository"]
    )


def prepare(root: Path, state_path: Path) -> None:
    started = time.monotonic()
    state = metadata(root, os.environ)
    state["status"] = "PREPARING"
    save(state_path, state)
    minimum_disk = int(os.environ.get("MATERIAL_MIN_FREE_GIB", "20"))
    if not 8 <= minimum_disk <= 100:
        raise ValueError("MATERIAL_MIN_FREE_GIB must be between 8 and 100")
    before, limits = preflight(root, "before-prepare", minimum_disk)
    state["resource_limits"] = limits
    state["docker_root"] = before["disk"]["docker"]["path"]
    save(state_path, state)
    pulled = execute(["docker", "pull", "--platform", PLATFORM, state["pointer"]], check=False)
    if pulled.returncode == 0:
        inspection = execute(["docker", "image", "inspect", state["pointer"]], capture=True)
        info = json.loads(inspection.stdout)[0]
        if compatible_image(info, state):
            candidates = [
                value for value in info.get("RepoDigests", [])
                if value.startswith(state["image_repository"] + "@sha256:")
            ]
            if not candidates:
                raise RuntimeError("pulled passed image lacks its immutable registry digest")
            state["base_image"] = candidates[0]
            state["parent_image_digest"] = candidates[0]
            state["parent_commit"] = (info["Config"].get("Labels") or {}).get(
                "org.opencontainers.image.revision"
            )
            state["restore_mode"] = "previous_passed_container"
        else:
            print("::warning::Registry pointer failed compatibility/PASS validation; cold bootstrap.")
    else:
        print("::notice::No accessible compatible passed image; cold cached-dependency bootstrap.")

    if "base_image" not in state:
        toolchain = (root / "Material/lean-toolchain").read_text().strip()
        if not re.fullmatch(r"leanprover/lean4:v[0-9A-Za-z.+-]+", toolchain):
            raise ValueError("unsupported or unpinned Lean toolchain")
        tag = "methboke-bootstrap:" + state["compatibility_key"][:16]
        execute([
            "docker", "build", "--platform", PLATFORM,
            "--file", str(root / "Material/ci/Dockerfile"),
            "--build-arg", "LEAN_TOOLCHAIN=" + toolchain,
            "--tag", tag, str(root / "Material/ci"),
        ])
        state.update(base_image=tag, parent_image_digest=None, parent_commit=None,
                     restore_mode="cold_bootstrap")
    preflight(root, "after-prepare", 8)
    state["prepare_seconds"] = round(time.monotonic() - started, 3)
    state["status"] = "PREPARED"
    save(state_path, state)
    print(json.dumps({key: state[key] for key in (
        "restore_mode", "base_image", "compatibility_key", "prepare_seconds"
    )}, indent=2))


def run(root: Path, state_path: Path) -> None:
    state = load(state_path)
    _, limits = preflight(root, "before-run", 8)
    state["resource_limits"] = limits
    save(state_path, state)
    env = {
        "CI": "true",
        "GITHUB_SHA": state["commit"],
        "GITHUB_RUN_ID": state["run_id"],
        "GITHUB_RUN_ATTEMPT": state["attempt"],
        "GITHUB_REPOSITORY": state["repository"],
        "GITHUB_REF_NAME": state["branch"],
        "MATERIAL_COMPATIBILITY_KEY": state["compatibility_key"],
        "MATERIAL_PARENT_IMAGE_DIGEST": state["parent_image_digest"] or "",
        "MATERIAL_RESTORE_MODE": state["restore_mode"],
        "MATERIAL_JOBS": os.environ.get("MATERIAL_JOBS", "2"),
    }
    args = [
        "docker", "create", "--platform", PLATFORM, "--name", state["container"],
        "--memory", str(limits["memory_bytes"]),
        "--memory-swap", str(limits["memory_swap_bytes"]),
        "--cpus", str(limits["cpus"]), "--pids-limit", str(limits["pids_limit"]),
        "--mount", f"type=bind,src={root},dst=/incoming,readonly",
    ]
    for name, value in env.items():
        args.extend(["--env", name + "=" + value])
    args.extend([state["base_image"], "/bin/bash", "/incoming/Material/ci/container-build.sh"])
    execute(args)
    state["status"] = "BUILDING"
    save(state_path, state)
    started = time.monotonic()
    stop = threading.Event()
    resource_failures: list[str] = []
    monitor = threading.Thread(target=monitor_resources,
                               args=(root, state["container"], stop, resource_failures,
                                     state.get("docker_root", "/var/lib/docker")), daemon=True)
    monitor.start()
    try:
        attached = execute(["docker", "start", "--attach", state["container"]], check=False)
    finally:
        stop.set()
        monitor.join(timeout=20)
    inspection = execute(["docker", "inspect", state["container"]], capture=True, timeout=30)
    state.update(container_exit_metadata(json.loads(inspection.stdout)[0]))
    exit_code = state["container_exit_code"]
    state["docker_attach_exit_code"] = attached.returncode
    state["resource_abort"] = resource_failures
    state["build_container_seconds"] = round(time.monotonic() - started, 3)
    passed = (exit_code == 0 and attached.returncode == 0 and
              state["container_state"] == "exited" and not state["container_oom_killed"] and
              not resource_failures)
    state["status"] = "BUILT" if passed else "BUILD_FAILED"
    save(state_path, state)
    save(root / "Material/registry/resources-after-run.json", {
        "host": host_resources(root, state.get("docker_root")),
        "container": {key: value for key, value in state.items()
                      if key.startswith("container_") or key in ("resource_abort", "enforced_resources")},
    })
    print("MATERIAL_CONTAINER_RESULT " + json.dumps({key: state.get(key) for key in
          ("status", "container_exit_code", "container_oom_killed", "container_error", "resource_abort")}), flush=True)
    if not passed:
        raise RuntimeError(f"external container failed: exit={exit_code}, OOMKilled={state['container_oom_killed']}, "
                           f"resource_abort={resource_failures}")


def collect(root: Path, state_path: Path) -> None:
    registry = root / "Material/registry"
    registry.mkdir(parents=True, exist_ok=True)
    if not state_path.exists():
        save(registry / "transport.json", {"status": "PREPARE_FAILED", "container_started": False})
        return
    state = load(state_path)
    if "container" in state:
        monitor_path = registry / "host-monitor.jsonl"
        # Host samples are newer than any snapshot copied during source overlay.
        # A container-to-host evidence copy must not truncate this host-only log.
        host_monitor = monitor_path.read_bytes() if monitor_path.is_file() else None
        inspection = execute(["docker", "inspect", state["container"]], capture=True,
                             check=False, timeout=30)
        if inspection.returncode == 0:
            state.update(container_exit_metadata(json.loads(inspection.stdout)[0]))
            save(state_path, state)
        execute([
            "docker", "cp", state["container"] + ":/workspace/Material/registry/.", str(registry)
        ], check=False)
        if host_monitor is not None:
            monitor_path.write_bytes(host_monitor)
    save(registry / "transport.json", state)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        lines = [
            "## Material endpoint compilation",
            "",
            f"- Source: `{state['commit']}`",
            f"- Cache mode: `{state.get('restore_mode', 'not_started')}`",
            f"- Parent digest: `{state.get('parent_image_digest') or 'none'}`",
            f"- Container result: `{state.get('status')}`",
            f"- Container OOMKilled: `{state.get('container_oom_killed')}`",
            f"- Container exit: `{state.get('container_exit_code')}`",
            f"- Resource abort: `{state.get('resource_abort')}`",
            f"- Restore/bootstrap seconds: `{state.get('prepare_seconds')}`",
            f"- Container build/audit seconds: `{state.get('build_container_seconds')}`",
            "",
            "Compiler, exact-type, axiom and no-op rerun evidence: uploaded artifact.",
            "",
        ]
        with open(summary_path, "a") as stream:
            stream.write("\n".join(lines))


def expected_endpoint_ids(root: Path) -> set[str]:
    manifest = load(root / "Material/endpoints.json")
    endpoints = manifest.get("endpoints")
    if not isinstance(endpoints, list) or not endpoints:
        raise ValueError("checked-in endpoint manifest must be nonempty")
    identifiers = [endpoint.get("id") for endpoint in endpoints if isinstance(endpoint, dict)]
    if len(identifiers) != len(endpoints) or not all(
        isinstance(identifier, str) and re.fullmatch(r"[A-Za-z0-9_.-]+", identifier)
        for identifier in identifiers
    ):
        raise ValueError("checked-in endpoint manifest contains invalid identities")
    if len(set(identifiers)) != len(identifiers):
        raise ValueError("checked-in endpoint manifest contains duplicate identities")
    if manifest.get("endpoint_count") != len(identifiers):
        raise ValueError("checked-in endpoint count disagrees with its identities")
    return set(identifiers)


def validate_pass(report: dict, state: dict, expected_ids: set[str]) -> list[dict]:
    if (state.get("container_exit_code") != 0 or state.get("container_oom_killed")
            or state.get("resource_abort")):
        raise ValueError("publication requires a successful external container exit")
    if report.get("status") != "PASS" or report.get("commit") != state["commit"]:
        raise ValueError("publication requires PASS evidence for this exact source commit")
    endpoints = report.get("endpoints")
    if not isinstance(endpoints, list) or not endpoints:
        raise ValueError("publication requires a nonempty audited endpoint registry")
    seen = set()
    for endpoint in endpoints:
        if not isinstance(endpoint, dict) or endpoint.get("status") != "PASS":
            raise ValueError("every published endpoint must pass")
        identifier = endpoint.get("id")
        if not isinstance(identifier, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+", identifier):
            raise ValueError("invalid endpoint identifier")
        if identifier in seen:
            raise ValueError("duplicate endpoint identifier")
        seen.add(identifier)
        if not re.fullmatch(r"[0-9a-f]{64}", endpoint.get("input_hash", "")):
            raise ValueError("each endpoint needs its exact SHA256 input hash")
    if seen != expected_ids:
        raise ValueError(
            "endpoint report must exactly match the checked-in manifest: "
            f"missing={sorted(expected_ids - seen)}, extra={sorted(seen - expected_ids)}"
        )
    return endpoints


def github_json(state: dict, suffix: str) -> dict:
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        raise ValueError("branch ancestry verification requires the host GitHub token")
    url = f"https://api.github.com/repos/{state['repository']}/{suffix}"
    request = urllib.request.Request(url, headers={
        "Authorization": "Bearer " + token,
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    })
    with urllib.request.urlopen(request, timeout=30) as response:
        return json.load(response)


def current_branch_head(state: dict) -> str:
    branch = urllib.parse.quote(state["branch"], safe="")
    return github_json(state, f"git/ref/heads/{branch}")["object"]["sha"]


def is_ancestor(state: dict, base: str, head: str) -> bool:
    if not all(re.fullmatch(r"[0-9a-f]{40}", commit) for commit in (base, head)):
        raise ValueError("ancestry comparison requires exact source commits")
    if base == head:
        return True
    comparison = github_json(state, f"compare/{base}...{head}")
    status = comparison.get("status")
    if status not in {"ahead", "identical", "behind", "diverged"}:
        raise ValueError("unrecognized GitHub commit-comparison status")
    return status in {"ahead", "identical"}


def refreshed_pointer(state: dict) -> dict | None:
    """Inspect the remote pointer again after the potentially long build."""
    pulled = execute([
        "docker", "pull", "--platform", PLATFORM, state["pointer"]
    ], capture=True, check=False)
    if pulled.returncode:
        detail = ((pulled.stdout or "") + "\n" + (pulled.stderr or "")).lower()
        if any(marker in detail for marker in ("manifest unknown", "name unknown", "not found")):
            return None
        raise RuntimeError("cannot verify latest registry pointer; pointer update refused")
    inspection = execute(["docker", "image", "inspect", state["pointer"]], capture=True)
    info = json.loads(inspection.stdout)[0]
    if not compatible_image(info, state):
        raise ValueError("latest registry pointer does not identify a compatible passed image")
    commit = (info["Config"].get("Labels") or {}).get("org.opencontainers.image.revision", "")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("latest registry pointer lacks an exact source commit")
    digests = [value for value in info.get("RepoDigests", [])
               if value.startswith(state["image_repository"] + "@sha256:")]
    if not digests:
        raise ValueError("latest registry pointer lacks an immutable digest")
    return {"commit": commit, "digest": digests[0]}


def pointer_advance_allowed(state: dict, previous: dict | None, head: str) -> bool:
    candidate = state["commit"]
    if not is_ancestor(state, candidate, head):
        return False
    return previous is None or is_ancestor(state, previous["commit"], candidate)


def publish(root: Path, state_path: Path) -> None:
    state = load(state_path)
    report_path = root / "Material/registry/current.json"
    report = load(report_path)
    endpoints = validate_pass(report, state, expected_endpoint_ids(root))
    entry = {
        "schema": 1,
        "status": "PASS",
        "source_commit": state["commit"],
        "compatibility_key": state["compatibility_key"],
        "parent_image_digest": state["parent_image_digest"],
        "image_tag": state["immutable_tag"],
        "report_sha256": hashlib.sha256(report_path.read_bytes()).hexdigest(),
        "run_id": state["run_id"],
        "attempt": state["attempt"],
        "endpoint_tags": {},
    }
    for endpoint in endpoints:
        suffix = f"{slug(endpoint['id'])}-{endpoint['input_hash'][:12]}-{state['run_id']}-{state['attempt']}"
        entry["endpoint_tags"][endpoint["id"]] = state["image_repository"] + ":ep-" + suffix
    registry_path = root / "Material/registry/registry-entry.json"
    save(registry_path, entry)
    execute([
        "docker", "cp", str(registry_path),
        state["container"] + f":/opt/material-registry/{state['run_id']}-{state['attempt']}.json",
    ])
    labels = {
        LABEL_PREFIX + "status": "PASS",
        LABEL_PREFIX + "compatibility": state["compatibility_key"],
        LABEL_PREFIX + "endpoint-count": str(len(endpoints)),
        LABEL_PREFIX + "report-sha256": entry["report_sha256"],
        "org.opencontainers.image.source": "https://github.com/" + state["repository"],
        "org.opencontainers.image.revision": state["commit"],
    }
    args = ["docker", "commit"]
    for key, value in labels.items():
        args.extend(["--change", "LABEL " + key + "=" + json.dumps(value)])
    args.extend([state["container"], state["immutable_tag"]])
    execute(args)
    execute(["docker", "push", state["immutable_tag"]])
    for tag in entry["endpoint_tags"].values():
        execute(["docker", "tag", state["immutable_tag"], tag])
        execute(["docker", "push", tag])

    # A queued newer commit must be able to reuse this completed predecessor.
    # Refresh the registry pointer after the build, then advance only forward:
    # previous successful commit <= candidate <= current branch head.
    # Workflow branch concurrency serializes ordinary pointer publishers.
    head = current_branch_head(state)
    previous = refreshed_pointer(state)
    pointer_updated = pointer_advance_allowed(state, previous, head)
    if pointer_updated:
        execute(["docker", "tag", state["immutable_tag"], state["pointer"]])
        execute(["docker", "push", state["pointer"]])
    inspection = execute(["docker", "image", "inspect", state["immutable_tag"]], capture=True)
    info = json.loads(inspection.stdout)[0]
    digests = [v for v in info.get("RepoDigests", [])
               if v.startswith(state["image_repository"] + "@sha256:")]
    if not digests:
        raise RuntimeError("successful push did not produce a registry digest")
    entry.update(image_digest=digests[0], pointer=state["pointer"],
                 pointer_updated=pointer_updated, observed_branch_head=head,
                 observed_previous_pointer=previous)
    save(registry_path, entry)
    state.update(status="REGISTERED", published_digest=digests[0], pointer_updated=pointer_updated)
    save(state_path, state)
    save(root / "Material/registry/transport.json", state)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as stream:
            stream.write(f"\nRegistered passed image: `{digests[0]}`\n\n")
            stream.write(f"Endpoint tags: {len(endpoints)}. Branch pointer updated: {pointer_updated}.\n")


def cleanup(state_path: Path) -> None:
    if state_path.exists():
        state = load(state_path)
        if "container" in state:
            execute(["docker", "rm", "--force", state["container"]], check=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("prepare", "run", "collect", "publish", "cleanup"))
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        if args.command == "cleanup":
            cleanup(args.state)
        else:
            globals()[args.command](args.root.resolve(), args.state)
        return 0
    except (OSError, ValueError, RuntimeError, KeyError, json.JSONDecodeError, subprocess.SubprocessError) as exc:
        print(f"::error::{exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
