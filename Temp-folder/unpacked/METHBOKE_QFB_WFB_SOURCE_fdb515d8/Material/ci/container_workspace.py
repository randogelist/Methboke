#!/usr/bin/env python3
"""External CI transport: use passed dependency layers without exporting them.

The compiler driver, source/object receipts and fresh audits are unchanged.
This module transports current sources into an isolated container, then returns
evidence and verified own outputs. It never exports the dependency directory.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

import registry as r


ENVIRONMENT_KEYS = (
    'CI', 'GITHUB_SHA', 'GITHUB_REPOSITORY', 'GITHUB_RUN_ID',
    'GITHUB_RUN_ATTEMPT', 'GITHUB_REF_NAME', 'MATERIAL_JOBS',
    'LEAN_NUM_THREADS', 'MATERIAL_COMMAND_TIMEOUT',
    'MATERIAL_DEPENDENCY_CACHE_CLASS', 'MATERIAL_PROJECT_CACHE_CLASS',
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_external(environment):
    if environment.get('CI') != 'true' or environment.get('GITHUB_ACTIONS') != 'true':
        raise ValueError('container workspace execution is reserved for authorized GitHub CI')


def check_state(root, state, environment):
    require_external(environment)
    expected = {'commit': 'GITHUB_SHA', 'repository': 'GITHUB_REPOSITORY',
                'run_id': 'GITHUB_RUN_ID', 'branch': 'GITHUB_REF_NAME'}
    if any(state.get(key) != environment.get(value) for key, value in expected.items()):
        raise ValueError('container transport does not match the current external run')
    if state.get('attempt') != environment.get('GITHUB_RUN_ATTEMPT', '1'):
        raise ValueError('container transport attempt mismatch')
    parent = state.get('parent_image_digest', '')
    if (state.get('status') != 'PREPARED' or state.get('workspace_mode') != 'container_native'
            or state.get('restore_mode') != 'previous_passed_container'
            or not re.fullmatch(re.escape(state['image_repository']) + r'@sha256:[0-9a-f]{64}', parent)):
        raise ValueError('container workspace requires a prepared immutable passed parent')
    if state.get('compatibility_key') != r.compatibility(root):
        raise ValueError('current source compatibility differs from the prepared parent')
    previous = root / 'Material/registry/current.json'
    if digest(previous) != state.get('parent_report_sha256'):
        raise ValueError('authenticated parent report changed before execution')
    report = r.load(previous)
    if report.get('status') != 'PASS' or report.get('commit') != state.get('parent_commit'):
        raise ValueError('parent report is not the expected passed source')


def source_files(root):
    """Current source/evidence only; never traverse any .lake directory."""
    result = []
    for name in ('Material', 'LEAN_CUTOUTS'):
        source = root / name
        if not source.is_dir() or source.is_symlink():
            raise ValueError('source root is missing or a symlink: ' + name)
        for directory, dirs, files in os.walk(source, followlinks=False):
            folder = Path(directory)
            dirs[:] = sorted(d for d in dirs if d not in {'.lake', '__pycache__'})
            if any((folder / d).is_symlink() for d in dirs):
                raise ValueError('source directory symlinks are not allowed in the transport')
            for name in sorted(files):
                path = folder / name
                if name.endswith('.pyc'):
                    continue
                if not path.is_file() or path.is_symlink():
                    raise ValueError('source transport requires regular files: ' + str(path))
                result.append((path, path.relative_to(root)))
    return result


@contextmanager
def source_context(root, state):
    files = source_files(root)
    manifest = {relative.as_posix(): digest(path) for path, relative in files}
    plan = {'commit': state['commit'], 'parent_report_sha256': state['parent_report_sha256'],
            'files': manifest, 'dependency_directory_transferred': False}
    with tempfile.TemporaryDirectory(prefix='.material-input-', dir=root.parent) as temporary:
        payload = Path(temporary)
        for source, relative in files:
            target = payload / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            os.link(source, target)
        r.save(payload / 'transport-input.json', plan)
        yield payload, {'source_payload_bytes': sum(path.stat().st_size for path, _ in files),
                        'source_file_count': len(files),
                        'source_manifest_sha256': hashlib.sha256(json.dumps(manifest, sort_keys=True).encode()).hexdigest()}


def apply_input(payload, workspace, expected_report_hash):
    """Run inside the isolated container before invoking the compiler driver."""
    plan = r.load(payload / 'transport-input.json')
    if plan.get('parent_report_sha256') != expected_report_hash:
        raise ValueError('input plan differs from authenticated parent report')
    for previous in (workspace / 'Material/registry/current.json', payload / 'Material/registry/current.json'):
        if digest(previous) != expected_report_hash:
            raise ValueError('container or incoming parent report differs from authenticated identity')
    actual = {relative.as_posix(): digest(path) for path, relative in source_files(payload)}
    if actual != plan.get('files'):
        raise ValueError('source transport bytes differ from the prepared current source')
    material = workspace / 'Material'
    if not (material / '.lake/packages').is_dir() or not (material / '.lake/build').is_dir():
        raise ValueError('passed image lacks retained dependency or own object directories')
    for path in material.iterdir():
        if path.name != '.lake':
            if path.is_symlink() or path.is_file():
                path.unlink()
            else:
                shutil.rmtree(path)
    cutouts = workspace / 'LEAN_CUTOUTS'
    if cutouts.exists():
        if cutouts.is_symlink():
            cutouts.unlink()
        else:
            shutil.rmtree(cutouts)
    shutil.copytree(payload / 'Material', material, dirs_exist_ok=True)
    shutil.copytree(payload / 'LEAN_CUTOUTS', cutouts)


def resolve_toolchain(root):
    result = subprocess.run(['elan', 'which', 'lean'], cwd=root / 'Material',
                            text=True, capture_output=True, check=True)
    toolchain = Path(result.stdout.strip()).resolve().parent.parent
    if any(char in str(toolchain) for char in ',\n\r'):
        raise ValueError('unsupported compiler mount path')
    if not all(os.access(toolchain / 'bin' / name, os.X_OK) for name in ('lean', 'lake')):
        raise ValueError('pinned compiler mount does not contain executable Lean and Lake')
    return toolchain


def create_command(state, toolchain, environment):
    # Container root owns the inherited snapshot. No host workspace is mounted,
    # and the only host mount is the read-only compiler installation.
    args = ['docker', 'create', '--name', state['container'], '--user', '0:0',
            '--mount', f'type=bind,src={toolchain},dst=/opt/lean,readonly',
            '--workdir', '/workspace',
            '--env', 'PATH=/opt/lean/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
            '--env', 'HOME=/tmp/material-home',
            '--env', 'MATERIAL_EXECUTION_BACKEND=passed_container',
            '--env', 'MATERIAL_RESTORE_MODE=previous_passed_container',
            '--env', 'MATERIAL_PARENT_IMAGE_DIGEST=' + state['parent_image_digest'],
            '--env', 'MATERIAL_PARENT_REPORT_SHA256=' + state['parent_report_sha256'],
            '--env', 'GITHUB_ACTIONS=true']
    for name in ENVIRONMENT_KEYS:
        if name in environment:
            args += ['--env', name + '=' + environment[name]]
    args += [state['parent_image_digest'], '/bin/bash', '-c',
             'python3 /tmp/material-current/Material/ci/container_workspace.py '
             '--apply-input /tmp/material-current --workspace /workspace '
             '--parent-report-sha256 "$MATERIAL_PARENT_REPORT_SHA256" && '
             'mkdir -p "$HOME" && exec python3 Material/ci/native_build.py --jobs "$MATERIAL_JOBS"']
    return args


def verify_exported_objects(root, report, expected_modules):
    receipts = report.get('module_receipts')
    if not isinstance(receipts, dict) or set(receipts) != set(expected_modules):
        raise ValueError('exported object receipt scope differs from current source modules')
    output = root / 'Material/.lake/build/lib/lean'
    if not output.is_dir() or output.is_symlink():
        raise ValueError('own object export directory is absent or a symlink')
    for module, receipt in receipts.items():
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
            raise ValueError('invalid exported module name')
        artifact = output.joinpath(*module.split('.')).with_suffix('.olean')
        if (receipt.get('status') != 'PASS' or not artifact.is_file()
                or artifact.stat().st_size == 0 or not artifact.resolve().is_relative_to(output.resolve())):
            raise ValueError('exported object is missing or outside the own object directory: ' + module)
        if any(path.is_symlink() for path in (artifact, *artifact.parents)):
            raise ValueError('exported own objects must not use symlinks')
        companions = list(artifact.parent.glob(artifact.name + '*'))
        if any(p.is_symlink() or not p.is_file() for p in companions):
            raise ValueError('exported object companion is not a regular file')
        actual = {path.name: digest(path) for path in sorted(companions)}
        if receipt.get('olean_sha256') != digest(artifact) or receipt.get('object_files') != actual:
            raise ValueError('exported object bytes differ from accepted receipts: ' + module)
    return len(receipts)


def verify_current_report(root, state):
    import build
    import native_build
    import native_registry
    report = r.load(root / 'Material/registry/current.json')
    accepted_state = {**state, 'native_exit_code': 0}
    endpoints = r.validate_pass(report, accepted_state, r.expected_endpoint_ids(root))
    native_registry.validate_native_evidence(root, accepted_state, report, endpoints)
    expected = native_build.local_records(build.validate(root / 'Material'))
    return report, expected


def run(root, state_path, environment=None):
    environment = dict(os.environ if environment is None else environment)
    require_external(environment)
    state = r.load(state_path)
    started = time.monotonic()
    metadata = {'schema_version': 1, 'mode': 'container_native', 'commit': state.get('commit'),
                'parent_image_digest': state.get('parent_image_digest'), 'workspace': '/workspace',
                'transport_sha256': digest(Path(__file__)), 'dependency_export_bytes': 0,
                'own_objects_exported': False, 'own_receipts_verified': False,
                'status': 'PREPARING', 'local_lean_allowed': False}
    created = False
    started_container = False
    evidence_exported = False
    exit_code = 1
    try:
        check_state(root, state, environment)
        info = json.loads(r.execute(['docker', 'image', 'inspect', state['parent_image_digest']], capture=True).stdout)[0]
        labels = info.get('Config', {}).get('Labels') or {}
        if (not r.compatible_image(info, state)
                or labels.get(r.LABEL_PREFIX + 'report-sha256') != state['parent_report_sha256']
                or labels.get('org.opencontainers.image.revision') != state['parent_commit']):
            raise ValueError('container launch image no longer matches the authenticated passed parent')
        toolchain = resolve_toolchain(root)
        with source_context(root, state) as (payload, source_metrics):
            metadata.update(source_metrics)
            r.execute(create_command(state, toolchain, environment))
            created = True
            r.execute(['docker', 'cp', str(payload), state['container'] + ':/tmp/material-current'])
            started_container = True
            result = r.execute(['docker', 'start', '--attach', state['container']], check=False)
            info = json.loads(r.execute(['docker', 'inspect', state['container']], capture=True).stdout)[0]
            stopped = info.get('State') or {}
            exit_code = int(stopped.get('ExitCode', 1))
            if result.returncode or stopped.get('Running') or stopped.get('OOMKilled') or stopped.get('Status') != 'exited':
                exit_code = exit_code or 1
            metadata.update(compiler_exit_code=exit_code, container_state=stopped.get('Status'),
                            container_oom_killed=bool(stopped.get('OOMKilled')))
            evidence = root / 'Material/registry'
            evidence.mkdir(parents=True, exist_ok=True)
            r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/registry/.', str(evidence)])
            evidence_exported = True
            if exit_code == 0:
                report, expected = verify_current_report(root, state)
                output = root / 'Material/.lake/build'
                output.mkdir(parents=True, exist_ok=True)
                r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/.lake/build/.', str(output)])
                count = verify_exported_objects(root, report, expected)
                metadata.update(own_objects_exported=True, own_receipts_verified=True,
                                verified_own_module_count=count, status='VERIFIED')
            else:
                metadata['status'] = 'BUILD_FAILED'
    except Exception as error:
        exit_code = 1
        metadata.update(status='TRANSPORT_FAILED', error=str(error))
        print('MATERIAL_WORKSPACE_FAILURE ' + str(error), flush=True)
    finally:
        if created:
            # A transport/inspection error must not discard the compiler's logs.
            # This recovery can preserve evidence but can never turn failure into PASS.
            if started_container and not evidence_exported:
                try:
                    evidence = root / 'Material/registry'
                    evidence.mkdir(parents=True, exist_ok=True)
                    result = r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/registry/.', str(evidence)], check=False)
                    metadata['failure_evidence_exported'] = result.returncode == 0
                except Exception as error:
                    metadata['failure_evidence_export_error'] = str(error)
            try:
                r.execute(['docker', 'rm', '--force', state['container']], check=False, timeout=30)
            except Exception as error:
                exit_code = 1
                metadata.update(status='TRANSPORT_FAILED', cleanup_error=str(error))
        metadata['total_seconds'] = round(time.monotonic() - started, 3)
        metadata['exit_code'] = exit_code
        state['container_workspace'] = metadata
        r.save(state_path, state)
        r.save(root / 'Material/registry/container-workspace.json', metadata)
    return exit_code


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--state', type=Path)
    parser.add_argument('--apply-input', type=Path)
    parser.add_argument('--workspace', type=Path, default=Path('/workspace'))
    parser.add_argument('--parent-report-sha256')
    args = parser.parse_args()
    if args.apply_input:
        require_external(os.environ)
        apply_input(args.apply_input.resolve(), args.workspace.resolve(), args.parent_report_sha256)
    else:
        if args.state is None:
            parser.error('--state is required for external workspace execution')
        raise SystemExit(run(args.root.resolve(), args.state))
