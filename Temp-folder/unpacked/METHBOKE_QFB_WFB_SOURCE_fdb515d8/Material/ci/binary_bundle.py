#!/usr/bin/env python3
"""Package verified native project objects for external CI artifact upload.

Archive paths are repository-relative: Material/.lake/build/lib/lean/... and
Material/registry/{current.json,audits/...,logs/cutouts-audit.log}. Dependencies
are restored separately. This command neither runs Lean nor publishes remotely.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import tarfile
import time

import build
import container_workspace
import native_build
import native_registry
import registry as r


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def reject_symlinks(path):
    if any(p.is_symlink() for p in (path, *path.parents)):
        raise ValueError('binary bundle paths must not contain symlinks')


def safe_file(root, relative):
    relative = Path(relative)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('binary member must be repository-relative')
    path = root / relative
    reject_symlinks(path)
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError('binary member is missing or outside the repository')
    return path


def validate(root, state, environment, require_full_rebuild=False):
    container_workspace.require_external(environment)
    expected = r.metadata(root, environment)
    for key in ('repository', 'commit', 'branch', 'run_id', 'attempt', 'compatibility_key'):
        if state.get(key) != expected[key]:
            raise ValueError('binary publication does not match current run: ' + key)
    if (state.get('status') != 'BUILT' or state.get('execution_backend') != 'native'
            or state.get('native_exit_code') != 0 or state.get('compiler_location') != 'native_host'):
        raise ValueError('binary publication requires a successful native host build')
    report_path = safe_file(root, 'Material/registry/current.json')
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    if report.get('execution_backend') != 'native_host':
        raise ValueError('binary trial requires native host verification')
    if report.get('run_url') != 'https://github.com/' + state['repository'] + '/actions/runs/' + state['run_id']:
        raise ValueError('binary report belongs to a different external run')
    endpoints = r.validate_pass(report, state, r.expected_endpoint_ids(root))
    native_registry.validate_native_evidence(root, state, report, endpoints)
    expected_modules = native_build.local_records(build.validate(root / 'Material'))
    container_workspace.verify_exported_objects(root, report, expected_modules)
    if require_full_rebuild:
        receipts = report['module_receipts']
        count = len(expected_modules)
        metrics = report.get('metrics', {})
        if (not count or any(receipt.get('status') != 'PASS' or receipt.get('reused') is not False
                             for receipt in receipts.values())
                or metrics.get('module_count') != count
                or metrics.get('fresh_module_count') != count
                or metrics.get('reused_module_count') != 0):
            raise ValueError('recovery publication requires every current project module freshly rebuilt')
        if report.get('cache_hydration', {}).get('mode') != 'official_cache_get':
            raise ValueError('recovery publication requires the pinned official dependency bootstrap')
    if report_path.read_bytes() != report_bytes:
        raise ValueError('accepted report changed during validation')
    return report, sha256(report_bytes)


def members(root, report, report_sha):
    """Only current receipt-bound objects and required fresh evidence are included."""
    result = {'Material/registry/current.json': report_sha}
    for module, receipt in report['module_receipts'].items():
        parent = Path('Material/.lake/build/lib/lean').joinpath(*module.split('.')).parent
        for filename, digest in receipt['object_files'].items():
            if Path(filename).name != filename:
                raise ValueError('object companion name is not a basename')
            result[(parent / filename).as_posix()] = digest
    for endpoint in report['endpoints'] + [report['cutout']]:
        relative = Path('Material') / endpoint['audit_log']
        result[relative.as_posix()] = endpoint['audit_sha256']
    for relative, digest in result.items():
        if sha256(safe_file(root, relative).read_bytes()) != digest:
            raise ValueError('binary member differs from accepted receipt: ' + relative)
    return result


def pack(root, expected, destination):
    manifest = {}
    with destination.open('xb') as output, gzip.GzipFile(fileobj=output, mode='wb', compresslevel=1, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w', format=tarfile.PAX_FORMAT) as archive:
            for relative, digest in sorted(expected.items()):
                data = safe_file(root, relative).read_bytes()
                if sha256(data) != digest:
                    raise ValueError('binary member changed during packaging: ' + relative)
                info = tarfile.TarInfo(relative)
                info.size = len(data)
                info.mode = 0o644
                info.mtime = 0
                archive.addfile(info, io.BytesIO(data))
                manifest[relative] = {'sha256': digest, 'bytes': len(data)}
    return manifest


def run(root, state_path, output_dir, environment=None, *, artifact_suffix='', require_full_rebuild=False):
    if artifact_suffix not in ('', 'fast', 'recovery'):
        raise ValueError('binary artifact suffix must be empty, fast or recovery')
    if artifact_suffix == 'recovery' and not require_full_rebuild:
        raise ValueError('recovery artifact requires full rebuild validation')
    suffix = '-' + artifact_suffix if artifact_suffix else ''
    environment = dict(os.environ if environment is None else environment)
    root = Path(root).absolute()
    output_dir = Path(output_dir).absolute()
    reject_symlinks(root)
    reject_symlinks(output_dir)
    root, output_dir = root.resolve(), output_dir.resolve()
    if output_dir.is_relative_to(root) or root.is_relative_to(output_dir):
        raise ValueError('binary output directory must be outside the repository')
    if output_dir.exists() and (not output_dir.is_dir() or any(output_dir.iterdir())):
        raise ValueError('binary output directory must be empty')
    state = r.load(state_path)
    container_workspace.require_external(environment)
    entry_path = root / 'Material/registry/binary-entry.json'
    reject_symlinks(entry_path)
    entry = {'schema_version': 1, 'status': 'PREPARING', 'commit': environment.get('GITHUB_SHA'),
             'run_id': environment.get('GITHUB_RUN_ID'), 'attempt': environment.get('GITHUB_RUN_ATTEMPT', '1'),
             'remote_upload_verified': False, 'local_lean_allowed': False}
    r.save(entry_path, entry)
    started, cpu_started = time.monotonic(), time.process_time()
    created = []
    try:
        report, report_sha = validate(root, state, environment, require_full_rebuild)
        selected = members(root, report, report_sha)
        verified = time.monotonic()
        output_dir.mkdir(parents=True, exist_ok=True)
        name = 'material-project-' + state['commit'][:12] + '-' + state['run_id'] + '-' + state['attempt'] + suffix + '.tar.gz'
        archive = output_dir / name
        created.append(archive)
        file_manifest = pack(root, selected, archive)
        archive_sha = sha256(archive.read_bytes())
        metadata = {'schema_version': 1, 'status': 'READY_FOR_UPLOAD', 'repository': state['repository'],
            'commit': state['commit'], 'branch': state['branch'], 'run_id': state['run_id'], 'attempt': state['attempt'],
            'run_url': report['run_url'], 'artifact_name': 'material-binary-' + state['commit'] + '-' + state['run_id'] + '-' + state['attempt'] + suffix,
            'worker_mode': artifact_suffix or 'legacy', 'full_project_rebuild_verified': require_full_rebuild,
            'archive_name': name, 'archive_sha256': archive_sha, 'archive_bytes': archive.stat().st_size,
            'compression': 'gzip-level-1', 'archive_layout': 'repository-relative; current own .olean* objects and fresh evidence only',
            'report_sha256': selected['Material/registry/current.json'],
            'dependency_identity': native_registry.dependency_identity(report), 'compiler': report['compiler'],
            'build_configuration': report['build_configuration'], 'module_count': len(report['module_receipts']),
            'own_object_bytes': sum(v['bytes'] for p, v in file_manifest.items() if p.startswith('Material/.lake/build/')),
            'member_bytes': sum(v['bytes'] for v in file_manifest.values()), 'member_count': len(file_manifest),
            'members': file_manifest, 'dependency_archive_included': False, 'fresh_required_audits': True,
            'verification_seconds': round(verified - started, 3), 'packaging_seconds': round(time.monotonic() - verified, 3),
            'total_seconds': round(time.monotonic() - started, 3), 'cpu_seconds': round(time.process_time() - cpu_started, 3),
            'remote_upload_verified': False, 'local_lean_allowed': False}
        manifest_path = output_dir / 'manifest.json'
        created.append(manifest_path)
        r.save(manifest_path, metadata)
        entry.update({key: value for key, value in metadata.items() if key != 'members'})
        entry['manifest_sha256'] = sha256(manifest_path.read_bytes())
        r.save(entry_path, entry)
        print('MATERIAL_BINARY_BUNDLE ' + json.dumps(entry, sort_keys=True), flush=True)
        return entry
    except Exception as exc:
        for path in created:
            if path.is_file() and not path.is_symlink():
                path.unlink()
        entry.update(status='REJECTED', error=str(exc), total_seconds=round(time.monotonic() - started, 3))
        r.save(entry_path, entry)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--artifact-suffix', choices=('fast', 'recovery'), default='')
    parser.add_argument('--require-full-rebuild', action='store_true')
    args = parser.parse_args()
    run(args.root, args.state, args.output_dir, artifact_suffix=args.artifact_suffix,
        require_full_rebuild=args.require_full_rebuild)


if __name__ == '__main__':
    main()
