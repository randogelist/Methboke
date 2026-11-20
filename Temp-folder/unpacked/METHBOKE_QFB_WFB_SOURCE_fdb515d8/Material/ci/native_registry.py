#!/usr/bin/env python3
"""Native CI restoration/publication of immutable passed-source/object snapshots."""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tempfile
import time

import registry as r


def outputs(values):
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
            for key, value in values.items():
                stream.write(f'{key}={value}\n')


def cache_keys(root):
    dep = hashlib.sha256()
    for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'ci/cache-contract.json'):
        dep.update(name.encode() + b'\0' + (root / 'Material' / name).read_bytes())
    dep.update(b'ubuntu-24.04-linux-x86_64-native-v1')
    identity = dep.hexdigest()
    own = hashlib.sha256()
    paths = list((root / 'Material').rglob('*.lean')) + list((root / 'Material').glob('*/endpoint.json'))
    paths += list((root / 'Material/ci').glob('*.py'))
    paths += list((root / 'Material/ci').glob('*.sh'))
    paths += list((root / 'LEAN_CUTOUTS').glob('*.lean'))
    paths += [p for p in (root / 'Material/owned-sources.json',) if p.is_file()]
    for path in sorted(p for p in paths if '.lake' not in p.parts and 'registry' not in p.parts):
        own.update(path.relative_to(root).as_posix().encode() + b'\0' + path.read_bytes())
    return {'dependency_key': 'material-deps-' + identity,
            'project_prefix': 'material-project-' + identity + '-',
            'project_key': 'material-project-' + identity + '-' + own.hexdigest()}


def prepare(root, state_path, benchmark=False):
    started = time.monotonic()
    state = r.metadata(root, os.environ)
    state.update(execution_backend='native', status='PREPARING', parent_image_digest=None,
                 restore_mode='actions_cache_or_seed', **cache_keys(root))
    r.save(state_path, state)
    restored = False
    if not benchmark:
        pulled = r.execute(['docker', 'pull', '--platform', r.PLATFORM, state['pointer']], capture=True, check=False)
        if pulled.returncode == 0:
            info = json.loads(r.execute(['docker', 'image', 'inspect', state['pointer']], capture=True).stdout)[0]
            if not r.compatible_image(info, state):
                raise ValueError('registry pointer does not identify a compatible passed snapshot')
            digests = [d for d in info.get('RepoDigests', []) if d.startswith(state['image_repository'] + '@sha256:')]
            if not digests:
                raise ValueError('passed snapshot lacks immutable digest')
            state['parent_image_digest'] = digests[0]
            r.execute(['docker', 'create', '--name', state['container'], digests[0], '/snapshot-only'])
            try:
                # Dependencies and own objects remain in the immutable image.
                # The external workspace runner exports only freshly verified own outputs.
                (root / 'Material/registry').mkdir(parents=True, exist_ok=True)
                r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/registry/current.json', str(root / 'Material/registry/current.json')])
                restored_report = root / 'Material/registry/current.json'
                labels = info['Config'].get('Labels') or {}
                if hashlib.sha256(restored_report.read_bytes()).hexdigest() != labels.get(r.LABEL_PREFIX + 'report-sha256'):
                    raise ValueError('restored PASS report digest disagrees with snapshot label')
                parent_report = r.load(restored_report)
                if parent_report.get('commit') != labels.get('org.opencontainers.image.revision'):
                    raise ValueError('restored PASS report source disagrees with snapshot revision')
                state['parent_report_sha256'] = hashlib.sha256(restored_report.read_bytes()).hexdigest()
                state['parent_commit'] = parent_report['commit']
                state['parent_dependency_identity'] = dependency_identity(parent_report)
                restored = True
                state['restore_mode'] = 'previous_passed_container'
                state['workspace_mode'] = 'container_native'
            finally:
                r.execute(['docker', 'rm', state['container']], check=False)
            # Retain this exact immutable image: the amendment build executes inside it.
        else:
            detail = ((pulled.stdout or '') + '\n' + (pulled.stderr or '')).lower()
            if not any(s in detail for s in ('manifest unknown', 'name unknown', 'not found', 'denied')):
                raise RuntimeError('registry lookup failed; refusing to mislabel network failure as cache miss')
            print('MATERIAL_REGISTRY_MISS: using compatible Actions caches or official dependency seed', flush=True)
    state.update(status='PREPARED', prepare_seconds=round(time.monotonic() - started, 3))
    r.save(state_path, state)
    outputs({**cache_keys(root), 'registry_restored': str(restored).lower(),
             'restore_mode': state['restore_mode'], 'parent_image_digest': state['parent_image_digest'] or ''})


def record(root, state_path, exit_code):
    state = r.load(state_path)
    state.update(native_exit_code=exit_code, status='BUILT' if exit_code == 0 else 'BUILD_FAILED',
                 compiler_location='passed_container' if state.get('restore_mode') == 'previous_passed_container' else 'native_host')
    try:
        if exit_code == 0:
            report = r.load(root / 'Material/registry/current.json')
            if state.get('workspace_mode') == 'container_native':
                workspace = state.get('container_workspace') or {}
                if (workspace.get('status') != 'VERIFIED' or workspace.get('exit_code') != 0
                        or workspace.get('commit') != state['commit']
                        or workspace.get('own_receipts_verified') is not True
                        or workspace.get('verified_own_module_count') != len(report.get('module_receipts', {}))):
                    raise ValueError('container-native result lacks verified current own-object exports')
            endpoints = r.validate_pass(report, state, r.expected_endpoint_ids(root))
            validate_native_evidence(root, state, report, endpoints)
    except Exception:
        state.update(status='EVIDENCE_REJECTED', native_exit_code=1)
        raise
    finally:
        r.save(state_path, state)
        r.save(root / 'Material/registry/transport.json', state)


def validate_native_evidence(root, state, report, endpoints):
    """Recheck exact fresh audit coverage and bytes before cache publication."""
    import build
    material = root / 'Material'
    plan = build.validate(material)
    if (report.get('compiler_executed') is not True
            or report.get('all_endpoints_selected') is not True
            or report.get('fresh_required_audits') is not True
            or report.get('toolchain') != plan['toolchain']
            or report.get('mathlib_commit') != plan['mathlib_commit']
            or report.get('build_configuration') != plan['config']):
        raise ValueError('publication requires matching compiler, pins, policy and full fresh scope')
    specs = {e['id']: e['spec'] for e in plan['endpoints']}
    if {e['id'] for e in endpoints} != set(specs):
        raise ValueError('published endpoint set differs from current source manifests')

    def check_log(record, names, allowed, expected_log=None):
        if (record.get('status') != 'PASS' or record.get('audit_reused') is not False
                or record.get('audit_origin_commit') != state['commit']):
            raise ValueError('publication requires a fresh audit of the current exact commit')
        relative = record.get('audit_log')
        if not isinstance(relative, str) or (expected_log and relative != expected_log):
            raise ValueError('audit log identity differs from required evidence')
        log = build.inside(material, relative)
        if not log.is_relative_to(material / 'registry') or not log.is_file():
            raise ValueError('required audit log is absent or outside the evidence directory')
        data = log.read_bytes()
        if build.sha256(data) != record.get('audit_sha256'):
            raise ValueError('audit log bytes differ from the accepted report')
        parsed = build.parse_audit(data.decode('utf-8'), names, set(allowed))
        if record.get('types') != parsed['types'] or record.get('axioms') != parsed['axioms']:
            raise ValueError('reported theorem types or axioms differ from fresh compiler evidence')

    for endpoint in endpoints:
        spec = specs[endpoint['id']]
        names = [d['name'] for d in spec['declarations']]
        if endpoint.get('declaration_count') != len(names):
            raise ValueError('published declaration count differs from required manifest scope')
        check_log(endpoint, names, spec['allowed_axioms'])
    cutout = root / 'LEAN_CUTOUTS/Cutouts.lean'
    cutout_record = report.get('cutout', {})
    if not cutout.is_file() or build.sha256(cutout.read_bytes()) != cutout_record.get('source_sha256'):
        raise ValueError('single-file QFB cutout is missing or differs from the freshly audited source')
    check_log(cutout_record, ['QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED'],
              build.STANDARD_AXIOMS, 'registry/logs/cutouts-audit.log')


def dependency_identity(report):
    """Identity of the installed dependencies inherited by a warm image layer."""
    if (report.get('status') != 'PASS' or report.get('compiler_executed') is not True
            or report.get('all_endpoints_selected') is not True):
        raise ValueError('dependency inheritance requires a complete passed report')
    fields = ('toolchain', 'mathlib_commit', 'compiler', 'platform',
              'verified_dependencies', 'external_objects')
    identity = {name: report.get(name) for name in fields}
    if any(not value for value in identity.values()):
        raise ValueError('passed report lacks dependency inheritance identity')
    objects = identity['external_objects']
    if (not isinstance(objects, dict) or not isinstance(objects.get('count'), int)
            or objects['count'] <= 0
            or not re.fullmatch('[0-9a-f]{64}', str(objects.get('sha256', '')))):
        raise ValueError('passed report lacks a complete dependency object digest')
    config = report.get('build_configuration') or {}
    keys = ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean')
    identity['dependency_configuration'] = {key: config.get(key) for key in keys}
    if any(not re.fullmatch('[0-9a-f]{64}', str(value or ''))
           for value in identity['dependency_configuration'].values()):
        raise ValueError('passed report lacks pinned dependency configuration hashes')
    return copy.deepcopy(identity)


def snapshot_mode(state, report):
    """Do not silently duplicate a loaded parent when its dependencies changed."""
    parent = state.get('parent_image_digest')
    if not parent:
        if state.get('restore_mode') == 'previous_passed_container':
            raise ValueError('restored snapshot lacks immutable parent identity')
        return 'cold_seed'
    expected = re.escape(state['image_repository']) + r'@sha256:[0-9a-f]{64}'
    if (state.get('restore_mode') != 'previous_passed_container'
            or not re.fullmatch(expected, parent)):
        raise ValueError('warm publication requires the exact restored immutable parent')
    if (not re.fullmatch('[0-9a-f]{40}', str(state.get('parent_commit', '')))
            or not re.fullmatch('[0-9a-f]{64}', str(state.get('parent_report_sha256', '')))):
        raise ValueError('warm publication lacks authenticated parent report identity')
    if (report.get('cache_hydration') or {}).get('mode') != 'retained_passed_outputs':
        raise ValueError('warm publication requires unchanged retained dependency outputs; a separate cold seed is required')
    if state.get('parent_dependency_identity') != dependency_identity(report):
        raise ValueError('inherited dependency identity changed; a separate cold seed is required')
    return 'inherited_dependencies'


def snapshot_files(root, mode):
    """Whitelist snapshot inputs; never stage the repository or dependency tree twice."""
    selected = []
    for top in ('Material', 'LEAN_CUTOUTS'):
        source = root / top
        if not source.is_dir() or source.is_symlink():
            raise ValueError('snapshot source directory is missing or is a symlink: ' + top)
        for directory, dirs, files in os.walk(source, followlinks=False):
            folder = Path(directory)
            dirs[:] = sorted(name for name in dirs if name != '__pycache__'
                and not (mode == 'inherited_dependencies'
                         and folder == root / 'Material/.lake' and name == 'packages'))
            # COPY preserves safe relative symlinks; never follow paths outside the snapshot.
            symlinks = [name for name in dirs if (folder / name).is_symlink()]
            dirs[:] = [name for name in dirs if name not in symlinks]
            for name in sorted(files + symlinks):
                path = folder / name
                if (name.endswith(('.ltar', '.pyc'))
                        or path == root / 'Material/registry/snapshot-plan.json'):
                    continue
                if path.is_symlink():
                    target = os.readlink(path)
                    if os.path.isabs(target) or not path.resolve().is_relative_to(root):
                        raise ValueError('snapshot symlink leaves the repository: ' + str(path))
                elif not path.is_file():
                    raise ValueError('snapshot input is not a regular file: ' + str(path))
                selected.append((path, path.relative_to(root)))
    return selected


def warm_dockerfile(parent):
    # Replace old source and own outputs so removed files cannot survive a COPY
    # overlay. The large verified dependency directory remains in its parent layer.
    cleanup = (
        "from pathlib import Path; import shutil; "
        "m=Path('/workspace/Material'); l=m/'.lake'; "
        "drop=lambda p: p.unlink() if p.is_symlink() or p.is_file() else shutil.rmtree(p); "
        "[drop(p) for p in m.iterdir() if p.name != '.lake']; "
        "[drop(p) for p in l.iterdir() if p.name != 'packages']; "
        "shutil.rmtree('/workspace/LEAN_CUTOUTS', ignore_errors=True)"
    )
    return ('# Inherit verified dependency bytes; no compiler runs while packaging.\n'
            + 'FROM ' + parent + '\nUSER root\n'
            + 'RUN ' + json.dumps(['python3', '-c', cleanup]) + '\n'
            + 'COPY Material /workspace/Material\n'
            + 'COPY LEAN_CUTOUTS /workspace/LEAN_CUTOUTS\n'
            + 'WORKDIR /workspace\n'
            + 'CMD ["python3", "Material/ci/native_build.py", "--jobs", "2"]\n')


def snapshot_disk_budget(root, context_bytes, file_count):
    """Leave room for BuildKit context, new layer/export and runner evidence."""
    info = json.loads(r.execute(['docker', 'info', '--format', '{{json .}}'],
                                capture=True, timeout=30).stdout)
    docker_root = Path(info.get('DockerRootDir') or '/var/lib/docker')
    # Staging uses hardlinks on the workspace filesystem, not a third data copy.
    # Three payloads reserve context/layer/export peaks; 2 GiB protects job evidence.
    required = 3 * context_bytes + 4096 * file_count + 2 * r.GIB
    disks = {}
    for label, path in (('workspace', root), ('docker', docker_root)):
        usage = shutil.disk_usage(path)
        disks[label] = {'path': str(path), 'free_bytes': usage.free,
                        'required_free_bytes': required}
    return {'context_bytes': context_bytes, 'context_file_count': file_count,
            'required_free_bytes': required, 'disks': disks,
            'sufficient': all(d['free_bytes'] >= required for d in disks.values()),
            'policy': '3*context_bytes + 4096*file_count + 2GiB; hardlink staging'}


@contextmanager
def snapshot_context(root, state, report):
    mode = snapshot_mode(state, report)
    files = snapshot_files(root, mode)
    size = sum(len(os.readlink(p).encode()) if p.is_symlink() else p.stat().st_size
               for p, _ in files)
    metrics = snapshot_disk_budget(root, size, len(files))
    metrics.update(mode=mode, parent_image_digest=state.get('parent_image_digest'),
                   inherited_dependency_objects=report['external_objects'] if mode == 'inherited_dependencies' else None)
    r.save(root / 'Material/registry/snapshot-plan.json', metrics)
    state['snapshot_publication'] = metrics
    if not metrics['sufficient']:
        raise ValueError('insufficient disk for snapshot publication; no Docker build or cache deletion performed')
    # Keep the temporary directory on the same filesystem so regular files can
    # be hardlinked. Cleanup affects staging links only, never source/cache bytes.
    with tempfile.TemporaryDirectory(prefix='.material-snapshot-', dir=root.parent) as temporary:
        context = Path(temporary)
        for source, relative in files:
            target = context / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if source.is_symlink():
                target.symlink_to(os.readlink(source))
            else:
                os.link(source, target)
        # The plan was written after file enumeration; include it deliberately.
        plan = context / 'Material/registry/snapshot-plan.json'
        plan.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / 'Material/registry/snapshot-plan.json', plan)
        dockerfile = context / 'Snapshot.Dockerfile'
        if mode == 'inherited_dependencies':
            dockerfile.write_text(warm_dockerfile(state['parent_image_digest']))
        else:
            shutil.copyfile(root / 'Material/ci/Snapshot.Dockerfile', dockerfile)
        yield context, dockerfile, metrics


def publish(root, state_path):
    state = r.load(state_path)
    report_path = root / 'Material/registry/current.json'
    report = r.load(report_path)
    endpoints = r.validate_pass(report, state, r.expected_endpoint_ids(root))
    validate_native_evidence(root, state, report, endpoints)
    entry = {'schema': 2, 'status': 'PASS', 'execution_backend': 'native',
        'source_commit': state['commit'], 'compatibility_key': state['compatibility_key'],
        'parent_image_digest': state['parent_image_digest'], 'image_tag': state['immutable_tag'],
        'report_sha256': hashlib.sha256(report_path.read_bytes()).hexdigest(),
        'run_id': state['run_id'], 'attempt': state['attempt'], 'endpoint_tags': {}}
    for endpoint in endpoints:
        entry['endpoint_tags'][endpoint['id']] = state['image_repository'] + ':ep-' + r.slug(endpoint['id']) + '-' + endpoint['input_hash'][:12] + '-' + state['run_id'] + '-' + state['attempt']
    entry_path = root / 'Material/registry/registry-entry.json'
    r.save(entry_path, entry)
    labels = {r.LABEL_PREFIX + 'status': 'PASS', r.LABEL_PREFIX + 'compatibility': state['compatibility_key'],
        r.LABEL_PREFIX + 'endpoint-count': str(len(endpoints)), r.LABEL_PREFIX + 'report-sha256': entry['report_sha256'],
        'org.opencontainers.image.source': 'https://github.com/' + state['repository'],
        'org.opencontainers.image.revision': state['commit']}
    try:
        with snapshot_context(root, state, report) as (context, dockerfile, metrics):
            entry['snapshot_publication'] = metrics
            r.save(entry_path, entry)
            # Refresh this small record after staging; dependency objects are inherited.
            shutil.copyfile(entry_path, context / 'Material/registry/registry-entry.json')
            args = ['docker', 'build', '--file', str(dockerfile), '--tag', state['immutable_tag']]
            for key, value in labels.items():
                args += ['--label', key + '=' + value]
            r.execute(args + [str(context)])
    except Exception:
        state['status'] = 'PUBLICATION_FAILED'
        raise
    finally:
        r.save(state_path, state)
        r.save(root / 'Material/registry/transport.json', state)
    r.execute(['docker', 'push', state['immutable_tag']])
    for tag in entry['endpoint_tags'].values():
        r.execute(['docker', 'tag', state['immutable_tag'], tag])
        r.execute(['docker', 'push', tag])
    head = r.current_branch_head(state)
    previous = r.refreshed_pointer(state)
    advanced = r.pointer_advance_allowed(state, previous, head)
    if advanced:
        r.execute(['docker', 'tag', state['immutable_tag'], state['pointer']])
        r.execute(['docker', 'push', state['pointer']])
    info = json.loads(r.execute(['docker', 'image', 'inspect', state['immutable_tag']], capture=True).stdout)[0]
    digests = [d for d in info.get('RepoDigests', []) if d.startswith(state['image_repository'] + '@sha256:')]
    if not digests:
        raise ValueError('successful push did not yield immutable digest')
    entry.update(image_digest=digests[0], pointer=state['pointer'], pointer_updated=advanced,
                 observed_branch_head=head, observed_previous_pointer=previous)
    r.save(entry_path, entry)
    state.update(status='REGISTERED', published_digest=digests[0], pointer_updated=advanced)
    r.save(state_path, state)
    r.save(root / 'Material/registry/transport.json', state)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
            stream.write(f"Native compilation and fresh audits: PASS.\n\nPassed snapshot: `{digests[0]}`\n")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['prepare', 'record', 'publish'])
    parser.add_argument('--root', type=Path, default=Path.cwd())
    parser.add_argument('--state', type=Path, required=True)
    parser.add_argument('--benchmark', action='store_true')
    parser.add_argument('--exit-code', type=int, default=1)
    args = parser.parse_args()
    if args.command == 'prepare': prepare(args.root.resolve(), args.state, args.benchmark)
    elif args.command == 'record': record(args.root.resolve(), args.state, args.exit_code)
    else: publish(args.root.resolve(), args.state)
