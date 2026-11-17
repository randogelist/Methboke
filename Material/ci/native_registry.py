#!/usr/bin/env python3
"""Native CI restoration/publication of immutable passed-source/object snapshots."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
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
                target = root / 'Material/.lake'
                target.mkdir(parents=True, exist_ok=True)
                r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/.lake/.', str(target)])
                r.execute(['docker', 'cp', state['container'] + ':/workspace/Material/registry/current.json', str(root / 'Material/registry/current.json')])
                restored_report = root / 'Material/registry/current.json'
                labels = info['Config'].get('Labels') or {}
                if hashlib.sha256(restored_report.read_bytes()).hexdigest() != labels.get(r.LABEL_PREFIX + 'report-sha256'):
                    raise ValueError('restored PASS report digest disagrees with snapshot label')
                if r.load(restored_report).get('commit') != labels.get('org.opencontainers.image.revision'):
                    raise ValueError('restored PASS report source disagrees with snapshot revision')
                restored = True
                state['restore_mode'] = 'previous_passed_container'
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


def publish(root, state_path):
    state = r.load(state_path)
    report_path = root / 'Material/registry/current.json'
    report = r.load(report_path)
    endpoints = r.validate_pass(report, state, r.expected_endpoint_ids(root))
    validate_native_evidence(root, state, report, endpoints)
    # Transfer archives are not required for installed-output reuse.
    for path in (root / 'Material/.lake').rglob('*.ltar'):
        path.unlink()
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
    args = ['docker', 'build', '--file', str(root / 'Material/ci/Snapshot.Dockerfile'), '--tag', state['immutable_tag']]
    for key, value in labels.items():
        args += ['--label', key + '=' + value]
    r.execute(args + [str(root)])
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
