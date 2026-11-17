#!/usr/bin/env python3
"""External native CI: dependency objects, receipt-checked own modules, fresh audits.

No Mathlib source target is ever passed to a compiler/build command. `lake exe
cache get` is the only bootstrap operation; subsequent Lean commands elaborate
only checked-in Material modules and audits. Compilation is forbidden locally.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import time

import build


def local_records(plan):
    audits = {e['spec']['audit_module'] for e in plan['endpoints']}
    return {r['module']: r for e in plan['endpoints'] for r in e['files']
            if r['module'] not in audits}


def object_digest(path):
    return build.sha256(path.read_bytes()) if path.is_file() else None


def object_files(artifact):
    return {p.name: object_digest(p) for p in sorted(artifact.parent.glob(artifact.name + '*')) if p.is_file()}


def receipt_matches(old, identity, artifact):
    return (isinstance(old, dict) and old.get('identity') == identity
            and artifact.is_file() and artifact.stat().st_size > 0
            and old.get('olean_sha256') == object_digest(artifact)
            and old.get('object_files') == object_files(artifact))


def schedule(records, context, old, output, worker, jobs=2):
    """Dependency-frontier scheduling; failures block dependants only."""
    pending = set(records)
    results = {}
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending:
            ready = sorted(m for m in pending if not any(i in pending for i in records[m]['imports']))
            if not ready:
                raise build.BuildError('cyclic local import graph')
            tasks = []
            for name in ready:
                pending.remove(name)
                dependencies = {i: results[i] for i in records[name]['imports'] if i in records}
                if any(r['status'] != 'PASS' for r in dependencies.values()):
                    results[name] = {'status': 'BLOCKED_BY_DEPENDENCY'}
                    continue
                identity = build.fingerprint({'context': context, 'source': records[name]['sha256'],
                    'module': name, 'imports': {i: {'identity': r['identity'], 'objects': r['object_files']} for i, r in dependencies.items()}})
                artifact = output.joinpath(*name.split('.')).with_suffix('.olean')
                tasks.append((name, identity, artifact))
            def perform(task):
                name, identity, artifact = task
                reused = receipt_matches(old.get(name), identity, artifact)
                try:
                    if not reused:
                        artifact.parent.mkdir(parents=True, exist_ok=True)
                        for stale in artifact.parent.glob(artifact.name + '*'):
                            if stale.is_file(): stale.unlink()
                        worker(name, records[name], artifact)
                    if not artifact.is_file() or artifact.stat().st_size == 0:
                        raise build.BuildError('missing compiler output: ' + name)
                    return name, {'status': 'PASS', 'identity': identity,
                        'olean_sha256': object_digest(artifact), 'object_files': object_files(artifact), 'reused': reused}
                except Exception as exc:
                    return name, {'status': 'FAIL', 'error': str(exc)}
            for name, record in pool.map(perform, tasks):
                results[name] = record
                print('MATERIAL_MODULE ' + name + ' ' + record['status'] +
                      (' REUSED' if record.get('reused') else ''), flush=True)
    return results


def dependency_outputs(root):
    """Bind receipts to all installed external oleans, not just cache labels."""
    base = root / '.lake/packages'
    outputs = sorted((p for p in base.glob('*/.lake/build/lib/lean/**/*.olean*') if p.is_file()))
    if not outputs:
        raise build.BuildError('official dependency objects missing; source rebuild forbidden')
    digest = hashlib.sha256()
    for path in outputs:
        digest.update(path.relative_to(base).as_posix().encode() + b'\0')
        digest.update(bytes.fromhex(object_digest(path)))
    return {'count': len(outputs), 'sha256': digest.hexdigest()}


def run(root, jobs=2, benchmark=False):
    if os.environ.get('CI', '').lower() != 'true':
        raise build.BuildError('native driver is reserved for authorized external CI')
    env = dict(os.environ)
    threads = int(env.get('LEAN_NUM_THREADS', '2'))
    if not 1 <= jobs <= 4 or not 1 <= threads <= 4:
        raise build.BuildError('module workers and Lean threads must each be 1..4')
    plan = build.validate(root)
    report_path = root / 'registry/current.json'
    previous = build.read_json(report_path) if report_path.is_file() else {}
    started = time.monotonic()
    commit = env['GITHUB_SHA']
    if not re.fullmatch('[0-9a-f]{40}', commit):
        raise build.BuildError('exact checked-out source commit required')
    report = {'schema_version': 2, 'status': 'FAIL', 'commit': commit,
        'toolchain': plan['toolchain'], 'mathlib_commit': plan['mathlib_commit'],
        'platform': {'system': platform.system(), 'machine': platform.machine()},
        'all_endpoints_selected': True, 'compiler_executed': False,
        'module_workers': jobs, 'lean_num_threads': threads, 'endpoints': [],
        'execution_backend': env.get('MATERIAL_EXECUTION_BACKEND', 'native_host'),
        'new_finite_cap_theorem_included': False, 'fresh_required_audits': True,
        'build_configuration': plan['config'], 'source_pin_integrity': all(not e['source_drift'] for e in plan['endpoints'])}
    logs = root / 'registry/logs'
    logs.mkdir(parents=True, exist_ok=True)
    run_plan = {'schema_version': 1, 'intent': 'warm_benchmark' if benchmark else 'verify',
        'profile': 'T2', 'repository': env['GITHUB_REPOSITORY'], 'requested_revision': commit,
        'tested_revision': commit, 'lean_toolchain': plan['toolchain'],
        'mathlib_revision': plan['mathlib_commit'], 'runner_label': 'ubuntu-24.04',
        'targets': [e['id'] for e in plan['endpoints']],
        'source_manifest_sha256': build.sha256((root / '_vendor/source-manifest.json').read_bytes()),
        'audit_policy_sha256': build.fingerprint({e['id']: e['spec'] for e in plan['endpoints']}),
        'prior_evidence_url': previous.get('run_url'), 'reason_for_new_run': 'verify current source and required fresh audits',
        'cache_requirement': 'exact' if benchmark else 'compatible', 'module_workers': jobs,
        'lean_threads': threads, 'fresh_required_audits': True, 'mathlib_source_build_allowed': False,
        'local_lean_allowed': False, 'execution_backend': report['execution_backend'], 'receipt_adapter': 'native_build.py; full external-object digest and own imported-object hashes'}
    build.atomic_json(root / 'registry/run-plan.json', run_plan)
    try:
        cutout = root.parent / 'LEAN_CUTOUTS/Cutouts.lean'
        if not cutout.is_file():
            raise build.BuildError('required single-file native QFB cutout is missing')
        lock = (root / 'lake-manifest.json').read_bytes()
        verified = build.verify_dependencies(root, plan['dependency_lock'], env, logs, False)
        roots = sorted({m for e in plan['endpoints'] for m in e['external_imports'] if m == 'Mathlib' or m.startswith('Mathlib.')})
        ready, reason = build.retained_dependency_cache_ready(root, plan, previous, roots, verified, env)
        cache_started = time.monotonic()
        if not ready:
            if benchmark:
                raise build.BuildError('CACHE_MISS: compatible installed dependency outputs required')
            build.execute(['lake', 'exe', 'cache', 'get', *roots], root, logs / 'cache-get.log', env)
        if lock != (root / 'lake-manifest.json').read_bytes():
            raise build.BuildError('locked dependency manifest changed')
        report['verified_dependencies'] = build.verify_dependencies(root, plan['dependency_lock'], env, logs, True)
        report['cache_hydration'] = {'mode': 'retained_passed_outputs' if ready else 'official_cache_get', 'reason': reason}
        report['dependency_cache_class'] = env.get('MATERIAL_DEPENDENCY_CACHE_CLASS', 'MISS')
        report['project_cache_class'] = env.get('MATERIAL_PROJECT_CACHE_CLASS', 'MISS')
        version, _ = build.execute(['lake', 'env', 'lean', '--version'], root, logs / 'lean-version.log', env)
        if not re.search(r'\bversion\s+' + re.escape(plan['toolchain'].rsplit(':v', 1)[-1]) + r'(?:,|\s|\))', version):
            raise build.BuildError('compiler differs from pinned version')
        report['compiler'] = version.strip()
        report['compiler_executed'] = True
        report['external_objects'] = dependency_outputs(root)
        cache_seconds = time.monotonic() - cache_started
        context = {'compiler': version.strip(), 'lock': build.sha256(lock), 'configuration': plan['config'],
            'driver': build.sha256(Path(__file__).read_bytes()),
            'launcher_policy': build.sha256((root / 'ci/verify-external.sh').read_bytes()),
            'external_objects': report['external_objects'],
            'platform': report['platform']}
        records = local_records(plan)
        output = root / '.lake/build/lib/lean'
        old = previous.get('module_receipts', {}) if previous.get('status') == 'PASS' else {}
        def compile_module(name, record, artifact):
            build.execute(['lake', 'env', 'lean', '--root=' + str(root / '_vendor' if record['path'].startswith('_vendor/') else root), '-o', str(artifact), record['path']],
                          root, logs / 'modules' / (name + '.log'), env)
        build_started = time.monotonic()
        receipts = schedule(records, context, old, output, compile_module, jobs)
        report['module_receipts'] = receipts
        if any(r['status'] != 'PASS' for r in receipts.values()):
            raise build.BuildError('own module compilation failed; see module receipts')
        build_seconds = time.monotonic() - build_started
        audit_started = time.monotonic()
        def audit(entry):
            identity = build.fingerprint({'input': entry['input_plan_hash'], 'compiler': version.strip(), 'context': context})
            rel = f"registry/audits/{entry['id']}-{identity}.log"
            text, seconds = build.execute(['lake', 'env', 'lean', entry['id'] + '/Audit.lean'], root, root / rel, env)
            parsed = build.parse_audit(text, [d['name'] for d in entry['spec']['declarations']], set(entry['spec']['allowed_axioms']))
            return {'id': entry['id'], 'input_hash': identity, 'status': 'PASS', **parsed,
                'audit_reused': False, 'audit_log': rel, 'audit_sha256': build.sha256((root / rel).read_bytes()),
                'audit_origin_commit': commit, 'audit_seconds': seconds,
                'declaration_count': len(entry['spec']['declarations']), 'source_drift': entry['source_drift']}
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for record in pool.map(audit, plan['endpoints']):
                report['endpoints'].append(record)
        name = 'QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED'
        text, seconds = build.execute(['lake', 'env', 'lean', '--root=' + str(root.parent), str(cutout)], root, logs / 'cutouts-audit.log', env)
        report['cutout'] = {'status': 'PASS', 'source_sha256': object_digest(cutout),
                           **build.parse_audit(text, [name]), 'seconds': seconds, 'audit_reused': False,
                           'audit_origin_commit': commit, 'audit_log': 'registry/logs/cutouts-audit.log',
                           'audit_sha256': object_digest(logs / 'cutouts-audit.log')}
        audit_seconds = time.monotonic() - audit_started
        # A rerun checks all receipts again without duplicate Lean/audit executions.
        rerun_started = time.monotonic()
        def reject_recompile(*args):
            raise build.BuildError('unchanged no-op receipt recheck unexpectedly requested compilation')
        recheck = schedule(records, context, receipts, output, reject_recompile, jobs)
        if not all(r['status'] == 'PASS' and r['reused'] for r in recheck.values()):
            raise build.BuildError('no-op object receipt recheck failed')
        report['metrics'] = {'cache_seconds': round(cache_seconds, 3), 'build_seconds': round(build_seconds, 3),
            'audit_seconds': round(audit_seconds, 3), 'rerun_receipt_seconds': round(time.monotonic() - rerun_started, 3),
            'module_count': len(records), 'fresh_module_count': sum(not r['reused'] for r in receipts.values()),
            'reused_module_count': sum(r['reused'] for r in receipts.values()),
            'target_loc': sum(len((root / r['path']).read_text().splitlines()) for r in records.values()),
            'fresh_loc': sum(len((root / records[m]['path']).read_text().splitlines()) for m, r in receipts.items() if not r['reused']),
            'reused_loc': sum(len((root / records[m]['path']).read_text().splitlines()) for m, r in receipts.items() if r['reused']),
            'audit_fresh_count': len(report['endpoints']), 'audit_reused_count': 0}
        report['run_url'] = f"https://github.com/{env['GITHUB_REPOSITORY']}/actions/runs/{env['GITHUB_RUN_ID']}"
        report['status'] = 'PASS'
    except Exception as exc:
        report['error'] = str(exc)
        print('MATERIAL_NATIVE_FAILURE ' + str(exc), flush=True)
    report['total_seconds'] = round(time.monotonic() - started, 3)
    build.atomic_json(report_path, report)
    print(json.dumps({k: v for k, v in report.items() if k in {'status', 'error', 'metrics', 'total_seconds'}}, indent=2), flush=True)
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=build.ROOT)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--benchmark', action='store_true')
    args = parser.parse_args()
    raise SystemExit(run(args.root.resolve(), args.jobs, args.benchmark))
