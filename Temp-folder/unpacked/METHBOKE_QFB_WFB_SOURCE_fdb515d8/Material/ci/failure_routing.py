#!/usr/bin/env python3
"""Fail-closed worker routing from explicit phase outcomes and current receipts.

This helper never invokes a compiler, deletes caches, or starts recovery. Only
the workflow may select a fresh runner from its ``recovery_allowed`` output.
Free-form exception/log text is never interpreted as a recovery authorization.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path


IDENTITY_ENV = {
    'commit': 'GITHUB_SHA', 'run_id': 'GITHUB_RUN_ID',
    'run_attempt': 'GITHUB_RUN_ATTEMPT', 'repository': 'GITHUB_REPOSITORY',
}
CACHE_CLASSES = frozenset({'CACHE_MISSING', 'CACHE_CORRUPT', 'CACHE_REJECTED'})
STEP_ORDER = (
    'routing', 'static', 'disk', 'registry_auth', 'restore', 'cold_disk',
    'repaired_dependencies', 'dependencies', 'repaired_project', 'project',
    'cache_admission', 'recovery_admission', 'exact_gate', 'compiler_setup',
    'audit_options', 'verify', 'verified_evidence', 'save_dependencies',
    'binary_package', 'save_project', 'published_dependencies',
    'published_project', 'published_identities', 'publish_binary',
    'publish_registry', 'final_evidence',
)
PUBLICATION_STEPS = frozenset(STEP_ORDER[STEP_ORDER.index('verified_evidence'):])
REQUIRED_CACHE_PREDECESSORS = (
    'routing', 'static', 'disk', 'restore', 'dependencies', 'project',
)


def identity(environment):
    return {key: environment.get(name, '') for key, name in IDENTITY_ENV.items()}


def same_identity(record, expected):
    return all(expected.get(key) and str(record.get(key, '')) == str(expected[key])
               for key in IDENTITY_ENV)


def load_optional(path):
    try:
        value = json.loads(path.read_text())
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError):
        return {}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def cache_rejection(root, environment, failure_class, reason):
    record = {'schema_version': 1, **identity(environment),
              'phase': 'cache_admission', 'failure_class': failure_class,
              'reason': reason, 'compiler_started': False}
    save(root / 'Material/registry/cache-admission.json', record)
    raise ValueError(f'{failure_class}: {reason}')


def admit_binary_cache(root, environment):
    """Admit a prior PASS report, or leave a typed pre-compiler rejection."""
    report_path = root / 'Material/registry/current.json'
    if (environment.get('DEPENDENCY_HIT') != 'true'
            or not environment.get('PROJECT_MATCHED')):
        cache_rejection(root, environment, 'CACHE_MISSING',
                        'exact dependencies and compatible passed project objects are required')
    if not report_path.is_file():
        cache_rejection(root, environment, 'CACHE_MISSING',
                        'restored project objects lack their PASS report')
    raw = report_path.read_bytes()
    try:
        previous = json.loads(raw)
    except (ValueError, UnicodeError):
        cache_rejection(root, environment, 'CACHE_CORRUPT',
                        'restored project report is not valid JSON')
    if (not isinstance(previous, dict) or previous.get('status') != 'PASS'
            or previous.get('compiler_executed') is not True
            or previous.get('all_endpoints_selected') is not True
            or previous.get('source_pin_integrity') is not True
            or not isinstance(previous.get('module_receipts'), dict)
            or not previous['module_receipts']):
        cache_rejection(root, environment, 'CACHE_REJECTED',
                        'a complete prior verified project report is required')
    # A missing/corrupt freshly generated state is a configuration failure,
    # never a reason to relabel the restored cache or rebuild foundations.
    state_path = Path(environment['MATERIAL_STATE'])
    state = json.loads(state_path.read_text())
    plan = {
        'schema_version': 1, 'backend': 'binary_cache',
        **identity(environment), 'attempt': environment['GITHUB_RUN_ATTEMPT'],
        'dependency_key': state['dependency_key'], 'dependency_exact_hit': True,
        'dependency_matched_key': environment['DEPENDENCY_MATCHED'],
        'project_requested_key': state['project_key'],
        'project_matched_key': environment['PROJECT_MATCHED'],
        'project_exact_hit': environment.get('PROJECT_HIT') == 'true',
        'parent_commit': previous.get('commit'), 'parent_run_url': previous.get('run_url'),
        'parent_report_sha256': hashlib.sha256(raw).hexdigest(),
        'compiler_location': 'native_host', 'docker_used': False,
        'missing_dependency_policy': ('STOP_WITHOUT_RECOVERY'
                                      if environment.get('STRICT_BENCHMARK') == 'true'
                                      else 'CLASSIFIED_CACHE_RECOVERY_ONLY'),
        'worker_mode': 'fast', 'artifact_retention_days': 90,
        'scope': 'own binary objects; dependencies remain in Actions cache',
    }
    state.update(restore_mode='actions_passed_cache', workspace_mode='native_binary',
                 benchmark_backend='binary_cache', binary_cache=plan)
    save(state_path, state)
    save(root / 'Material/registry/binary-restore-plan.json', plan)
    save(root / 'Material/registry/cache-admission.json', {
        'schema_version': 1, **identity(environment), 'phase': 'cache_admission',
        'failure_class': 'NONE', 'compiler_started': False,
        'parent_report_sha256': plan['parent_report_sha256'],
    })
    print('MATERIAL_BINARY_RESTORE ' + json.dumps(plan, sort_keys=True))
    return plan


def classify(outcomes, environment, cache_receipt=None, report=None):
    """Use the first failed phase; stale evidence can never authorize recovery."""
    expected = identity(environment)
    cache_receipt, report = cache_receipt or {}, report or {}
    result = {'schema_version': 1, **expected, 'failure_class': 'NONE',
              'failed_step': None, 'recovery_allowed': False,
              'worker_mode': environment.get('WORKER_MODE'),
              'backend': environment.get('WORKER_BACKEND'),
              'step_outcomes': outcomes}
    if any(value == 'cancelled' for value in outcomes.values()):
        result['failure_class'] = 'CANCELLED'
        return result
    failed = next((step for step in STEP_ORDER if outcomes.get(step) == 'failure'), None)
    if failed is None:
        if (set(outcomes) != set(STEP_ORDER)
                or outcomes.get('verify') != 'success'
                or outcomes.get('final_evidence') != 'success'
                or any(value not in {'success', 'skipped'} for value in outcomes.values())):
            result['failure_class'] = 'UNKNOWN_FAILURE'
        return result
    result['failed_step'] = failed
    if failed in {'routing', 'static', 'recovery_admission'}:
        result['failure_class'] = 'STATIC_VALIDATION_FAILURE'
    elif failed in {'disk', 'cold_disk', 'registry_auth', 'compiler_setup'}:
        result['failure_class'] = 'RUNNER_SETUP_FAILURE'
    elif failed == 'audit_options':
        result['failure_class'] = 'AUDIT_CONFIGURATION_FAILURE'
    elif failed in PUBLICATION_STEPS:
        result['failure_class'] = 'PUBLICATION_FAILURE'
    elif failed == 'cache_admission':
        if (same_identity(cache_receipt, expected)
                and cache_receipt.get('phase') == 'cache_admission'
                and cache_receipt.get('compiler_started') is False
                and cache_receipt.get('failure_class') in CACHE_CLASSES):
            result['failure_class'] = cache_receipt['failure_class']
        else:
            result['failure_class'] = 'UNKNOWN_FAILURE'
    elif failed == 'verify':
        if (same_identity(report, expected) and report.get('status') == 'FAIL'
                and report.get('failure_class') == 'DEPENDENCY_CACHE_REJECTED'
                and report.get('failure_phase') == 'dependencies'
                and report.get('compiler_executed') is False
                and not report.get('module_receipts')):
            result['failure_class'] = 'DEPENDENCY_CACHE_REJECTED'
        elif same_identity(report, expected) and report.get('status') == 'FAIL':
            result['failure_class'] = {
                'compile': 'PROOF_OR_TYPE_FAILURE', 'audit': 'TYPE_OR_AXIOM_AUDIT_FAILURE',
                'recheck': 'CURRENT_RECEIPT_FAILURE', 'static': 'STATIC_VALIDATION_FAILURE',
                'compiler': 'COMPILER_CONFIGURATION_FAILURE',
            }.get(report.get('failure_phase'), 'VERIFICATION_FAILURE')
        else:
            result['failure_class'] = 'VERIFICATION_FAILURE'
    else:
        # Restore action/network/timeout failures and exact-benchmark misses
        # lack an authenticated cache rejection. They fail closed.
        result['failure_class'] = 'CACHE_TRANSPORT_OR_UNKNOWN_FAILURE'
    cache_failure = result['failure_class'] in CACHE_CLASSES | {'DEPENDENCY_CACHE_REJECTED'}
    prerequisites = all(outcomes.get(step) == 'success' for step in REQUIRED_CACHE_PREDECESSORS)
    if failed == 'verify':
        prerequisites = prerequisites and all(outcomes.get(step) == 'success'
            for step in ('cache_admission', 'compiler_setup', 'audit_options'))
    result['recovery_allowed'] = bool(
        cache_failure and prerequisites and environment.get('WORKER_MODE') == 'fast'
        and environment.get('WORKER_BACKEND') == 'binary_cache'
        and environment.get('STRICT_BENCHMARK') == 'false'
        and set(outcomes) == set(STEP_ORDER)
        and all(value in {'success', 'failure', 'skipped'} for value in outcomes.values())
        and all(value != 'failure' for step, value in outcomes.items() if step != failed))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('admit', 'classify'))
    parser.add_argument('--root', type=Path, default=Path.cwd())
    args = parser.parse_args()
    if args.operation == 'admit':
        admit_binary_cache(args.root, os.environ)
        return
    outcomes = json.loads(os.environ['STEP_OUTCOMES'])
    result = classify(outcomes, os.environ,
                      load_optional(args.root / 'Material/registry/cache-admission.json'),
                      load_optional(args.root / 'Material/registry/current.json'))
    save(args.root / 'Material/registry/failure-routing.json', result)
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
            stream.write('failure_class=' + result['failure_class'] + '\n')
            stream.write('recovery_allowed=' + str(result['recovery_allowed']).lower() + '\n')
    print('MATERIAL_FAILURE_ROUTING ' + json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
