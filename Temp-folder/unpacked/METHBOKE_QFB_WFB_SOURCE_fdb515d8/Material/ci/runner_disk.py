#!/usr/bin/env python3
"""Conditional SDK reclamation on disposable GitHub-hosted runners only."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


GIB = 1024 ** 3
SDK_PATHS = tuple(Path(path) for path in (
    '/usr/local/lib/android', '/usr/share/dotnet', '/opt/ghc', '/usr/local/.ghcup'))
DEFAULT_GIB = {'warm': 20, 'cold': 40}
MINIMUM_GIB = {'warm': 16, 'cold': 32}


def required_bytes(mode, environment):
    if mode not in DEFAULT_GIB:
        raise ValueError('runner disk mode must be warm or cold')
    variable = 'MATERIAL_' + mode.upper() + '_MIN_FREE_GIB'
    value = str(environment.get(variable, DEFAULT_GIB[mode]))
    if not re.fullmatch(r'[0-9]{1,3}', value):
        raise ValueError(variable + ' must be an integer number of GiB')
    amount = int(value)
    if not MINIMUM_GIB[mode] <= amount <= 100:
        raise ValueError(f'{variable} must be between {MINIMUM_GIB[mode]} and 100 GiB')
    return amount * GIB


def disk_snapshot(root):
    docker = Path('/var/lib/docker')
    if not docker.is_dir():
        docker = Path('/')
    return {name: {'path': str(path), 'free_bytes': shutil.disk_usage(path).free}
            for name, path in (('workspace', root), ('docker', docker))}


def enough_space(snapshot, required):
    return bool(snapshot) and all(value['free_bytes'] >= required for value in snapshot.values())


def eligible_sdk(path):
    # The path itself and every ancestor must resolve to this exact allowlisted
    # location. A symlink must never turn SDK reclamation into a wider deletion.
    return (path in SDK_PATHS and not path.is_symlink() and path.is_dir()
            and path.resolve() == path)


def remove_sdk(path):
    if not eligible_sdk(path):
        raise ValueError('refusing to remove a non-allowlisted or redirected SDK')
    subprocess.run(['sudo', 'rm', '-rf', '--one-file-system', '--', str(path)],
                   check=True, timeout=180)


def save_report(root, mode, report):
    target = root / 'Material/registry' / f'runner-disk-{mode}.json'
    target.parent.mkdir(parents=True, exist_ok=True)
    temporary = target.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    temporary.replace(target)
    print('MATERIAL_RUNNER_DISK ' + json.dumps(report, sort_keys=True), flush=True)


def prepare(root, mode='warm', environment=None):
    environment = os.environ if environment is None else environment
    if (environment.get('GITHUB_ACTIONS') != 'true'
            or environment.get('RUNNER_ENVIRONMENT') != 'github-hosted'):
        report = {'status': 'SKIPPED', 'mode': mode,
                  'reason': 'not_a_disposable_github_hosted_runner', 'removed_sdk_paths': []}
        print('MATERIAL_RUNNER_DISK ' + json.dumps(report, sort_keys=True), flush=True)
        return report

    required = required_bytes(mode, environment)
    started = time.monotonic()
    report = {'schema_version': 1, 'mode': mode, 'required_free_bytes': required,
              'status': 'CHECKING', 'removed_sdk_paths': [], 'skipped_sdk_paths': [],
              'policy': 'fixed_sdk_allowlist_only; stop_when_budget_met; preserve_all_caches',
              'cleanup_skipped': True}
    before = disk_snapshot(root)
    current = before
    report['before'] = before
    try:
        if not enough_space(current, required):
            for sdk in SDK_PATHS:
                if not eligible_sdk(sdk):
                    report['skipped_sdk_paths'].append({'path': str(sdk), 'reason': 'absent_or_redirected'})
                    continue
                remove_sdk(sdk)
                report['cleanup_skipped'] = False
                report['removed_sdk_paths'].append(str(sdk))
                current = disk_snapshot(root)
                if enough_space(current, required):
                    break
        if not enough_space(current, required):
            raise RuntimeError('insufficient runner disk after the permitted SDK allowlist; caches remain intact')
        report['status'] = 'SPACE_SUFFICIENT'
        return report
    except Exception as error:
        report['status'] = 'FAIL'
        report['error'] = str(error)
        raise
    finally:
        report['after'] = current
        report['observed_free_gain_bytes'] = {
            name: current[name]['free_bytes'] - values['free_bytes']
            for name, values in before.items()}
        report['seconds'] = round(time.monotonic() - started, 3)
        save_report(root, mode, report)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=['warm', 'cold'], default='warm')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    prepare(args.root.resolve(), args.mode)
