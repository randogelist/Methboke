"""Routing controls for external CI; no compiler, process or network calls."""
import copy
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import failure_routing as f


class RoutingTests(unittest.TestCase):
    def setUp(self):
        self.env = {'GITHUB_SHA': '1' * 40, 'GITHUB_RUN_ID': '17',
                    'GITHUB_RUN_ATTEMPT': '2', 'GITHUB_REPOSITORY': 'owner/repo',
                    'WORKER_MODE': 'fast', 'WORKER_BACKEND': 'binary_cache',
                    'STRICT_BENCHMARK': 'false'}
        self.outcomes = {key: 'success' for key in f.STEP_ORDER}
        self.receipt = {'schema_version': 1, **f.identity(self.env),
                        'phase': 'cache_admission', 'failure_class': 'CACHE_MISSING',
                        'compiler_started': False}
        self.report = {**f.identity(self.env), 'status': 'FAIL',
                       'failure_phase': 'dependencies',
                       'failure_class': 'DEPENDENCY_CACHE_REJECTED',
                       'compiler_executed': False}

    def outcome_at(self, phase):
        outcomes = {key: 'skipped' for key in f.STEP_ORDER}
        for key in f.STEP_ORDER:
            outcomes[key] = 'success'
            if key == phase:
                outcomes[key] = 'failure'
                break
        outcomes['final_evidence'] = 'success'
        return outcomes

    def result(self, phase, **kwargs):
        return f.classify(self.outcome_at(phase), kwargs.get('env', self.env),
                          kwargs.get('receipt', self.receipt),
                          kwargs.get('report', self.report))

    def test_success_never_selects_recovery(self):
        result = f.classify(self.outcomes, self.env)
        self.assertEqual(result['failure_class'], 'NONE')
        self.assertFalse(result['recovery_allowed'])

    def test_typed_cache_admission_failures_allow_recovery(self):
        for failure_class in f.CACHE_CLASSES:
            with self.subTest(failure_class=failure_class):
                receipt = {**self.receipt, 'failure_class': failure_class}
                self.assertTrue(self.result('cache_admission', receipt=receipt)['recovery_allowed'])

    def test_only_typed_precompiler_dependency_rejection_allows_recovery(self):
        self.assertTrue(self.result('verify')['recovery_allowed'])
        for amendment in ({'compiler_executed': True}, {'failure_phase': 'compile'},
                          {'module_receipts': {'A': {'status': 'FAIL'}}},
                          {'failure_class': 'UNKNOWN'}, {'status': 'PASS'}):
            with self.subTest(amendment=amendment):
                self.assertFalse(self.result('verify', report={**self.report, **amendment})['recovery_allowed'])

    def test_stale_source_run_attempt_and_repository_fail_closed(self):
        for field in f.IDENTITY_ENV:
            with self.subTest(field=field):
                receipt, report = copy.deepcopy(self.receipt), copy.deepcopy(self.report)
                receipt[field], report[field] = 'stale', 'stale'
                self.assertFalse(self.result('cache_admission', receipt=receipt)['recovery_allowed'])
                self.assertFalse(self.result('verify', report=report)['recovery_allowed'])

    def test_missing_or_wrong_receipts_fail_closed(self):
        for receipt in ({}, {'error': 'CACHE_MISS: retry'},
                        {**self.receipt, 'compiler_started': True},
                        {**self.receipt, 'phase': 'publication'}):
            self.assertFalse(self.result('cache_admission', receipt=receipt)['recovery_allowed'])

    def test_all_other_failed_phases_never_allow_recovery(self):
        for phase in f.STEP_ORDER:
            if phase in {'cache_admission', 'verify'}:
                continue
            with self.subTest(phase=phase):
                outcomes = self.outcome_at(phase)
                outcomes[phase] = 'failure'
                self.assertFalse(f.classify(outcomes, self.env, self.receipt, self.report)['recovery_allowed'])

    def test_proof_audit_and_recheck_failures_never_recover(self):
        for phase in ('compile', 'audit', 'recheck', 'static', 'compiler'):
            report = {**self.report, 'failure_phase': phase, 'error': 'CACHE_MISS in theorem text'}
            self.assertFalse(self.result('verify', report=report)['recovery_allowed'])

    def test_benchmark_registry_and_recovery_workers_cannot_recover(self):
        for amendment in ({'STRICT_BENCHMARK': 'true'}, {'WORKER_BACKEND': 'registry'},
                          {'WORKER_MODE': 'recovery'}, {'STRICT_BENCHMARK': ''}):
            self.assertFalse(self.result('cache_admission', env={**self.env, **amendment})['recovery_allowed'])

    def test_missing_prerequisite_or_extra_failure_blocks_recovery(self):
        for step in f.REQUIRED_CACHE_PREDECESSORS:
            outcomes = self.outcome_at('cache_admission')
            outcomes[step] = 'skipped'
            self.assertFalse(f.classify(outcomes, self.env, self.receipt)['recovery_allowed'])
        outcomes = self.outcome_at('cache_admission')
        outcomes['final_evidence'] = 'failure'
        self.assertFalse(f.classify(outcomes, self.env, self.receipt)['recovery_allowed'])

    def test_cancelled_unknown_and_incomplete_outcomes_fail_closed(self):
        for amendment in ({'verify': 'cancelled'}, {'static': ''}, {'unknown': 'failure'}):
            outcomes = {**self.outcome_at('cache_admission'), **amendment}
            self.assertFalse(f.classify(outcomes, self.env, self.receipt)['recovery_allowed'])
        outcomes = self.outcome_at('cache_admission')
        del outcomes['routing']
        self.assertFalse(f.classify(outcomes, self.env, self.receipt)['recovery_allowed'])

    def test_missing_cache_receipt_binds_current_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(ValueError, 'CACHE_MISSING'):
                f.admit_binary_cache(root, self.env)
            saved = json.loads((root / 'Material/registry/cache-admission.json').read_text())
            self.assertTrue(f.same_identity(saved, f.identity(self.env)))
            self.assertIs(saved['compiler_started'], False)

    def test_corrupt_and_unaccepted_reports_are_typed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            report = root / 'Material/registry/current.json'
            report.parent.mkdir(parents=True)
            env = {**self.env, 'DEPENDENCY_HIT': 'true', 'PROJECT_MATCHED': 'passed-key'}
            for content, expected in (('invalid json', 'CACHE_CORRUPT'),
                                      ('{"status":"FAIL"}', 'CACHE_REJECTED'),
                                      ('[]', 'CACHE_REJECTED')):
                report.write_text(content)
                with self.assertRaisesRegex(ValueError, expected):
                    f.admit_binary_cache(root, env)

    def test_action_supplies_every_classified_outcome(self):
        root = Path(__file__).resolve().parents[3]
        source = (root / '.github/actions/material-worker/action.yml').read_text()
        supplied = re.findall(r'"([a-z_]+)": "\$\{\{ steps\.([\w-]+)\.outcome \}\}"', source)
        self.assertEqual({key for key, _ in supplied}, set(f.STEP_ORDER))
        ids = re.findall(r'^      id: ([\w-]+)$', source, re.MULTILINE)
        self.assertEqual(len(ids), len(set(ids)))
        for _, step in supplied:
            self.assertIn(step, ids)

    def test_recovery_job_requires_explicit_classification_or_manual_request(self):
        root = Path(__file__).resolve().parents[3]
        source = (root / '.github/workflows/material.yml').read_text()
        recovery = source.split('  rebuild-and-reseed:', 1)[1].split('  material-result:', 1)[0]
        condition = next(line for line in recovery.splitlines() if line.strip().startswith('if:'))
        self.assertIn("inputs.force_rebuild || needs.compile-audit-register.outputs.recovery-allowed == 'true'", condition)
        self.assertIn('!cancelled()', condition)
        self.assertIn('!inputs.exact_cache_benchmark', condition)


if __name__ == '__main__':
    unittest.main()
