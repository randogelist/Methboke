"""Mocked SDK-reclamation fixtures for external CI; no removal or subprocess runs."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import runner_disk as d


class RunnerDiskTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.environment = {'GITHUB_ACTIONS': 'true', 'RUNNER_ENVIRONMENT': 'github-hosted'}

    def tearDown(self):
        self.temporary.cleanup()

    def space(self, gib):
        return {name: {'path': str(self.root), 'free_bytes': gib * d.GIB}
                for name in ('workspace', 'docker')}

    def test_sufficient_space_skips_all_sdk_deletions(self):
        with patch.object(d, 'disk_snapshot', return_value=self.space(50)), \
                patch.object(d, 'eligible_sdk') as eligibility, patch.object(d, 'remove_sdk') as remove:
            result = d.prepare(self.root, environment=self.environment)
        eligibility.assert_not_called()
        remove.assert_not_called()
        self.assertTrue(result['cleanup_skipped'])
        self.assertEqual(result['status'], 'SPACE_SUFFICIENT')
        saved = json.loads((self.root / 'Material/registry/runner-disk-warm.json').read_text())
        self.assertEqual(saved['before']['workspace']['free_bytes'], 50 * d.GIB)

    def test_reclamation_stops_as_soon_as_budget_is_met(self):
        with patch.object(d, 'disk_snapshot', side_effect=[self.space(12), self.space(21)]), \
                patch.object(d, 'eligible_sdk', return_value=True), patch.object(d, 'remove_sdk') as remove:
            result = d.prepare(self.root, environment=self.environment)
        remove.assert_called_once_with(d.SDK_PATHS[0])
        self.assertEqual(result['removed_sdk_paths'], [str(d.SDK_PATHS[0])])
        self.assertEqual(result['observed_free_gain_bytes']['docker'], 9 * d.GIB)

    def test_both_workspace_and_docker_need_headroom(self):
        insufficient = self.space(25)
        insufficient['docker']['free_bytes'] = 10 * d.GIB
        with patch.object(d, 'disk_snapshot', side_effect=[insufficient, self.space(22)]), \
                patch.object(d, 'eligible_sdk', return_value=True), patch.object(d, 'remove_sdk') as remove:
            d.prepare(self.root, environment=self.environment)
        remove.assert_called_once_with(d.SDK_PATHS[0])

    def test_absent_or_redirected_sdk_is_skipped(self):
        with patch.object(d, 'disk_snapshot', side_effect=[self.space(12), self.space(21)]), \
                patch.object(d, 'eligible_sdk', side_effect=[False, True]), patch.object(d, 'remove_sdk') as remove:
            result = d.prepare(self.root, environment=self.environment)
        remove.assert_called_once_with(d.SDK_PATHS[1])
        self.assertEqual(result['skipped_sdk_paths'][0]['path'], str(d.SDK_PATHS[0]))

    def test_sdk_symlink_is_never_eligible(self):
        with patch.object(Path, 'is_symlink', return_value=True), patch.object(Path, 'is_dir', return_value=True):
            self.assertFalse(d.eligible_sdk(d.SDK_PATHS[0]))

    def test_redirected_parent_is_never_eligible(self):
        with patch.object(Path, 'is_symlink', return_value=False), patch.object(Path, 'is_dir', return_value=True), \
                patch.object(Path, 'resolve', return_value=Path('/outside')):
            self.assertFalse(d.eligible_sdk(d.SDK_PATHS[0]))

    def test_arbitrary_path_is_never_deleted(self):
        with patch.object(d.subprocess, 'run') as process:
            with self.assertRaisesRegex(ValueError, 'refusing'):
                d.remove_sdk(self.root / 'Material/.lake')
        process.assert_not_called()

    def test_deletion_uses_fixed_path_and_no_other_filesystems(self):
        with patch.object(d, 'eligible_sdk', return_value=True), patch.object(d.subprocess, 'run') as process:
            d.remove_sdk(d.SDK_PATHS[0])
        process.assert_called_once_with(
            ['sudo', 'rm', '-rf', '--one-file-system', '--', str(d.SDK_PATHS[0])], check=True, timeout=180)

    def test_self_hosted_and_authoring_environments_do_nothing(self):
        for environment in ({}, {'GITHUB_ACTIONS': 'true', 'RUNNER_ENVIRONMENT': 'self-hosted'},
                            {'GITHUB_ACTIONS': 'false', 'RUNNER_ENVIRONMENT': 'github-hosted'}):
            with self.subTest(environment=environment), patch.object(d, 'disk_snapshot') as sample, \
                    patch.object(d, 'remove_sdk') as remove:
                result = d.prepare(self.root, environment=environment)
            self.assertEqual(result['status'], 'SKIPPED')
            sample.assert_not_called()
            remove.assert_not_called()

    def test_insufficient_space_fails_after_only_allowlisted_attempts(self):
        with patch.object(d, 'disk_snapshot', return_value=self.space(5)), \
                patch.object(d, 'eligible_sdk', return_value=True), patch.object(d, 'remove_sdk') as remove:
            with self.assertRaisesRegex(RuntimeError, 'caches remain intact'):
                d.prepare(self.root, environment=self.environment)
        self.assertEqual([call.args[0] for call in remove.call_args_list], list(d.SDK_PATHS))
        report = json.loads((self.root / 'Material/registry/runner-disk-warm.json').read_text())
        self.assertEqual(report['status'], 'FAIL')
        self.assertEqual(report['after']['docker']['free_bytes'], 5 * d.GIB)

    def test_threshold_values_are_bounded_and_cannot_be_shell_syntax(self):
        for value in ('0', '101', '2.5', '20; rm -rf /', '../cache'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                d.required_bytes('warm', {'MATERIAL_WARM_MIN_FREE_GIB': value})
        self.assertEqual(d.required_bytes('warm', {}), 20 * d.GIB)
        self.assertEqual(d.required_bytes('cold', {}), 40 * d.GIB)
        self.assertEqual(d.required_bytes('cold', {'MATERIAL_COLD_MIN_FREE_GIB': '36'}), 36 * d.GIB)

    def test_cold_mode_records_its_distinct_budget(self):
        with patch.object(d, 'disk_snapshot', return_value=self.space(50)), patch.object(d, 'remove_sdk') as remove:
            report = d.prepare(self.root, mode='cold', environment=self.environment)
        remove.assert_not_called()
        self.assertEqual(report['required_free_bytes'], 40 * d.GIB)
        self.assertTrue((self.root / 'Material/registry/runner-disk-cold.json').is_file())

    def test_binary_recovery_accepts_observed_headroom_without_lowering_registry_default(self):
        observed = {name: {'path': str(self.root), 'free_bytes': 36011274240}
                    for name in ('workspace', 'docker')}
        recovery = {**self.environment, 'MATERIAL_COLD_MIN_FREE_GIB': '32'}
        with patch.object(d, 'disk_snapshot', return_value=observed), \
                patch.object(d, 'eligible_sdk', return_value=False), patch.object(d, 'remove_sdk') as remove:
            report = d.prepare(self.root, mode='cold', environment=recovery)
            self.assertEqual(report['status'], 'SPACE_SUFFICIENT')
            self.assertEqual(report['required_free_bytes'], 32 * d.GIB)
            self.assertTrue(report['cleanup_skipped'])
            with self.assertRaisesRegex(RuntimeError, 'insufficient runner disk'):
                d.prepare(self.root, mode='cold', environment=self.environment)
            remove.assert_not_called()
        saved = json.loads((self.root / 'Material/registry/runner-disk-cold.json').read_text())
        self.assertEqual(saved['required_free_bytes'], 40 * d.GIB)
        self.assertEqual(saved['status'], 'FAIL')


if __name__ == '__main__':
    unittest.main()
