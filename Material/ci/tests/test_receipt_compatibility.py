"""External control tests for the explicit legacy migration; never invoke Lean."""
import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import native_build
import receipt_compatibility as compatibility


class ContextMigrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.output = Path(self.temp.name)
        self.records = {'A': {'sha256': 'a', 'imports': []},
                        'B': {'sha256': 'b', 'imports': ['A']},
                        'C': {'sha256': 'c', 'imports': []}}
        self.context = {'compiler': 'Lean pinned compiler',
            'lock': compatibility.LEGACY_CONFIGURATION['lake-manifest.json'],
            'configuration': {**compatibility.LEGACY_CONFIGURATION, 'ci/build.py': 'new-build'},
            'driver': 'new-native-driver', 'receipt_adapter': 'adapter-hash',
            'launcher_policy': compatibility.LEGACY_LAUNCHER,
            'external_objects': {'count': 5, 'sha256': 'e' * 64},
            'platform': {'system': 'Linux', 'machine': 'x86_64'}}
        self.previous = {'status': 'PASS', 'compiler_executed': True,
            'all_endpoints_selected': True, 'fresh_required_audits': True,
            'build_configuration': copy.deepcopy(compatibility.LEGACY_CONFIGURATION),
            'compiler': self.context['compiler'], 'external_objects': self.context['external_objects'],
            'platform': self.context['platform'],
            'endpoints': [{'id': name, 'status': 'PASS', 'audit_reused': False}
                          for name in compatibility.LEGACY_ENDPOINTS],
            'cutout': {'status': 'PASS', 'audit_reused': False}}
        legacy = compatibility.legacy_context(self.previous, self.context)
        self.calls = []
        self.previous['module_receipts'] = native_build.schedule(
            self.records, legacy, {}, self.output, self.worker, 2)
        self.calls.clear()

    def tearDown(self):
        self.temp.cleanup()

    def worker(self, name, record, artifact):
        self.calls.append(name)
        artifact.write_text(name + record['sha256'])

    def migrate(self):
        return compatibility.migrate(self.previous, self.context, self.records,
                                     self.output, native_build.receipt_matches)

    def test_exact_legacy_source_and_object_chain_migrates(self):
        old, metadata = self.migrate()
        result = native_build.schedule(self.records, self.context, old, self.output, self.worker, 2)
        self.assertEqual(metadata['migrated_count'], 3)
        self.assertEqual(self.calls, [])
        self.assertTrue(all(r['reused'] for r in result.values()))
        self.assertTrue(all('context_migration' in r for r in result.values()))

    def test_changed_source_rejects_affected_dependency_closure(self):
        self.records['A']['sha256'] = 'changed'
        old, metadata = self.migrate()
        self.assertEqual(metadata['migrated_count'], 1)
        result = native_build.schedule(self.records, self.context, old, self.output, self.worker, 2)
        self.assertEqual(set(self.calls), {'A', 'B'})
        self.assertTrue(result['C']['reused'])

    def test_tampered_object_and_dependants_do_not_migrate(self):
        (self.output / 'A.olean').write_text('tampered')
        _, metadata = self.migrate()
        self.assertEqual(metadata['migrated_count'], 1)

    def test_new_namespace_is_never_inherited(self):
        self.records['Owned.New'] = {'sha256': 'new', 'imports': ['A']}
        old, metadata = self.migrate()
        native_build.schedule(self.records, self.context, old, self.output, self.worker, 2)
        self.assertEqual(self.calls, ['Owned.New'])
        self.assertEqual(metadata['migrated_count'], 3)

    def test_dependency_compiler_launcher_or_pinned_config_change_is_rejected(self):
        for key, value in [('compiler', 'another compiler'), ('external_objects', {'sha256': 'different'}),
                           ('platform', {'system': 'Windows'}), ('launcher_policy', 'new-launcher'),
                           ('lock', 'another lock')]:
            with self.subTest(key=key):
                changed = {**self.context, key: value}
                self.assertIsNone(compatibility.legacy_context(self.previous, changed))
        changed = copy.deepcopy(self.context)
        changed['configuration']['lakefile.lean'] = 'new-lake-config'
        self.assertIsNone(compatibility.legacy_context(self.previous, changed))

    def test_unknown_legacy_driver_configuration_does_not_migrate(self):
        self.previous['build_configuration']['ci/build.py'] = 'unknown-old-build'
        _, metadata = self.migrate()
        self.assertEqual(metadata['status'], 'NOT_APPLICABLE')

    def test_incomplete_or_reused_prior_audit_is_rejected(self):
        self.previous['endpoints'][0]['audit_reused'] = True
        self.assertIsNone(compatibility.legacy_context(self.previous, self.context))

    def test_original_report_is_not_rewritten(self):
        original = copy.deepcopy(self.previous)
        self.migrate()
        self.assertEqual(original, self.previous)

    def test_unrecognized_native_driver_does_not_match_any_legacy_receipt(self):
        for receipt in self.previous['module_receipts'].values():
            receipt['identity'] = 'unknown-driver-receipt'
        _, metadata = self.migrate()
        self.assertEqual(metadata['migrated_count'], 0)
        self.assertEqual(metadata['rejected_count'], 3)


if __name__ == '__main__':
    unittest.main()
