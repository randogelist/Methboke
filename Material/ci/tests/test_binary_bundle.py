"""External CI archive fixtures; no compiler, Lake, Docker or network is used."""
import hashlib
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import binary_bundle as b


class BinaryBundleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / 'repo'
        self.root.mkdir()
        self.output = Path(self.tmp.name) / 'binary'
        self.state_path = Path(self.tmp.name) / 'state.json'
        self.env = {'CI': 'true', 'GITHUB_ACTIONS': 'true', 'GITHUB_REPOSITORY': 'example/project',
                    'GITHUB_SHA': '1' * 40, 'GITHUB_REF_NAME': 'main', 'GITHUB_RUN_ID': '234',
                    'GITHUB_RUN_ATTEMPT': '2'}
        self.state = {'repository': 'example/project', 'commit': '1' * 40, 'branch': 'main',
                      'run_id': '234', 'attempt': '2', 'compatibility_key': '2' * 64,
                      'status': 'BUILT', 'execution_backend': 'native',
                      'native_exit_code': 0, 'compiler_location': 'native_host'}
        b.r.save(self.state_path, self.state)
        obj = self.write('Material/.lake/build/lib/lean/A.olean', b'accepted own object')
        companion = self.write('Material/.lake/build/lib/lean/A.olean.private', b'private companion')
        self.write('Material/.lake/build/lib/lean/Old.olean', b'stale object excluded')
        self.write('Material/.lake/packages/mathlib/Mathlib.olean', b'dependency excluded')
        self.write('Material/registry/audits/A.log', b'fresh endpoint evidence')
        self.write('Material/registry/logs/cutouts-audit.log', b'fresh cutout evidence')
        self.write('Material/registry/stale-evidence.json', b'stale evidence excluded')
        self.report = {'status': 'PASS', 'commit': self.state['commit'], 'execution_backend': 'native_host',
                       'run_url': 'https://github.com/example/project/actions/runs/234',
                       'compiler': 'pinned fixture', 'build_configuration': {},
                       'module_receipts': {'A': {'status': 'PASS', 'olean_sha256': self.hash(obj),
                           'object_files': {'A.olean': self.hash(obj), 'A.olean.private': self.hash(companion)}}},
                       'endpoints': [{'id': 'A', 'status': 'PASS', 'input_hash': '3' * 64,
                           'audit_log': 'registry/audits/A.log',
                           'audit_sha256': self.hash(self.root / 'Material/registry/audits/A.log')}],
                       'cutout': {'audit_log': 'registry/logs/cutouts-audit.log',
                           'audit_sha256': self.hash(self.root / 'Material/registry/logs/cutouts-audit.log')}}
        b.r.save(self.root / 'Material/registry/current.json', self.report)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def hash(self, path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    def run_fixture(self, evidence_error=None):
        with patch.object(b.r, 'metadata', return_value=self.state), \
             patch.object(b.r, 'expected_endpoint_ids', return_value={'A'}), \
             patch.object(b.native_registry, 'validate_native_evidence', side_effect=evidence_error), \
             patch.object(b.native_registry, 'dependency_identity', return_value={'compiler': 'pinned fixture'}), \
             patch.object(b.build, 'validate', return_value={}), \
             patch.object(b.native_build, 'local_records', return_value={'A'}):
            return b.run(self.root, self.state_path, self.output, self.env)

    def test_archive_bytes_match_manifest_and_exclude_unaccepted_files(self):
        entry = self.run_fixture()
        manifest = json.loads((self.output / 'manifest.json').read_text())
        archive = self.output / entry['archive_name']
        self.assertEqual(entry['status'], 'READY_FOR_UPLOAD')
        self.assertFalse(entry['remote_upload_verified'])
        self.assertEqual(entry['manifest_sha256'], self.hash(self.output / 'manifest.json'))
        self.assertEqual(entry['archive_sha256'], self.hash(archive))
        with tarfile.open(archive, 'r:gz') as packed:
            self.assertEqual(set(packed.getnames()), set(manifest['members']))
            self.assertEqual(len(packed.getnames()), 5)
            for member in packed:
                self.assertTrue(member.isfile())
                data = packed.extractfile(member).read()
                self.assertEqual(b.sha256(data), manifest['members'][member.name]['sha256'])
                self.assertEqual(len(data), manifest['members'][member.name]['bytes'])
        self.assertEqual(entry['module_count'], 1)
        self.assertFalse(entry['dependency_archive_included'])

    def test_tampered_object_is_rejected_before_packaging(self):
        self.write('Material/.lake/build/lib/lean/A.olean', b'tampered')
        with self.assertRaisesRegex(ValueError, 'differ from accepted receipts'):
            self.run_fixture()
        self.assertFalse(self.output.exists())
        self.assertEqual(b.r.load(self.root / 'Material/registry/binary-entry.json')['status'], 'REJECTED')

    def test_missing_companion_is_rejected(self):
        (self.root / 'Material/.lake/build/lib/lean/A.olean.private').unlink()
        with self.assertRaisesRegex(ValueError, 'differ from accepted receipts'):
            self.run_fixture()

    def test_fresh_evidence_validation_cannot_be_bypassed(self):
        with self.assertRaisesRegex(ValueError, 'stale evidence'):
            self.run_fixture(ValueError('stale evidence'))
        self.assertFalse(self.output.exists())

    def test_current_source_commit_is_required(self):
        self.report['commit'] = '9' * 40
        b.r.save(self.root / 'Material/registry/current.json', self.report)
        with self.assertRaisesRegex(ValueError, 'exact source commit'):
            self.run_fixture()

    def test_run_attempt_must_match_current_environment(self):
        wrong = {**self.state, 'attempt': '1'}
        b.r.save(self.state_path, wrong)
        with self.assertRaisesRegex(ValueError, 'current run: attempt'):
            self.run_fixture()

    def test_local_execution_is_rejected(self):
        self.env['GITHUB_ACTIONS'] = 'false'
        with self.assertRaisesRegex(ValueError, 'authorized GitHub CI'):
            self.run_fixture()

    def test_output_inside_repository_is_rejected(self):
        self.output = self.root / 'artifact'
        with self.assertRaisesRegex(ValueError, 'outside the repository'):
            self.run_fixture()

    def test_existing_output_is_preserved(self):
        self.output.mkdir()
        original = self.output / 'previous.tar.gz'
        original.write_bytes(b'preserve')
        with self.assertRaisesRegex(ValueError, 'must be empty'):
            self.run_fixture()
        self.assertEqual(original.read_bytes(), b'preserve')

    def test_symlinked_output_parent_is_rejected(self):
        link = Path(self.tmp.name) / 'alias'
        link.symlink_to(self.output.parent, target_is_directory=True)
        self.output = link / 'binary'
        with self.assertRaisesRegex(ValueError, 'symlinks'):
            self.run_fixture()

    def test_symlinked_object_is_rejected(self):
        path = self.root / 'Material/.lake/build/lib/lean/A.olean'
        path.unlink()
        path.symlink_to(self.root / 'Material/.lake/packages/mathlib/Mathlib.olean')
        with self.assertRaises(ValueError):
            self.run_fixture()

    def test_archive_failure_removes_partial_output(self):
        def broken_pack(root, members, destination):
            destination.write_bytes(b'partial archive')
            raise OSError('simulated write failure')
        with patch.object(b, 'pack', side_effect=broken_pack):
            with self.assertRaisesRegex(OSError, 'simulated write failure'):
                self.run_fixture()
        self.assertEqual(list(self.output.iterdir()), [])
        self.assertEqual(b.r.load(self.root / 'Material/registry/binary-entry.json')['status'], 'REJECTED')

    def test_member_mutation_during_packaging_is_rejected(self):
        expected = {'Material/.lake/build/lib/lean/A.olean': '0' * 64}
        with self.assertRaisesRegex(ValueError, 'changed during packaging'):
            b.pack(self.root, expected, Path(self.tmp.name) / 'mutation.tar.gz')

    def test_traversal_member_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'repository-relative'):
            b.safe_file(self.root, '../outside')


if __name__ == '__main__':
    unittest.main()
