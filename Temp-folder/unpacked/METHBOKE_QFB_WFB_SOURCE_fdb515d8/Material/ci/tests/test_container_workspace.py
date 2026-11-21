"""External CI fixtures for container-native transport; no real tools run here."""
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import container_workspace as c


class ContainerWorkspaceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / 'repo'
        self.root.mkdir()
        self.parent_report = {'status': 'PASS', 'commit': '1' * 40}
        self.write('Material/registry/current.json', json.dumps(self.parent_report))
        self.write('Material/registry/audit-options-plan.json', '{"current": true}')
        self.write('Material/A/Endpoint.lean', 'import A\n')
        self.write('Material/ci/container_workspace.py', '# source transport fixture\n')
        self.write('LEAN_CUTOUTS/Cutouts.lean', 'selected proof\n')
        self.write('Material/.lake/packages/mathlib/DoNotExport.olean', 'large dependency')
        self.write('Material/.lake/build/lib/lean/Old.olean', 'old own object')
        self.write('Material/ci/__pycache__/ignored.pyc', 'bytecode')
        self.state = {'status': 'PREPARED', 'workspace_mode': 'container_native',
                      'execution_backend': 'native', 'restore_mode': 'previous_passed_container',
                      'repository': 'example/repo', 'commit': '2' * 40,
                      'run_id': '123', 'attempt': '1', 'branch': 'main',
                      'image_repository': 'ghcr.io/example/repo-material',
                      'parent_image_digest': 'ghcr.io/example/repo-material@sha256:' + '3' * 64,
                      'parent_commit': self.parent_report['commit'],
                      'parent_report_sha256': c.digest(self.root / 'Material/registry/current.json'),
                      'compatibility_key': '4' * 64, 'container': 'material-123-1'}
        self.state_path = self.root.parent / 'state.json'
        c.r.save(self.state_path, self.state)
        self.env = {'CI': 'true', 'GITHUB_ACTIONS': 'true', 'GITHUB_SHA': self.state['commit'],
                    'GITHUB_REPOSITORY': 'example/repo', 'GITHUB_RUN_ID': '123',
                    'GITHUB_RUN_ATTEMPT': '1', 'GITHUB_REF_NAME': 'main', 'MATERIAL_JOBS': '2',
                    'LEAN_NUM_THREADS': '2', 'GITHUB_TOKEN': 'must-not-enter-container',
                    'GH_TOKEN': 'also-excluded', 'HOME': '/home/host-with-credentials'}
        body = b'current object A'
        sha = hashlib.sha256(body).hexdigest()
        self.report = {'status': 'PASS', 'commit': self.state['commit'],
                       'module_receipts': {'A': {'status': 'PASS', 'olean_sha256': sha,
                                               'object_files': {'A.olean': sha}}}}
        self.calls = []
        self.native_exit = 0
        self.export_failure = False

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def fake_execute(self, argv, **kwargs):
        self.calls.append(argv)
        if argv[:3] == ['docker', 'image', 'inspect']:
            info = {'Config': {'Labels': {c.r.LABEL_PREFIX + 'report-sha256': self.state['parent_report_sha256'],
                                         'org.opencontainers.image.revision': self.state['parent_commit']}}}
            return SimpleNamespace(returncode=0, stdout=json.dumps([info]))
        if argv[:2] == ['docker', 'inspect']:
            return SimpleNamespace(returncode=0, stdout=json.dumps([{'State': {
                'Status': 'exited', 'Running': False, 'ExitCode': self.native_exit, 'OOMKilled': False}}]))
        if argv[:3] == ['docker', 'start', '--attach']:
            return SimpleNamespace(returncode=self.native_exit, stdout='')
        if argv[:2] == ['docker', 'cp'] and ':/workspace/Material/registry/.' in argv[2]:
            c.r.save(self.root / 'Material/registry/current.json', self.report)
        if argv[:2] == ['docker', 'cp'] and ':/workspace/Material/.lake/build/.' in argv[2]:
            if self.export_failure:
                raise RuntimeError('simulated own output export failure')
            self.write('Material/.lake/build/lib/lean/A.olean', 'current object A')
        return SimpleNamespace(returncode=0, stdout='')

    def run_fixture(self):
        with patch.object(c.r, 'compatibility', return_value=self.state['compatibility_key']), \
             patch.object(c.r, 'compatible_image', return_value=True), \
             patch.object(c.r, 'execute', side_effect=self.fake_execute), \
             patch.object(c, 'resolve_toolchain', return_value=Path('/compiler')), \
             patch.object(c, 'verify_current_report', return_value=(self.report, {'A'})):
            result = c.run(self.root, self.state_path, self.env)
        return result, c.r.load(self.root / 'Material/registry/container-workspace.json')

    def test_source_input_never_transfers_lake_or_bytecode(self):
        with c.source_context(self.root, self.state) as (payload, metrics):
            self.assertFalse((payload / 'Material/.lake').exists())
            self.assertFalse((payload / 'Material/ci/__pycache__').exists())
            self.assertTrue((payload / 'LEAN_CUTOUTS/Cutouts.lean').exists())
            self.assertTrue((payload / 'Material/registry/audit-options-plan.json').exists())
            self.assertLess(metrics['source_payload_bytes'], 1000)

    def test_overlay_replaces_sources_and_preserves_inherited_outputs(self):
        image = self.root.parent / 'image'
        for name, data in {'Material/registry/current.json': json.dumps(self.parent_report),
                           'Material/Stale.lean': 'removed source',
                           'Material/.lake/packages/mathlib/Keep.olean': 'dependency',
                           'Material/.lake/build/lib/lean/Keep.olean': 'own object',
                           'LEAN_CUTOUTS/Stale.lean': 'old cutout'}.items():
            target = image / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(data)
        with c.source_context(self.root, self.state) as (payload, _):
            c.apply_input(payload, image, self.state['parent_report_sha256'])
        self.assertFalse((image / 'Material/Stale.lean').exists())
        self.assertFalse((image / 'LEAN_CUTOUTS/Stale.lean').exists())
        self.assertTrue((image / 'Material/A/Endpoint.lean').exists())
        self.assertEqual((image / 'Material/.lake/packages/mathlib/Keep.olean').read_text(), 'dependency')
        self.assertEqual((image / 'Material/.lake/build/lib/lean/Keep.olean').read_text(), 'own object')

    def test_launch_exposes_only_readonly_compiler_and_allowlisted_environment(self):
        args = c.create_command(self.state, Path('/compiler'), self.env)
        self.assertEqual(args[args.index('--user') + 1], '0:0')
        self.assertEqual(args.count('--mount'), 1)
        self.assertEqual(args[args.index('--mount') + 1], 'type=bind,src=/compiler,dst=/opt/lean,readonly')
        text = '\n'.join(args)
        self.assertNotIn('must-not-enter-container', text)
        self.assertNotIn('also-excluded', text)
        self.assertNotIn('/home/host-with-credentials', text)
        self.assertNotIn('docker.sock', text)
        self.assertIn(self.state['parent_image_digest'], args)

    def test_success_exports_only_evidence_and_verified_own_outputs(self):
        result, metadata = self.run_fixture()
        self.assertEqual(result, 0)
        self.assertEqual(metadata['status'], 'VERIFIED')
        self.assertTrue(metadata['own_receipts_verified'])
        self.assertEqual(metadata['verified_own_module_count'], 1)
        exports = [argv[2] for argv in self.calls if argv[:2] == ['docker', 'cp'] and ':/' in argv[2]]
        self.assertEqual(exports, ['material-123-1:/workspace/Material/registry/.',
                                   'material-123-1:/workspace/Material/.lake/build/.'])
        self.assertEqual(self.calls[-1], ['docker', 'rm', '--force', 'material-123-1'])

    def test_failed_native_run_exports_evidence_but_not_own_objects(self):
        self.native_exit = 1
        result, metadata = self.run_fixture()
        self.assertEqual(result, 1)
        self.assertEqual(metadata['status'], 'BUILD_FAILED')
        self.assertFalse(metadata['own_objects_exported'])
        self.assertFalse(any(':/workspace/Material/.lake/build/.' in arg for call in self.calls for arg in call))

    def test_failed_export_is_not_a_successful_transport(self):
        self.export_failure = True
        result, metadata = self.run_fixture()
        self.assertEqual(result, 1)
        self.assertEqual(metadata['status'], 'TRANSPORT_FAILED')
        self.assertFalse(metadata['own_receipts_verified'])

    def test_wrong_current_commit_is_rejected_before_docker(self):
        self.env['GITHUB_SHA'] = '9' * 40
        result, metadata = self.run_fixture()
        self.assertEqual(result, 1)
        self.assertEqual(self.calls, [])
        self.assertIn('current external run', metadata['error'])

    def test_no_local_execution(self):
        with self.assertRaisesRegex(ValueError, 'authorized GitHub CI'):
            c.run(self.root, self.state_path, {})

    def test_tampered_parent_report_rejected(self):
        self.write('Material/registry/current.json', '{}')
        result, metadata = self.run_fixture()
        self.assertEqual(result, 1)
        self.assertIn('parent report changed', metadata['error'])
        self.assertEqual(self.calls, [])

    def test_stale_parent_pass_is_not_a_current_verification(self):
        with patch.object(c.r, 'expected_endpoint_ids', return_value={'A'}):
            with self.assertRaisesRegex(ValueError, 'exact source commit'):
                c.verify_current_report(self.root, self.state)

    def test_exported_companion_bytes_and_scope_must_match(self):
        self.write('Material/.lake/build/lib/lean/A.olean', 'current object A')
        self.assertEqual(c.verify_exported_objects(self.root, self.report, {'A'}), 1)
        self.write('Material/.lake/build/lib/lean/A.olean.private', 'unexpected companion')
        with self.assertRaisesRegex(ValueError, 'bytes differ'):
            c.verify_exported_objects(self.root, self.report, {'A'})
        with self.assertRaisesRegex(ValueError, 'scope differs'):
            c.verify_exported_objects(self.root, self.report, {'A', 'B'})

    def test_symlinked_own_output_is_rejected(self):
        outside = self.root.parent / 'outside.olean'
        outside.write_text('current object A')
        (self.root / 'Material/.lake/build/lib/lean/A.olean').symlink_to(outside)
        with self.assertRaises(ValueError):
            c.verify_exported_objects(self.root, self.report, {'A'})

    def test_symlinked_output_parent_directory_is_rejected(self):
        self.write('Material/.lake/build/lib/lean/A.olean', 'current object A')
        parent = self.root / 'Material/.lake/build/lib'
        outside = self.root.parent / 'outside-lib'
        parent.rename(outside)
        parent.symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symlinks'):
            c.verify_exported_objects(self.root, self.report, {'A'})


if __name__ == '__main__':
    unittest.main()
