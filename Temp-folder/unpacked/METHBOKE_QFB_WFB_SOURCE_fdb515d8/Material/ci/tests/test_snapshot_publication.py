"""External CI tests for disk-safe publication; never invoke Lean, Lake or Docker."""
import json
from pathlib import Path
from types import SimpleNamespace
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import native_registry as n


class SnapshotPublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name) / 'repo'
        self.root.mkdir()
        for relative, text in {
            'Material/ci/Snapshot.Dockerfile': 'FROM ubuntu:24.04\nCOPY Material /workspace/Material\n',
            'Material/Example/Endpoint.lean': 'import Example\n',
            'Material/.lake/build/lib/lean/Example.olean': 'own passed object',
            'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean': 'dependency object',
            'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.ir': 'dependency ir',
            'Material/.lake/transfer.ltar': 'transfer archive',
            'Material/ci/__pycache__/native_registry.pyc': 'python bytecode',
            'LEAN_CUTOUTS/Cutouts.lean': 'selected proof',
            'outside-context.txt': 'not part of the snapshot',
        }.items():
            self.write(relative, text)
        self.report = {
            'status': 'PASS', 'commit': '1' * 40, 'compiler_executed': True,
            'all_endpoints_selected': True, 'toolchain': 'leanprover/lean4:v4.33.0',
            'mathlib_commit': '2' * 40, 'compiler': 'Lean 4.33.0 pinned compiler',
            'platform': {'system': 'Linux', 'machine': 'x86_64'},
            'verified_dependencies': [{'name': 'mathlib', 'commit': '2' * 40, 'tracked_source_clean': True}],
            'external_objects': {'count': 1, 'sha256': '3' * 64},
            'build_configuration': {key: '4' * 64 for key in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean')},
            'cache_hydration': {'mode': 'retained_passed_outputs'},
        }
        self.image = 'ghcr.io/example/material'
        self.parent = self.image + '@sha256:' + '5' * 64
        self.state = {
            'image_repository': self.image, 'parent_image_digest': self.parent,
            'restore_mode': 'previous_passed_container', 'parent_commit': '6' * 40,
            'parent_report_sha256': '7' * 64,
            'parent_dependency_identity': n.dependency_identity(self.report),
        }
        self.free = 64 * n.r.GIB

    def tearDown(self):
        self.temporary.cleanup()

    def write(self, relative, text):
        target = self.root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        return target

    def docker_info(self, argv, **kwargs):
        self.assertEqual(argv, ['docker', 'info', '--format', '{{json .}}'])
        return SimpleNamespace(stdout=json.dumps({'DockerRootDir': str(self.root)}))

    def usage(self, _):
        return SimpleNamespace(free=self.free)

    def context(self):
        return n.snapshot_context(self.root, self.state, self.report)

    def test_warm_context_inherits_dependencies_and_preserves_own_objects(self):
        with patch.object(n.r, 'execute', side_effect=self.docker_info), patch.object(n.shutil, 'disk_usage', side_effect=self.usage):
            with self.context() as (context, dockerfile, metrics):
                self.assertFalse((context / 'Material/.lake/packages').exists())
                own = context / 'Material/.lake/build/lib/lean/Example.olean'
                self.assertEqual(own.read_text(), 'own passed object')
                self.assertEqual(own.stat().st_ino, (self.root / own.relative_to(context)).stat().st_ino)
                self.assertFalse((context / 'outside-context.txt').exists())
                self.assertFalse((context / 'Material/.lake/transfer.ltar').exists())
                self.assertFalse((context / 'Material/ci/__pycache__').exists())
                self.assertIn('FROM ' + self.parent, dockerfile.read_text())
                self.assertEqual(metrics['mode'], 'inherited_dependencies')
                self.assertTrue((context / 'Material/registry/snapshot-plan.json').is_file())
                staged = context
            self.assertFalse(staged.exists())
        self.assertTrue((self.root / 'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').is_file())
        self.assertTrue((self.root / 'Material/.lake/transfer.ltar').is_file())

    def test_warm_cleanup_removes_old_sources_and_own_objects_only(self):
        image_root = Path(self.temporary.name) / 'image'
        for relative in ('Material/Removed.lean', 'Material/.lake/build/Removed.olean',
                         'Material/.lake/packages/mathlib/Kept.olean', 'LEAN_CUTOUTS/Old.lean'):
            path = image_root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(relative)
        line = next(line for line in n.warm_dockerfile(self.parent).splitlines() if line.startswith('RUN '))
        command = json.loads(line.removeprefix('RUN '))
        self.assertEqual(command[:2], ['python3', '-c'])
        # Execute only the generated file cleanup against this disposable fixture.
        # No process, compiler, package manager or Docker is called.
        exec(command[2].replace('/workspace', str(image_root)), {})
        self.assertFalse((image_root / 'Material/Removed.lean').exists())
        self.assertFalse((image_root / 'Material/.lake/build').exists())
        self.assertFalse((image_root / 'LEAN_CUTOUTS').exists())
        self.assertTrue((image_root / 'Material/.lake/packages/mathlib/Kept.olean').exists())

    def test_cold_context_retains_dependency_objects_and_original_recipe(self):
        self.state.update(parent_image_digest=None, restore_mode='actions_cache_or_seed')
        with patch.object(n.r, 'execute', side_effect=self.docker_info), patch.object(n.shutil, 'disk_usage', side_effect=self.usage):
            with self.context() as (context, dockerfile, metrics):
                self.assertEqual(metrics['mode'], 'cold_seed')
                self.assertTrue((context / 'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.ir').is_file())
                self.assertEqual(dockerfile.read_bytes(), (self.root / 'Material/ci/Snapshot.Dockerfile').read_bytes())

    def test_dependency_digest_change_cannot_inherit_or_fall_back_to_full_copy(self):
        self.report['external_objects']['sha256'] = '8' * 64
        with self.assertRaisesRegex(ValueError, 'cold seed'):
            n.snapshot_mode(self.state, self.report)

    def test_changed_dependency_configuration_rejects_warm_publication(self):
        self.report['build_configuration']['lake-manifest.json'] = '9' * 64
        with self.assertRaisesRegex(ValueError, 'cold seed'):
            n.snapshot_mode(self.state, self.report)

    def test_rehydrated_dependencies_cannot_inherit_unchecked_companions(self):
        self.report['cache_hydration']['mode'] = 'official_cache_get'
        with self.assertRaisesRegex(ValueError, 'retained dependency outputs'):
            n.snapshot_mode(self.state, self.report)

    def test_unauthenticated_parent_report_rejected(self):
        self.state.pop('parent_report_sha256')
        with self.assertRaisesRegex(ValueError, 'parent report identity'):
            n.snapshot_mode(self.state, self.report)

    def test_mutable_parent_tag_rejected(self):
        self.state['parent_image_digest'] = self.image + ':latest'
        with self.assertRaisesRegex(ValueError, 'immutable parent'):
            n.snapshot_mode(self.state, self.report)

    def test_failed_parent_report_cannot_supply_identity(self):
        self.report['status'] = 'FAIL'
        with self.assertRaisesRegex(ValueError, 'complete passed report'):
            n.dependency_identity(self.report)

    def test_low_disk_stops_before_staging_and_preserves_caches(self):
        self.free = n.r.GIB
        with patch.object(n.r, 'execute', side_effect=self.docker_info), patch.object(n.shutil, 'disk_usage', side_effect=self.usage):
            with self.assertRaisesRegex(ValueError, 'insufficient disk'):
                with self.context():
                    self.fail('low-disk publication must not yield a context')
        self.assertFalse(self.state['snapshot_publication']['sufficient'])
        self.assertTrue((self.root / 'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').is_file())
        self.assertEqual(list(self.root.parent.glob('.material-snapshot-*')), [])

    def test_repeated_planning_does_not_link_the_plan_onto_itself(self):
        with patch.object(n.r, 'execute', side_effect=self.docker_info), patch.object(n.shutil, 'disk_usage', side_effect=self.usage):
            for _ in range(2):
                with self.context() as (context, _, _):
                    self.assertTrue((context / 'Material/registry/snapshot-plan.json').is_file())

    def test_absolute_or_external_symlink_is_rejected(self):
        (self.root / 'Material/unsafe').symlink_to('/etc/passwd')
        with self.assertRaisesRegex(ValueError, 'symlink leaves'):
            n.snapshot_files(self.root, 'inherited_dependencies')

    def test_context_measurement_excludes_large_inherited_dependencies(self):
        dependency = self.root / 'Material/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
        dependency.write_bytes(b'x' * 100_000)
        files = n.snapshot_files(self.root, 'inherited_dependencies')
        measured = sum(path.stat().st_size for path, _ in files)
        self.assertLess(measured, 1000)
        with patch.object(n.r, 'execute', side_effect=self.docker_info), patch.object(n.shutil, 'disk_usage', side_effect=self.usage):
            budget = n.snapshot_disk_budget(self.root, measured, len(files))
        self.assertEqual(budget['required_free_bytes'], 3 * measured + 4096 * len(files) + 2 * n.r.GIB)


if __name__ == '__main__':
    unittest.main()
