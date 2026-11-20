"""Compiler-free adversarial checks for native object reuse and scheduling."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import patch

CI = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(CI))
import native_build as n
import native_registry as nr
import registry


class ReceiptSchedulerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.records = {'A': {'sha256': 'a', 'imports': []},
                        'B': {'sha256': 'b', 'imports': ['A']},
                        'C': {'sha256': 'c', 'imports': []}}
        self.calls = []
    def tearDown(self):
        self.temp.cleanup()
    def worker(self, name, record, artifact):
        self.calls.append(name)
        artifact.write_text(name + record['sha256'])
    def run_schedule(self, old=None, context='pins', records=None):
        return n.schedule(records or self.records, context, old or {}, self.root, self.worker, 2)
    def test_warm_objects_reused_but_tampering_rebuilds_affected_closure(self):
        first = self.run_schedule()
        self.calls.clear()
        warm = self.run_schedule(first)
        self.assertEqual(self.calls, [])
        self.assertTrue(all(r['reused'] for r in warm.values()))
        (self.root / 'A.olean').write_text('tampered')
        self.calls.clear()
        repaired = self.run_schedule(warm)
        self.assertEqual(self.calls, ['A'])
        self.assertEqual(repaired['A']['olean_sha256'], first['A']['olean_sha256'])
    def test_source_change_invalidates_transitive_dependants(self):
        first = self.run_schedule()
        self.calls.clear()
        changed = {**self.records, 'A': {**self.records['A'], 'sha256': 'changed'}}
        self.run_schedule(first, records=changed)
        self.assertEqual(self.calls, ['A', 'B'])
    def test_compiler_dependency_policy_change_rebuilds_all(self):
        first = self.run_schedule()
        self.calls.clear()
        self.run_schedule(first, context='new-pins')
        self.assertEqual(set(self.calls), {'A', 'B', 'C'})
    def test_companion_object_change_rejects_reuse(self):
        first = self.run_schedule()
        (self.root / 'A.olean.private').write_text('unexpected')
        self.calls.clear()
        self.run_schedule(first)
        self.assertIn('A', self.calls)
    def test_failed_module_blocks_only_dependants(self):
        def worker(name, record, artifact):
            if name == 'A': raise RuntimeError('deliberate failure')
            self.worker(name, record, artifact)
        result = n.schedule(self.records, 'pins', {}, self.root, worker, 2)
        self.assertEqual(result['A']['status'], 'FAIL')
        self.assertEqual(result['B']['status'], 'BLOCKED_BY_DEPENDENCY')
        self.assertEqual(result['C']['status'], 'PASS')
        self.assertEqual(self.calls, ['C'])
    def test_two_independent_workers_join_before_dependant(self):
        barrier = threading.Barrier(2)
        completed = set()
        def worker(name, record, artifact):
            if name in {'A', 'C'}:
                barrier.wait(timeout=2)
            if name == 'B': self.assertIn('A', completed)
            self.worker(name, record, artifact)
            completed.add(name)
        result = n.schedule(self.records, 'pins', {}, self.root, worker, 2)
        self.assertTrue(all(r['status'] == 'PASS' for r in result.values()))
    def test_missing_object_rebuilds(self):
        first = self.run_schedule()
        (self.root / 'C.olean').unlink()
        self.calls.clear()
        self.run_schedule(first)
        self.assertEqual(self.calls, ['C'])
    def test_cycle_fails_closed(self):
        with self.assertRaises(n.build.BuildError):
            self.run_schedule(records={'A': {'sha256': 'a', 'imports': ['A']}})
    def test_native_execution_refuses_authoring_environment(self):
        with patch.dict(n.os.environ, {}, clear=True), self.assertRaises(n.build.BuildError):
            n.run(self.root)


class NativePublicationTests(unittest.TestCase):
    def test_native_exit_failure_cannot_publish(self):
        with self.assertRaisesRegex(ValueError, 'successful external native'):
            registry.validate_pass({}, {'execution_backend': 'native', 'native_exit_code': 1}, {'A'})
    def test_source_and_policy_cache_identity_changes(self):
        root = CI.parents[1]
        keys = nr.cache_keys(root)
        self.assertTrue(keys['project_key'].startswith(keys['project_prefix']))
        self.assertTrue(keys['dependency_key'].startswith('material-deps-'))


if __name__ == '__main__': unittest.main()
