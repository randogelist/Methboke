"""Pure evidence checks: never invoke Lean, Lake or Docker."""
import copy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import build
import native_registry as n


class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.commit = '1' * 40
        self.state = {'commit': self.commit}
        self.name = 'QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED'
        self.spec = {'declarations': [{'name': self.name}], 'allowed_axioms': list(build.STANDARD_AXIOMS)}
        self.plan = {'toolchain': 'pinned', 'mathlib_commit': '2' * 40, 'config': {'driver': 'hash'},
                     'endpoints': [{'id': 'QFBRoot', 'spec': self.spec}]}
        cutout = self.root / 'LEAN_CUTOUTS/Cutouts.lean'
        cutout.parent.mkdir(parents=True)
        cutout.write_text('original selected proof')
        self.endpoint = self.record('registry/audits/QFBRoot.log')
        self.endpoint.update(id='QFBRoot', declaration_count=1)
        self.cutout = self.record('registry/logs/cutouts-audit.log')
        self.cutout['source_sha256'] = build.sha256(cutout.read_bytes())
        self.report = {'compiler_executed': True, 'all_endpoints_selected': True,
                       'fresh_required_audits': True, 'toolchain': 'pinned',
                       'mathlib_commit': '2' * 40, 'build_configuration': {'driver': 'hash'},
                       'cutout': self.cutout}
    def tearDown(self):
        self.tmp.cleanup()
    def record(self, relative):
        text = (f'TYPE_BEGIN:{self.name}\n{self.name} : QuasiFeffermanB.QuasiFeffermanBStatement\n'
                f'TYPE_END:{self.name}\nAXIOMS_BEGIN:{self.name}\n'
                f"'{self.name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
                f'AXIOMS_END:{self.name}\n')
        path = self.root / 'Material' / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return {'status': 'PASS', 'audit_reused': False, 'audit_origin_commit': self.commit,
                'audit_log': relative, 'audit_sha256': build.sha256(path.read_bytes()),
                **build.parse_audit(text, [self.name])}
    def check(self):
        with patch.object(build, 'validate', return_value=self.plan):
            n.validate_native_evidence(self.root, self.state, self.report, [self.endpoint])
    def test_matching_fresh_evidence_passes(self):
        self.check()
    def test_tampered_log_is_rejected(self):
        (self.root / 'Material' / self.endpoint['audit_log']).write_text('tampered')
        with self.assertRaises(ValueError): self.check()
    def test_changed_cutout_is_rejected(self):
        (self.root / 'LEAN_CUTOUTS/Cutouts.lean').write_text('changed')
        with self.assertRaises(ValueError): self.check()
    def test_missing_cutout_is_rejected(self):
        (self.root / 'LEAN_CUTOUTS/Cutouts.lean').unlink()
        with self.assertRaises(ValueError): self.check()
    def test_stale_origin_is_rejected(self):
        self.endpoint['audit_origin_commit'] = '3' * 40
        with self.assertRaises(ValueError): self.check()
    def test_extra_axiom_or_type_record_is_rejected(self):
        self.endpoint['types']['unrequested'] = 'unrequested : True'
        with self.assertRaises(ValueError): self.check()
    def test_reused_audit_is_rejected(self):
        self.cutout['audit_reused'] = True
        with self.assertRaises(ValueError): self.check()
    def test_missing_decl_is_rejected(self):
        self.endpoint['declaration_count'] = 0
        with self.assertRaises(ValueError): self.check()
    def test_wrong_compiler_scope_is_rejected(self):
        self.report['compiler_executed'] = False
        with self.assertRaises(ValueError): self.check()


if __name__ == '__main__': unittest.main()
