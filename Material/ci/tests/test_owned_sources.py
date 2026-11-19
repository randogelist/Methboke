"""External filesystem-only controls for first-party source registration."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import build


class OwnedSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.name = 'MethbokeAddon.Front'
        self.path = self.root / 'MethbokeAddon/Front.lean'
        self.path.parent.mkdir(parents=True)
        self.path.write_text('import Mathlib.Init\ntheorem front : True := True.intro\n')
        self.row = {'module': self.name, 'path': 'MethbokeAddon/Front.lean',
                    'sha256': build.sha256(self.path.read_bytes()), 'imports': ['Mathlib.Init'],
                    'origin': {'repository': 'randogelist/Methboke', 'revision': 'a' * 40,
                               'path': 'candidate/MethbokeAddon/Front.lean'}}
        self.save()

    def tearDown(self):
        self.temp.cleanup()

    def save(self):
        (self.root / 'owned-sources.json').write_text(json.dumps({'schema_version': 1, 'modules': [self.row]}))

    def validate(self):
        return build.validate_owned_sources(self.root, build.module_index(self.root), set())

    def test_current_exact_owned_source_is_registered(self):
        self.assertEqual(self.validate(), {self.name: self.row})

    def test_manifest_cannot_mask_changed_source(self):
        self.path.write_text(self.path.read_text() + '-- changed\n')
        with self.assertRaisesRegex(build.BuildError, 'bytes/imports'):
            self.validate()

    def test_manifest_imports_are_checked(self):
        self.row['imports'] = []
        self.save()
        with self.assertRaisesRegex(build.BuildError, 'bytes/imports'):
            self.validate()

    def test_unregistered_owned_source_is_rejected(self):
        (self.root / 'owned-sources.json').unlink()
        with self.assertRaisesRegex(build.BuildError, 'unregistered owned source'):
            self.validate()

    def test_moving_branch_is_not_source_provenance(self):
        self.row['origin']['revision'] = 'main'
        self.save()
        with self.assertRaisesRegex(build.BuildError, 'exact repository snapshot'):
            self.validate()

    def test_vendor_files_need_no_owned_manifest(self):
        destination = self.root / '_vendor/MethbokeAddon/Front.lean'
        destination.parent.mkdir(parents=True)
        self.path.rename(destination)
        (self.root / 'owned-sources.json').unlink()
        self.assertEqual(self.validate(), {})


if __name__ == '__main__':
    unittest.main()
