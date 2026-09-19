import tempfile
import unittest
from pathlib import Path
from conjectures import skills, core


class SkillTests(unittest.TestCase):
    def test_install_repeat_and_preserve_edits(self):
        with tempfile.TemporaryDirectory() as d:
            parent=Path(d)/'unusual path'/'skills'
            first=skills.install('conjectures',parent)
            self.assertEqual(first,skills.install('conjectures',parent))
            target=parent/'conjectures'/'SKILL.md'
            self.assertIn('name: conjectures',target.read_text())
            target.write_text('operator edit')
            with self.assertRaises(core.Failure):skills.install('conjectures',parent)
            self.assertEqual(target.read_text(),'operator edit')

    def test_review_install_excludes_keys_and_symlink_target(self):
        with tempfile.TemporaryDirectory() as d:
            parent=Path(d)
            skills.install('formal-conjectures-review',parent)
            self.assertFalse((parent/'formal-conjectures-review/evals').exists())
            (parent/'conjectures').symlink_to(skills.path())
            with self.assertRaises(core.Failure):skills.install('conjectures',parent)
