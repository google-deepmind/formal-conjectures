"""Regression checks for literate caches restored across module deletions and renames."""

from pathlib import Path
import tempfile
import unittest

from prune_literate_cache import LIBRARIES, prune


class PruneLiterateCacheTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.source = Path(self.temp.name) / "source"
        self.cache = Path(self.temp.name) / "literate"
        for library in LIBRARIES:
            (self.source / library).mkdir(parents=True)

    def cached(self, module, live=False):
        page = self.cache / f"{module}.json"
        page.parent.mkdir(parents=True, exist_ok=True)
        page.write_text('{"cached": true}')
        for suffix in (".hash", ".trace"):
            page.with_name(page.name + suffix).write_text("cached metadata")
        if live:
            source = self.source / f"{module}.lean"
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("module\n")
        return page

    def test_moved_hypergraph_declaration_drops_old_page_only(self):
        prefix = "FormalConjecturesForMathlib/Combinatorics/Hypergraph/"
        old = self.cached(prefix + "ThreeUniform")
        live = [self.cached(prefix + name, live=True) for name in ("Finite", "Uniform")]
        self.assertEqual(prune(self.source, self.cache), [old.relative_to(self.cache)])
        for path in [old, old.with_name(old.name + ".hash"), old.with_name(old.name + ".trace")]:
            self.assertFalse(path.exists())
        for page in live:
            self.assertEqual(page.read_text(), '{"cached": true}')
            for suffix in (".hash", ".trace"):
                self.assertEqual(page.with_name(page.name + suffix).read_text(), "cached metadata")
        self.assertEqual(prune(self.source, self.cache), [])

    def test_deleted_problem_and_library_root(self):
        deleted = [self.cached("FormalConjectures/ErdosProblems/1076"),
                   self.cached("FormalConjecturesUtil/Removed")]
        root = self.cached("FormalConjecturesForMathlib", live=True)
        self.assertEqual(set(prune(self.source, self.cache)),
                         {page.relative_to(self.cache) for page in deleted})
        self.assertTrue(root.exists())

    def test_preserves_dependencies_and_non_module_data(self):
        unrelated = [self.cached("Mathlib/Removed"), self.cached("metadata")]
        self.assertEqual(prune(self.source, self.cache), [])
        self.assertTrue(all(page.exists() for page in unrelated))

    def test_missing_cache_is_harmless(self):
        self.assertEqual(prune(self.source, self.cache), [])

    def test_wrong_source_root_does_not_delete_data(self):
        page = self.cached("FormalConjectures/ErdosProblems/1076")
        with self.assertRaises(ValueError):
            prune(self.source / "missing", self.cache)
        self.assertTrue(page.exists())


if __name__ == "__main__":
    unittest.main()
