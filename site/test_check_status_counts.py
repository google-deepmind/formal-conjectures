#!/usr/bin/env python3
"""Tests for `check_status_counts.py`.

Run with `python3 -m unittest discover -s site -p 'test_*.py'`.
No dependencies beyond the standard library.
"""

import contextlib
import io
import json
import os
import pathlib
import tempfile
import unittest
import unittest.mock

import check_status_counts as cs

OPEN = '@[category research open]\ntheorem a{0} : True := trivial\n'
SOLVED = '@[category research solved]\ntheorem b{0} : True := trivial\n'
PROVED = ('@[category research solved, formal_proof using lean4 at "https://e.com"]\n'
          'theorem c{0} : True := trivial\n')


def problem(category, kind=None):
    return {'theorem': 'a', 'module': 'FormalConjectures.Example',
            'category': category, 'formalProofKind': kind}


class CountSourceTest(unittest.TestCase):

    def setUp(self):
        self.root = pathlib.Path(self.enterContext(tempfile.TemporaryDirectory()))

    def write(self, path, source):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source, encoding='utf-8')

    def test_counts_across_files(self):
        self.write('FormalConjectures/A.lean', OPEN.format(1))
        self.write('FormalConjectures/Sub/B.lean', SOLVED.format(1) + PROVED.format(1))
        self.assertEqual(cs.count_source(self.root),
                         {'open': 1, 'solved': 2, 'formal': 1})

    def test_skips_formathlib_and_other_libraries(self):
        self.write('FormalConjectures/ForMathlib/A.lean', OPEN.format(1))
        self.write('FormalConjecturesUtil/B.lean', OPEN.format(2))
        self.write('FormalConjecturesTest/C.lean', OPEN.format(3))
        self.assertEqual(cs.count_source(self.root),
                         {'open': 0, 'solved': 0, 'formal': 0})

    def test_skips_non_lean_files(self):
        self.write('FormalConjectures/A.md', OPEN.format(1))
        self.assertEqual(cs.count_source(self.root)['open'], 0)

    def test_empty_checkout(self):
        self.assertEqual(cs.count_source(self.root),
                         {'open': 0, 'solved': 0, 'formal': 0})


class CountExtractionTest(unittest.TestCase):

    def setUp(self):
        self.dir = pathlib.Path(self.enterContext(tempfile.TemporaryDirectory()))

    def extraction(self, problems):
        path = self.dir / 'conjectures.json'
        path.write_text(json.dumps({'problems': problems}), encoding='utf-8')
        return str(path)

    def test_counts_each_status(self):
        path = self.extraction([
            problem('research open'),
            problem('research solved'),
            problem('research solved', 'lean4'),
        ])
        self.assertEqual(cs.count_extraction(path),
                         {'open': 1, 'solved': 2, 'formal': 1})

    def test_formal_proof_outside_research_solved_counts(self):
        path = self.extraction([problem('textbook', 'lean4'),
                                problem('test', 'formal_conjectures')])
        self.assertEqual(cs.count_extraction(path),
                         {'open': 0, 'solved': 0, 'formal': 2})

    def test_null_kind_is_not_a_formal_proof(self):
        path = self.extraction([problem('research solved', None)])
        self.assertEqual(cs.count_extraction(path)['formal'], 0)

    def test_absent_kind_is_not_a_formal_proof(self):
        entry = problem('research solved')
        del entry['formalProofKind']
        self.assertEqual(cs.count_extraction(self.extraction([entry]))['formal'], 0)

    def test_missing_category(self):
        entry = problem('research open')
        del entry['category']
        with self.assertRaisesRegex(cs.DataError, 'category'):
            cs.count_extraction(self.extraction([entry]))

    def test_entry_not_an_object(self):
        with self.assertRaisesRegex(cs.DataError, 'not an object'):
            cs.count_extraction(self.extraction(['a']))

    def test_no_problems_list(self):
        path = self.dir / 'conjectures.json'
        path.write_text(json.dumps({'moduleDocstrings': {}}), encoding='utf-8')
        with self.assertRaisesRegex(cs.DataError, 'problems'):
            cs.count_extraction(str(path))

    def test_not_json(self):
        path = self.dir / 'conjectures.json'
        path.write_text('{not json', encoding='utf-8')
        with self.assertRaisesRegex(cs.DataError, 'not valid JSON'):
            cs.count_extraction(str(path))

    def test_missing_file(self):
        with self.assertRaisesRegex(cs.DataError, 'cannot read'):
            cs.count_extraction(str(self.dir / 'absent.json'))


class MainTest(unittest.TestCase):
    """End to end, including exit codes and the run summary."""

    def setUp(self):
        self.dir = pathlib.Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.root = self.dir / 'checkout'
        (self.root / 'FormalConjectures').mkdir(parents=True)
        self.summary = self.dir / 'summary.md'
        self.enterContext(unittest.mock.patch.dict(
            os.environ, {'GITHUB_STEP_SUMMARY': str(self.summary)}))

    def source(self, text):
        (self.root / 'FormalConjectures' / 'A.lean').write_text(text, encoding='utf-8')

    def extraction(self, problems):
        path = self.dir / 'conjectures.json'
        path.write_text(json.dumps({'problems': problems}), encoding='utf-8')
        return str(path)

    def run_main(self, path):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cs.main([path, '--root', str(self.root)])
        summary = (self.summary.read_text(encoding='utf-8')
                   if self.summary.exists() else '')
        return code, out.getvalue(), summary

    def test_agreement_succeeds(self):
        self.source(OPEN.format(1) + PROVED.format(1))
        code, out, summary = self.run_main(
            self.extraction([problem('research open'),
                             problem('research solved', 'lean4')]))
        self.assertEqual(code, 0)
        self.assertNotIn('::error', out)
        self.assertIn('| `research open` | 1 | 1 |', summary)

    def test_disagreement_fails(self):
        self.source(OPEN.format(1) + OPEN.format(2))
        code, out, summary = self.run_main(
            self.extraction([problem('research open')]))
        self.assertEqual(code, 1)
        self.assertIn('::error file=site/status_counts.py', out)
        self.assertIn('research open counted 2 from source but 1', out)
        self.assertIn('**Failing**', summary)

    def test_disagreement_on_formal_proofs_only(self):
        self.source(PROVED.format(1))
        code, out, _ = self.run_main(
            self.extraction([problem('research solved')]))
        self.assertEqual(code, 1)
        self.assertIn('formally proved counted 1 from source but 0', out)

    def test_both_empty_succeeds(self):
        code, _, _ = self.run_main(self.extraction([]))
        self.assertEqual(code, 0)

    def test_malformed_extraction_fails_loudly(self):
        path = self.dir / 'conjectures.json'
        path.write_text('{not json', encoding='utf-8')
        code, out, _ = self.run_main(str(path))
        self.assertEqual(code, 2)
        self.assertIn('::error::', out)


if __name__ == '__main__':
    unittest.main()
