#!/usr/bin/env python3
"""Tests for `status_counts.py`.

Run with `python3 -m unittest discover -s site -p 'test_*.py'`.
No dependencies beyond the standard library.

The counts these produce have to agree with what `lake exe extract_names`
reports, so most of what is checked here are the cases where reading the
source text could disagree with what Lean sees.
"""

import contextlib
import os
import pathlib
import subprocess
import tempfile
import unittest

import status_counts as sc


def counts(source):
    """Counts one file, given without the trailing newline handling of a file."""
    return sc.count_statuses(source)


class CategoryTest(unittest.TestCase):
    """The plain cases, one attribute on one theorem."""

    def test_open(self):
        self.assertEqual(counts('@[category research open, AMS 11]\ntheorem a : True := trivial'),
                         {'open': 1, 'solved': 0, 'formal': 0})

    def test_solved(self):
        self.assertEqual(counts('@[category research solved, AMS 11]\ntheorem a : True := trivial'),
                         {'open': 0, 'solved': 1, 'formal': 0})

    def test_other_categories_count_for_nothing(self):
        for category in ('test', 'API', 'textbook'):
            with self.subTest(category=category):
                self.assertEqual(counts(f'@[category {category}]\ntheorem a : True := trivial'),
                                 {'open': 0, 'solved': 0, 'formal': 0})

    def test_uncategorised_theorem(self):
        self.assertEqual(counts('theorem a : True := trivial'),
                         {'open': 0, 'solved': 0, 'formal': 0})

    def test_attribute_without_category(self):
        self.assertEqual(counts('@[simp]\ntheorem a : True := trivial'),
                         {'open': 0, 'solved': 0, 'formal': 0})


class FormalProofTest(unittest.TestCase):

    def test_solved_with_formal_proof(self):
        source = ('@[category research solved, formal_proof using lean4 at "https://example.com"]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 1, 'formal': 1})

    def test_several_formal_proofs_on_one_theorem_count_once(self):
        # `extract_names` keys its results by declaration name, so a theorem
        # carrying two links is still one formally proved statement.
        source = ('@[category research solved,\n'
                  'formal_proof using lean4 at "https://example.com/one",\n'
                  'formal_proof using formal_conjectures at "https://example.com/two"]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 1, 'formal': 1})

    def test_formal_proof_outside_research_solved(self):
        # Not every formally proved statement is `research solved`; the live
        # data has them on `textbook` and `test` too.
        source = ('@[category textbook, formal_proof using lean4 at "https://example.com"]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 0, 'formal': 1})

    def test_every_formal_proof_kind(self):
        for kind in ('lean4', 'formal_conjectures', 'other_system'):
            with self.subTest(kind=kind):
                source = (f'@[category research solved, formal_proof using {kind} at "https://e.com"]\n'
                          'theorem a : True := trivial')
                self.assertEqual(counts(source)['formal'], 1)

    def test_conditional_formal_proof(self):
        # The `conditional ... assuming` modifier added in #4368.
        source = ('@[category research solved,\n'
                  'formal_proof using lean4 conditional at "https://example.com" assuming rh]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 1, 'formal': 1})

    def test_formally_solved_category_before_the_refactor(self):
        # Before #3645 this category was how a formal proof was recorded.
        source = ('@[category research formally solved using lean4 at "https://example.com"]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 1, 'formal': 1})


class DeclarationKindTest(unittest.TestCase):
    """Only what `extract_names` reports as a theorem is counted."""

    def test_lemma_counts(self):
        self.assertEqual(counts('@[category research open]\nlemma a : True := trivial')['open'], 1)

    def test_instance_counts(self):
        source = '@[category test]\ninstance foo : Nonempty Nat := ⟨0⟩'
        self.assertEqual(counts(source), {'open': 0, 'solved': 0, 'formal': 0})

    def test_definitions_do_not_count(self):
        for keyword in ('def', 'abbrev', 'example'):
            with self.subTest(keyword=keyword):
                source = f'@[category research open]\n{keyword} a : Nat := 0'
                self.assertEqual(counts(source)['open'], 0)

    def test_modifiers_before_the_keyword(self):
        for modifier in ('protected', 'noncomputable', 'nonrec'):
            with self.subTest(modifier=modifier):
                source = f'@[category research open]\n{modifier} theorem a : True := trivial'
                self.assertEqual(counts(source)['open'], 1)


class InternalDeclarationTest(unittest.TestCase):
    """Lean marks some declarations internal and `extract_names` drops them."""

    def test_private_is_skipped(self):
        source = '@[category API]\nprivate lemma a : True := trivial'
        self.assertEqual(counts(source), {'open': 0, 'solved': 0, 'formal': 0})

    def test_private_research_open_is_skipped(self):
        source = '@[category research open]\nprivate theorem a : True := trivial'
        self.assertEqual(counts(source)['open'], 0)

    def test_underscore_prefixed_name_component_is_skipped(self):
        source = '@[category research solved]\ntheorem foo.variants._1000_le_bar : True := trivial'
        self.assertEqual(counts(source)['solved'], 0)

    def test_underscore_at_the_start_is_skipped(self):
        source = '@[category research solved]\ntheorem _private_helper : True := trivial'
        self.assertEqual(counts(source)['solved'], 0)

    def test_underscore_inside_a_component_still_counts(self):
        source = '@[category research solved]\ntheorem erdos_370.variants.le_bar : True := trivial'
        self.assertEqual(counts(source)['solved'], 1)


class CommentTest(unittest.TestCase):
    """Attribute names appear in prose, which must not be counted."""

    def test_docstring_mentioning_a_category(self):
        source = ('/-- We record it as a `category research solved` statement. -/\n'
                  '@[category research open]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 1, 'solved': 0, 'formal': 0})

    def test_module_docstring_mentioning_an_attribute(self):
        source = ('/-!\n# Attributes\n'
                  'Use `@[category research solved, formal_proof using lean4 at "..."]` here.\n-/\n')
        self.assertEqual(counts(source), {'open': 0, 'solved': 0, 'formal': 0})

    def test_commented_out_attribute(self):
        source = ('-- @[category research solved]\n'
                  '@[category research open]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 1, 'solved': 0, 'formal': 0})

    def test_nested_block_comments(self):
        source = ('/- outer /- inner @[category research solved] -/ still comment -/\n'
                  '@[category research open]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 1, 'solved': 0, 'formal': 0})

    def test_trailing_comment_after_an_attribute(self):
        source = ('@[category research open] -- not @[category research solved]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 1, 'solved': 0, 'formal': 0})


class LayoutTest(unittest.TestCase):
    """Attributes are written in more than one shape."""

    def test_attribute_split_over_lines(self):
        source = ('@[category research solved, AMS 11,\n'
                  ' formal_proof using lean4 at\n'
                  ' "https://example.com/a/very/long/link"]\n'
                  'theorem a : True := trivial')
        self.assertEqual(counts(source), {'open': 0, 'solved': 1, 'formal': 1})

    def test_category_is_not_the_first_attribute(self):
        source = '@[simp, AMS 11, category research open]\ntheorem a : True := trivial'
        self.assertEqual(counts(source)['open'], 1)

    def test_theorem_on_the_line_after_a_blank_one(self):
        source = '@[category research open]\n\ntheorem a : True := trivial'
        self.assertEqual(counts(source)['open'], 1)

    def test_nested_brackets_inside_the_attribute(self):
        source = '@[category research open, foo [1, 2]]\ntheorem a : True := trivial'
        self.assertEqual(counts(source)['open'], 1)

    def test_several_theorems_in_one_file(self):
        source = ('@[category research open]\ntheorem a : True := trivial\n\n'
                  '@[category research solved, formal_proof using lean4 at "https://e.com"]\n'
                  'theorem b : True := trivial\n\n'
                  '@[category research open]\ntheorem c : True := trivial\n')
        self.assertEqual(counts(source), {'open': 2, 'solved': 1, 'formal': 1})

    def test_attribute_with_no_declaration_after_it(self):
        self.assertEqual(counts('@[category research open]\n'),
                         {'open': 0, 'solved': 0, 'formal': 0})

    def test_empty_file(self):
        self.assertEqual(counts(''), {'open': 0, 'solved': 0, 'formal': 0})


class HistoryTest(unittest.TestCase):
    """The walk over commits, including the per-blob cache."""

    def setUp(self):
        self.dir = pathlib.Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.enterContext(contextlib.chdir(self.dir))
        self.git('init', '-q', '-b', 'main')
        self.git('config', 'user.email', 'test@example.com')
        self.git('config', 'user.name', 'Test')

    def git(self, *arguments, **environment):
        subprocess.run(['git', *arguments], check=True, capture_output=True,
                       env=dict(os.environ, **environment))

    def commit(self, path, source, when):
        target = self.dir / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source, encoding='utf-8')
        self.git('add', '-A')
        self.git('commit', '-q', '-m', f'add {path}',
                 GIT_AUTHOR_DATE=when, GIT_COMMITTER_DATE=when)

    def series(self, start_date='2025-01-01'):
        return sc.get_status_counts_over_time(
            start_date, ['Date', 'Open', 'Solved', 'Formally proved'])

    def test_counts_accumulate_over_commits(self):
        self.commit('FormalConjectures/A.lean',
                    '@[category research open]\ntheorem a : True := trivial',
                    '2025-06-01T12:00:00')
        self.commit('FormalConjectures/B.lean',
                    '@[category research solved, formal_proof using lean4 at "https://e.com"]\n'
                    'theorem b : True := trivial',
                    '2025-06-02T12:00:00')
        rows = self.series()
        self.assertEqual([row[1:] for row in rows], [[1, 0, 0], [1, 1, 1]])

    def test_rows_are_in_chronological_order(self):
        self.commit('FormalConjectures/A.lean', 'theorem a : True := trivial',
                    '2025-06-01T12:00:00')
        self.commit('FormalConjectures/B.lean', 'theorem b : True := trivial',
                    '2025-06-02T12:00:00')
        dates = [row[0] for row in self.series()]
        self.assertEqual(dates, sorted(dates))

    def test_identical_files_are_counted_separately(self):
        # Two files with the same contents share a blob, so the cache must be
        # read once per file rather than once per blob.
        source = '@[category research open]\ntheorem a : True := trivial'
        self.commit('FormalConjectures/A.lean', source, '2025-06-01T12:00:00')
        self.commit('FormalConjectures/B.lean', source, '2025-06-02T12:00:00')
        self.assertEqual(self.series()[-1][1], 2)

    def test_files_outside_the_counted_tree_are_ignored(self):
        self.commit('FormalConjectures/ForMathlib/A.lean',
                    '@[category research open]\ntheorem a : True := trivial',
                    '2025-06-01T12:00:00')
        self.commit('FormalConjecturesUtil/B.lean',
                    '@[category research open]\ntheorem b : True := trivial',
                    '2025-06-02T12:00:00')
        self.assertEqual([row[1:] for row in self.series()], [[0, 0, 0], [0, 0, 0]])

    def test_commits_before_the_start_date_are_dropped(self):
        self.commit('FormalConjectures/A.lean', 'theorem a : True := trivial',
                    '2025-06-01T12:00:00')
        self.commit('FormalConjectures/B.lean', 'theorem b : True := trivial',
                    '2026-06-01T12:00:00')
        self.assertEqual(len(self.series(start_date='2026-01-01')), 1)

    def test_wrong_number_of_columns(self):
        with self.assertRaisesRegex(ValueError, 'length 4'):
            sc.get_status_counts_over_time('2025-01-01', ['Date', 'Open'])


if __name__ == '__main__':
    unittest.main()
