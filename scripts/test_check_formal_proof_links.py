# Copyright 2026 The Formal Conjectures Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Tests for the parsing and policy in `check_formal_proof_links.py`. No network."""

import os
import tempfile
import unittest

from check_formal_proof_links import (
    check_link,
    declaration_near,
    declaration_statement,
    find_links,
    line_anchor,
    mask_comments,
    names_agree,
    normalise,
    raw_url,
)

FILE = '''
/-- Solved. -/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/someone/formal-conjectures/blob/abc123/FormalConjectures/ErdosProblems/1.lean#L40"]
theorem erdos_1 : answer(True) ↔ ∀ n : ℕ, 0 ≤ n := by
  sorry

/-- Two proofs. -/
@[category research solved, AMS 11,
  formal_proof using lean4 at "https://example.org/a.lean",
  formal_proof using other_system at "https://example.org/b.v"]
theorem erdos_1.variants.two : True := by
  sorry

@[category research open, AMS 11]
theorem erdos_1.variants.open : answer(sorry) ↔ True := by
  sorry
'''


def link(kind="formal_conjectures", url="https://github.com/x/y/blob/c/F.lean", name="erdos_1",
         statement=" : answer(True) ↔ ∀ n : ℕ, 0 ≤ n "):
    return {"file": "FormalConjectures/ErdosProblems/1.lean", "name": name, "kind": kind,
            "url": url, "statement": statement}


class FindLinksTest(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        sub = os.path.join(self.tmp.name, "ErdosProblems")
        os.makedirs(sub)
        with open(os.path.join(sub, "1.lean"), "w", encoding="utf-8") as f:
            f.write(FILE)

    def tearDown(self):
        self.tmp.cleanup()

    def test_finds_every_tag_with_its_declaration(self):
        links = find_links(self.tmp.name)
        self.assertEqual([(l["name"], l["kind"]) for l in links], [
            ("erdos_1", "formal_conjectures"),
            ("erdos_1.variants.two", "lean4"),
            ("erdos_1.variants.two", "other_system"),
        ])

    def test_records_the_statement_of_the_annotated_declaration(self):
        links = find_links(self.tmp.name)
        self.assertEqual(normalise(links[0]["statement"]), ":answer(True)↔∀n:ℕ,0≤n")


COMMENTED_FILE = '''
@[category research solved, AMS 3, formal_proof using lean4 at "https://example.org/c.lean"]
-- The formal proof was done by someone else.
theorem boxdot : True := by
  sorry

-- @[category research solved, formal_proof using lean4 at "https://example.org/old.lean"]
@[category research open, AMS 3]
theorem still_open : True := by
  sorry
'''


class FindLinksCommentsTest(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        with open(os.path.join(self.tmp.name, "C.lean"), "w", encoding="utf-8") as f:
            f.write(COMMENTED_FILE)

    def tearDown(self):
        self.tmp.cleanup()

    def test_a_comment_between_attribute_and_declaration_does_not_hide_it(self):
        links = find_links(self.tmp.name)
        self.assertEqual([(l["name"], l["url"]) for l in links], [("boxdot", "https://example.org/c.lean")])
        self.assertEqual(normalise(links[0]["statement"]), ":True")

    def test_a_commented_out_attribute_is_not_a_link(self):
        urls = [l["url"] for l in find_links(self.tmp.name)]
        self.assertNotIn("https://example.org/old.lean", urls)


class MaskCommentsTest(unittest.TestCase):

    def test_keeps_length_and_newlines(self):
        text = "a -- note\n/- block\n -/ b\n/-- doc -/ c"
        masked = mask_comments(text)
        self.assertEqual(len(masked), len(text))
        self.assertEqual(masked.count("\n"), text.count("\n"))
        self.assertEqual(masked.split(), ["a", "b", "c"])

    def test_nested_block_comments(self):
        self.assertEqual(mask_comments("/- a /- b -/ c -/ d").split(), ["d"])

    def test_double_dash_inside_a_string_is_not_a_comment(self):
        self.assertEqual(mask_comments('x "a--b" y'), 'x "a--b" y')


class DeclarationStatementTest(unittest.TestCase):

    def test_matches_on_the_final_name_segment(self):
        self.assertEqual(
            normalise(declaration_statement(FILE, "Erdos1.erdos_1.variants.two")), ":True")

    def test_returns_none_when_absent(self):
        self.assertIsNone(declaration_statement(FILE, "erdos_2"))

    def test_does_not_match_a_prefix(self):
        # `erdos_1` must not be found by looking for `erdos_1.variants.op`.
        self.assertIsNone(declaration_statement(FILE, "op"))

    def test_does_not_match_a_longer_dotted_name(self):
        # Looking up `erdos_1` where only the dotted variants exist must find nothing.
        only_variants = FILE.replace("theorem erdos_1 :", "theorem erdos_2 :")
        self.assertIsNone(declaration_statement(only_variants, "erdos_1"))
        self.assertIsNone(declaration_statement(only_variants, "erdos_1.variants"))

    def test_does_not_match_a_different_parent_with_the_same_final_segment(self):
        target = "theorem erdos_1.parts.i : True := trivial"
        self.assertIsNone(declaration_statement(target, "erdos_1.variants.i"))
        self.assertEqual(normalise(declaration_statement(target, "erdos_1.parts.i")), ":True")

    def test_a_namespace_prefix_on_either_side_still_matches(self):
        qualified = "theorem Erdos1.erdos_1.parts.i : True := trivial"
        self.assertEqual(normalise(declaration_statement(qualified, "erdos_1.parts.i")), ":True")
        in_namespace = "namespace erdos_1.parts\ntheorem i : True := trivial\nend erdos_1.parts"
        self.assertEqual(normalise(declaration_statement(in_namespace, "erdos_1.parts.i")), ":True")

    def test_names_agree_at_dot_boundaries_only(self):
        self.assertTrue(names_agree("erdos_1", "erdos_1"))
        self.assertTrue(names_agree("A.erdos_1", "erdos_1"))
        self.assertTrue(names_agree("i", "erdos_1.parts.i"))
        self.assertFalse(names_agree("xerdos_1", "erdos_1"))
        self.assertFalse(names_agree("erdos_1.parts.i", "erdos_1.variants.i"))

    def test_a_theorem_mentioned_in_a_comment_is_not_found(self):
        for target in ["-- theorem erdos_1 : True := trivial\ntheorem other : True := trivial",
                       "/- theorem erdos_1 : True := trivial -/",
                       "/-- Compare theorem erdos_1. -/\ntheorem other : True := trivial"]:
            self.assertIsNone(declaration_statement(target, "erdos_1"), target)

    def test_a_colon_equals_in_a_comment_does_not_end_the_statement(self):
        target = "theorem erdos_1 : -- note := here\n  True := trivial"
        self.assertEqual(normalise(declaration_statement(target, "erdos_1")), ":True")

    def test_matches_a_name_with_universe_parameters(self):
        self.assertEqual(
            normalise(declaration_statement("theorem erdos_1.{u} : True := trivial", "erdos_1")),
            ".{u}:True")


class RawUrlTest(unittest.TestCase):

    def test_blob_url_becomes_raw_and_drops_the_anchor(self):
        self.assertEqual(
            raw_url("https://github.com/o/r/blob/abc/Dir/F.lean#L40"),
            "https://raw.githubusercontent.com/o/r/abc/Dir/F.lean")

    def test_line_range_anchor(self):
        self.assertEqual(
            raw_url("https://github.com/o/r/blob/abc/F.lean#L40-L42"),
            "https://raw.githubusercontent.com/o/r/abc/F.lean")

    def test_other_urls_unchanged(self):
        self.assertEqual(raw_url("https://example.org/a.lean"), "https://example.org/a.lean")


class LineAnchorTest(unittest.TestCase):

    def test_single_line(self):
        self.assertEqual(line_anchor("https://github.com/o/r/blob/abc/F.lean#L40"), (40, 40))

    def test_range(self):
        self.assertEqual(line_anchor("https://github.com/o/r/blob/abc/F.lean#L40-L95"), (40, 95))

    def test_none(self):
        self.assertIsNone(line_anchor("https://github.com/o/r/blob/abc/F.lean"))


class DeclarationNearTest(unittest.TestCase):
    BODY = "\n".join(["-- header"] * 20 + ["theorem t :", "    True", "  :=", "  trivial"] + [""] * 20)

    def test_anchor_on_the_theorem_line(self):
        self.assertTrue(declaration_near(self.BODY, (21, 21)))

    def test_anchor_on_the_assign_line_below_a_long_statement(self):
        self.assertTrue(declaration_near(self.BODY, (23, 23)))

    def test_anchor_range_covering_the_proof(self):
        self.assertTrue(declaration_near(self.BODY, (10, 40)))

    def test_anchor_far_from_any_declaration(self):
        self.assertFalse(declaration_near(self.BODY, (2, 2)))

    def test_an_alias_at_the_anchor_counts(self):
        body = "\n".join(["-- header"] * 20 + ["alias statement_t := Foo.t"] + [""] * 20)
        self.assertTrue(declaration_near(body, (21, 21)))

    def test_a_theorem_after_a_custom_command_counts(self):
        body = "\n".join(["-- header"] * 20 + ["fc_compact_decl theorem t :", "    True :=", "  trivial"] + [""] * 20)
        self.assertTrue(declaration_near(body, (21, 21)))

    def test_the_word_theorem_in_a_name_does_not_count(self):
        body = "\n".join(["-- header"] * 20 + ["def my_theorem_list := 3", "#check Nat.theorem_like"] + [""] * 20)
        self.assertFalse(declaration_near(body, (21, 21)))

    def test_a_theorem_inside_a_block_comment_near_the_anchor_does_not_count(self):
        body = "\n".join(["-- header"] * 20 + ["/-", "theorem t : True := trivial", "-/"] + [""] * 20)
        self.assertFalse(declaration_near(body, (22, 22)))


class CheckLinkTest(unittest.TestCase):

    def test_unreachable(self):
        cache = {raw_url(link()["url"]): (404, "")}
        findings = check_link(link(), cache, wayback=False)
        self.assertEqual([f["kind"] for f in findings], ["unreachable"])
        self.assertNotIn("wayback", findings[0])

    def test_stale_anchor_is_reported(self):
        l = link(url="https://github.com/x/y/blob/c/F.lean#L50")
        cache = {raw_url(l["url"]): (200, "theorem erdos_1 : True := trivial\n" + "\n" * 80)}
        kinds = [f["kind"] for f in check_link(l, cache)]
        self.assertEqual(kinds, ["anchor-not-on-declaration"])

    def test_name_missing_in_a_fork_is_reported(self):
        cache = {raw_url(link()["url"]): (200, "theorem something_else : True := trivial")}
        kinds = [f["kind"] for f in check_link(link(), cache)]
        self.assertEqual(kinds, ["name-not-found"])

    def test_dotted_variant_does_not_stand_in_for_the_name(self):
        # Anchorless fork link, default run (no --compare): a target that only declares
        # `erdos_1.variants.two` does not contain `erdos_1`.
        cache = {raw_url(link()["url"]): (200, "theorem erdos_1.variants.two : True := trivial")}
        kinds = [f["kind"] for f in check_link(link(), cache, compare=False)]
        self.assertEqual(kinds, ["name-not-found"])

    def test_anchor_on_an_alias_is_clean(self):
        l = link(kind="lean4", url="https://github.com/x/y/blob/c/F.lean#L3")
        body = "/-- The statement linked from formal-conjectures. -/\n\nalias statement_erdos_1 := Gallery.erdos_1\n"
        self.assertEqual(check_link(l, {raw_url(l["url"]): (200, body)}, compare=False), [])

    def test_name_declared_as_an_alias_in_a_fork_is_found(self):
        cache = {raw_url(link()["url"]): (200, "alias erdos_1 := Elsewhere.erdos_1_proof")}
        self.assertEqual(check_link(link(), cache, compare=False), [])

    def test_name_missing_in_an_external_repo_is_not_reported(self):
        l = link(kind="lean4")
        cache = {raw_url(l["url"]): (200, "theorem Erdos1 : True := trivial")}
        self.assertEqual(check_link(l, cache), [])

    def test_same_statement_is_clean(self):
        cache = {raw_url(link()["url"]): (200, "theorem erdos_1 : answer(True) ↔ ∀ n : ℕ, 0 ≤ n := by\n  trivial")}
        self.assertEqual(check_link(link(), cache, compare=True), [])

    def test_different_statement_is_advisory(self):
        cache = {raw_url(link()["url"]): (200, "theorem erdos_1 : ∀ n : ℕ, 0 ≤ n := by\n  trivial")}
        kinds = [f["kind"] for f in check_link(link(), cache, compare=True)]
        self.assertEqual(kinds, ["statement-differs"])
        self.assertEqual(check_link(link(), cache, compare=False), [])

    def test_non_lean_target_is_only_checked_for_reachability(self):
        l = link(kind="other_system", url="https://example.org/b.v")
        cache = {l["url"]: (200, "Lemma erdos_1 : True.")}
        self.assertEqual(check_link(l, cache, compare=True), [])


if __name__ == "__main__":
    unittest.main()
