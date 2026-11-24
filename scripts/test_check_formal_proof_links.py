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

import json
import os
import tempfile
import unittest

from check_formal_proof_links import (
    check_link,
    declaration_near,
    declares,
    line_anchor,
    links_from_metadata,
    load_metadata,
    mask_comments,
    module_path,
    names_agree,
    raw_url,
)

# The shape `lake exe extract_names` writes (schema version 2).
RAW = {
    "schemaVersion": 2,
    "problems": [
        {
            "theorem": "Erdos1.erdos_1",
            "module": "FormalConjectures.ErdosProblems.«1»",
            "category": "research solved",
            "formalProofs": [
                {"kind": "formal_conjectures",
                 "link": "https://github.com/someone/formal-conjectures/blob/abc123/FormalConjectures/ErdosProblems/1.lean#L40",
                 "conditions": []},
            ],
        },
        {
            "theorem": "Erdos1.erdos_1.variants.two",
            "module": "FormalConjectures.ErdosProblems.«1»",
            "category": "research solved",
            "formalProofs": [
                {"kind": "lean4", "link": "https://example.org/a.lean", "conditions": []},
                {"kind": "other_system", "link": "https://example.org/b.v", "conditions": ["GRH"]},
            ],
        },
        {
            "theorem": "Erdos1.erdos_1.variants.open",
            "module": "FormalConjectures.ErdosProblems.«1»",
            "category": "research open",
        },
    ],
}

# The shape the website publishes: the same entries under `conjectures`, with `githubPath`.
PUBLISHED = {
    "conjectures": [
        {
            "theorem": "Green52.green_52_log",
            "module": "FormalConjectures.GreensOpenProblems.«52»",
            "githubPath": "FormalConjectures/GreensOpenProblems/52.lean",
            "formalProofs": [{"kind": "lean4", "link": "https://example.org/g.lean", "conditions": []}],
        },
        {"theorem": "Green52.green_52", "module": "FormalConjectures.GreensOpenProblems.«52»", "formalProofs": []},
    ],
}


def link(kind="formal_conjectures", url="https://github.com/x/y/blob/c/F.lean", name="Erdos1.erdos_1"):
    return {"file": "FormalConjectures/ErdosProblems/1.lean", "name": name, "kind": kind,
            "url": url, "conditions": []}


class LinksFromMetadataTest(unittest.TestCase):

    def test_one_record_per_formal_proof_with_the_full_name(self):
        links = links_from_metadata(RAW)
        self.assertEqual([(l["name"], l["kind"]) for l in links], [
            ("Erdos1.erdos_1", "formal_conjectures"),
            ("Erdos1.erdos_1.variants.two", "lean4"),
            ("Erdos1.erdos_1.variants.two", "other_system"),
        ])

    def test_keeps_conditions(self):
        links = links_from_metadata(RAW)
        self.assertEqual(links[2]["conditions"], ["GRH"])

    def test_file_from_the_module(self):
        self.assertEqual(links_from_metadata(RAW)[0]["file"], "FormalConjectures/ErdosProblems/1.lean")

    def test_reads_the_published_shape(self):
        links = links_from_metadata(PUBLISHED)
        self.assertEqual([(l["name"], l["file"], l["url"]) for l in links], [
            ("Green52.green_52_log", "FormalConjectures/GreensOpenProblems/52.lean", "https://example.org/g.lean"),
        ])

    def test_rejects_unknown_metadata(self):
        with self.assertRaises(ValueError):
            links_from_metadata({"something": []})

    def test_loads_a_local_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "conjectures.json")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(RAW, f, ensure_ascii=False)
            self.assertEqual(len(links_from_metadata(load_metadata(path))), 3)


class ModulePathTest(unittest.TestCase):

    def test_guillemets_are_dropped(self):
        self.assertEqual(module_path("FormalConjectures.GreensOpenProblems.«52»"),
                         "FormalConjectures/GreensOpenProblems/52.lean")


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


TARGET = '''
theorem erdos_1 : answer(True) ↔ ∀ n : ℕ, 0 ≤ n := by
  sorry

theorem erdos_1.variants.two : True := by
  sorry
'''


class DeclaresTest(unittest.TestCase):

    def test_a_namespace_prefix_on_our_side_still_matches(self):
        self.assertTrue(declares(TARGET, "Erdos1.erdos_1"))
        self.assertTrue(declares(TARGET, "Erdos1.erdos_1.variants.two"))

    def test_returns_false_when_absent(self):
        self.assertFalse(declares(TARGET, "Erdos1.erdos_2"))

    def test_does_not_match_a_prefix(self):
        self.assertFalse(declares(TARGET, "op"))

    def test_does_not_match_a_longer_dotted_name(self):
        # Looking up `erdos_1` where only the dotted variants exist must find nothing.
        only_variants = TARGET.replace("theorem erdos_1 :", "theorem erdos_2 :")
        self.assertFalse(declares(only_variants, "Erdos1.erdos_1"))
        self.assertFalse(declares(only_variants, "Erdos1.erdos_1.variants"))

    def test_does_not_match_a_different_parent_with_the_same_final_segment(self):
        target = "theorem erdos_1.parts.i : True := trivial"
        self.assertFalse(declares(target, "erdos_1.variants.i"))
        self.assertTrue(declares(target, "erdos_1.parts.i"))

    def test_a_namespace_prefix_on_either_side_still_matches(self):
        self.assertTrue(declares("theorem Erdos1.erdos_1.parts.i : True := trivial", "erdos_1.parts.i"))
        in_namespace = "namespace erdos_1.parts\ntheorem i : True := trivial\nend erdos_1.parts"
        self.assertTrue(declares(in_namespace, "erdos_1.parts.i"))

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
            self.assertFalse(declares(target, "erdos_1"), target)

    def test_matches_a_name_with_universe_parameters(self):
        self.assertTrue(declares("theorem erdos_1.{u} : True := trivial", "erdos_1"))

    def test_an_alias_counts(self):
        self.assertTrue(declares("alias erdos_1 := Elsewhere.erdos_1_proof", "Erdos1.erdos_1"))


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
        self.assertEqual([f["kind"] for f in check_link(l, cache)], ["anchor-not-on-declaration"])

    def test_anchor_on_a_declaration_is_clean(self):
        l = link(url="https://github.com/x/y/blob/c/F.lean#L1")
        cache = {raw_url(l["url"]): (200, "theorem erdos_1 : True := trivial\n")}
        self.assertEqual(check_link(l, cache), [])

    def test_name_missing_in_a_fork_is_reported(self):
        cache = {raw_url(link()["url"]): (200, "theorem something_else : True := trivial")}
        self.assertEqual([f["kind"] for f in check_link(link(), cache)], ["name-not-found"])

    def test_name_present_in_a_fork_is_clean(self):
        cache = {raw_url(link()["url"]): (200, "theorem erdos_1 : True := trivial")}
        self.assertEqual(check_link(link(), cache), [])

    def test_dotted_variant_does_not_stand_in_for_the_name(self):
        # Anchorless fork link: a target that only declares `erdos_1.variants.two` does not
        # contain `erdos_1`.
        cache = {raw_url(link()["url"]): (200, "theorem erdos_1.variants.two : True := trivial")}
        self.assertEqual([f["kind"] for f in check_link(link(), cache)], ["name-not-found"])

    def test_anchor_on_an_alias_is_clean(self):
        l = link(kind="lean4", url="https://github.com/x/y/blob/c/F.lean#L3")
        body = "/-- The statement linked from formal-conjectures. -/\n\nalias statement_erdos_1 := Gallery.erdos_1\n"
        self.assertEqual(check_link(l, {raw_url(l["url"]): (200, body)}), [])

    def test_name_missing_in_an_external_repo_is_not_reported(self):
        l = link(kind="lean4")
        cache = {raw_url(l["url"]): (200, "theorem Erdos1 : True := trivial")}
        self.assertEqual(check_link(l, cache), [])

    def test_non_lean_target_is_only_checked_for_reachability(self):
        l = link(kind="other_system", url="https://example.org/b.v")
        cache = {l["url"]: (200, "Lemma erdos_1 : True.")}
        self.assertEqual(check_link(l, cache), [])


if __name__ == "__main__":
    unittest.main()
