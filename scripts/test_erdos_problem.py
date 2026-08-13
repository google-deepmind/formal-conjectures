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

"""Tests for the LaTeX that `erdos_problem.py` pulls out of a problem page.

The tests run on saved markup and make no network request.
"""

import unittest

from erdos_problem import blocks, cross_references, to_text

PAGE = """
<div class="problem-box">
  <div class="problem-text">
    <div id="content" style="white-space: pre-line;">
      Let $r\\geq 3$.<br><br>Does the set have density $0$?
    </div>
  </div>
  <div class="problem-additional-text" style="white-space: pre-line;">
    Erd\\H{o}s \\cite{Er76d} claims this is 'easy' for $r=2$.<br>
    <br>See also <a href="/1081" rel="nofollow">1081</a>, and
    <a href="/1107" rel="nofollow">1107</a> for the case of $r+1$ summands.
  </div>
  <div class="problem-additional-text" style="white-space: pre-line;">
    <h3>References</h3>
    [BaBr94] Baker, R. C., <i>On sums of two squarefull numbers</i>. (1994), 1--5.
  </div>
  <div class="problem-additional-text" style="text-align:center">
    <a href="/940">Back to the problem</a>
  </div>
</div>
"""


class ToTextTest(unittest.TestCase):

    def test_keeps_latex_unrendered(self):
        self.assertEqual(to_text("$3^7\\cdot 61^5$"), "$3^7\\cdot 61^5$")

    def test_turns_a_break_into_a_newline(self):
        self.assertEqual(to_text("one<br>two"), "one\ntwo")

    def test_turns_a_problem_link_into_its_number(self):
        self.assertEqual(to_text('see <a href="/1107">1107</a> too'), "see [1107] too")

    def test_unescapes_entities(self):
        self.assertEqual(to_text("a &amp; b"), "a & b")

    def test_drops_a_trailing_back_link(self):
        self.assertEqual(to_text('body<br><a href="/940">Back to the problem</a>'), "body")


class BlocksTest(unittest.TestCase):

    def test_reads_the_statement_first(self):
        self.assertTrue(blocks(PAGE)[0].startswith("Let $r\\geq 3$."))

    def test_keeps_the_remarks_which_carry_the_status(self):
        self.assertIn("'easy' for $r=2$", "\n".join(blocks(PAGE)))

    def test_keeps_the_reference_list(self):
        self.assertIn("[BaBr94] Baker", "\n".join(blocks(PAGE)))

    def test_drops_the_back_link_block(self):
        self.assertNotIn("[940]", blocks(PAGE))

    def test_finds_no_block_in_an_unrecognised_page(self):
        self.assertEqual(blocks("<html><body>nothing here</body></html>"), [])


class CrossReferencesTest(unittest.TestCase):

    def test_lists_linked_problems_in_order(self):
        self.assertEqual(cross_references(PAGE), ["1081", "1107", "940"])

    def test_does_not_repeat_a_number(self):
        self.assertEqual(
            cross_references('<a href="/12">a</a><a href="/12">b</a>'), ["12"])


if __name__ == "__main__":
    unittest.main()
