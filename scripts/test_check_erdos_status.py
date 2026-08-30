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

"""Tests for `check_erdos_status.py`: status scanning and issue syncing."""

import os
import tempfile
import unittest
from unittest import mock

import check_erdos_status
from check_erdos_status import issues_to_close, scan_lean_files


def issue(number, problem, repo="solved", site="formally solved"):
    return {
        "number": number,
        "title": f"Erdős Problem {problem}: status mismatch "
                 f"(repo={repo}, erdosproblems.com={site})",
    }


class IssuesToCloseTest(unittest.TestCase):

    def test_closes_when_the_mismatch_is_gone(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open=set(), known={"71"}), [100])

    def test_keeps_one_that_still_mismatches(self):
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open={"71"}, known={"71"}), [])

    def test_keeps_one_whose_status_cannot_be_read(self):
        # A problem missing from `known` has a YAML state the script does not recognise.
        # That is "we cannot tell", which must not be read as "resolved".
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open=set(), known=set()), [])

    def test_compares_problem_numbers_as_strings(self):
        # `find_mismatches` keys problems by string; comparing an int against that set
        # silently matches nothing and would close everything.
        self.assertEqual(
            issues_to_close([issue(100, "71")], still_open={"71"}, known={"71"}), [])

    def test_ignores_issues_with_an_unrelated_title(self):
        self.assertEqual(
            issues_to_close([{"number": 100, "title": "Something else entirely"}],
                            still_open=set(), known={"71"}), [])

    def test_handles_several_at_once(self):
        issues = [issue(1, "71"), issue(2, "209"), issue(3, "353")]
        self.assertEqual(
            issues_to_close(issues, still_open={"209"}, known={"71", "209"}), [1])


class ScanLeanFilesTest(unittest.TestCase):
    """scan_lean_files must see multi-line annotations and scope a formal_proof
    attribute to the theorem whose own annotation carries it."""

    def scan(self, files):
        with tempfile.TemporaryDirectory() as tmp:
            for name, content in files.items():
                with open(os.path.join(tmp, name), "w", encoding="utf-8") as f:
                    f.write(content)
            with mock.patch.object(check_erdos_status, "ERDOS_DIR", tmp):
                return scan_lean_files()

    def test_multiline_annotation_is_seen(self):
        # The category attribute spans several lines, with formal_proof listed
        # underneath. The old regex stopped at the first `]`, so it never saw
        # the theorem at all and the problem was dropped from the scan.
        content = (
            "import Mathlib\n\n"
            "example : True := by trivial\n\n"
            "@[category research solved, AMS 28 30,\n"
            "formal_proof using lean4 at \"...\",\n"
            "formal_proof using formal_conjectures at \"...\"]\n"
            "theorem erdos_848 : True := by trivial\n"
        )
        self.assertEqual(self.scan({"848.lean": content}), {"848": "formally solved"})

    def test_variant_formal_proof_does_not_upgrade_main(self):
        # The variant is formally proved but the main theorem is not. A proof
        # of one variant does not formally solve the whole problem, so the
        # problem must stay 'solved', not become 'formally solved'.
        content = (
            "import Mathlib\n\n"
            "@[category research solved]\n"
            "theorem erdos_848 : True := by trivial\n\n"
            "@[category research solved,\n"
            "formal_proof using lean4 at \"...\"]\n"
            "theorem erdos_848.variants.asymptotic : True := by trivial\n"
        )
        self.assertEqual(self.scan({"848.lean": content}), {"848": "solved"})

    def test_multiline_open_annotation_stays_open(self):
        # A multi-line attribute on an open problem must not be skipped.
        content = (
            "import Mathlib\n\n"
            "@[category research open, AMS 02 10]\n"
            "theorem erdos_1041 : True := by trivial\n"
        )
        self.assertEqual(self.scan({"1041.lean": content}), {"1041": "open"})

    def test_proof_elsewhere_in_file_does_not_upgrade(self):
        # A formal_proof attribute elsewhere in the file (here on an unrelated
        # helper theorem) must not leak into an unsolved problem.
        content = (
            "import Mathlib\n\n"
            "@[category research solved]\n"
            "theorem erdos_180 : True := by trivial\n\n"
            "@[category research solved,\n"
            "formal_proof using other_system at \"...\"]\n"
            "theorem helper_lemma : True := by trivial\n"
        )
        self.assertEqual(self.scan({"180.lean": content}), {"180": "solved"})


if __name__ == "__main__":
    unittest.main()
