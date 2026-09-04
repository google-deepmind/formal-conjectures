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

"""Tests for canonical and transitional formal-proof link extraction."""

import json
import pathlib
import tempfile
import unittest

from check_proof_links import links_from_extract, unique_links


class ProofLinksTest(unittest.TestCase):

    def write_extract(self, value):
        tmp = tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False)
        self.addCleanup(pathlib.Path(tmp.name).unlink, missing_ok=True)
        json.dump(value, tmp)
        tmp.close()
        return pathlib.Path(tmp.name)

    def test_enumerates_every_nonempty_proof_link_once(self):
        path = self.write_extract({
            "schemaVersion": 2,
            "conjectures": [
                {"formalProofs": [
                    {"kind": "lean4", "link": "https://example.com/a",
                     "conditions": ["h"]},
                    {"kind": "lean4", "link": "", "conditions": []},
                ]},
                {"formalProofs": [
                    {"kind": "lean4", "link": "https://example.com/b",
                     "conditions": []},
                    {"kind": "lean4", "link": "https://example.com/a",
                     "conditions": []},
                ]},
            ],
        })
        self.assertEqual(
            links_from_extract(path),
            ["https://example.com/a", "https://example.com/b"])

    def test_rejects_legacy_extract_in_canonical_mode(self):
        path = self.write_extract({"conjectures": []})
        with self.assertRaisesRegex(ValueError, "schemaVersion 2"):
            links_from_extract(path)

    def test_rejects_missing_proof_list(self):
        path = self.write_extract({"schemaVersion": 2, "conjectures": [{}]})
        with self.assertRaisesRegex(ValueError, "formalProofs must be a list"):
            links_from_extract(path)

    def test_rejects_non_string_link(self):
        path = self.write_extract({
            "schemaVersion": 2,
            "conjectures": [{"formalProofs": [{"link": None}]}],
        })
        with self.assertRaisesRegex(ValueError, "link must be a string"):
            links_from_extract(path)

    def test_source_mode_deduplication_stays_stable(self):
        self.assertEqual(unique_links(["b", "", "a", "b"]), ["b", "a"])


if __name__ == "__main__":
    unittest.main()
