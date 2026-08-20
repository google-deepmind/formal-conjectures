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

"""Tests for the command that runs the importer and then the generator.

The case that matters here is the seam itself: what this repository hands over
has to be enough. If a workspace cannot be rebuilt from the emitted module and
manifest alone, then some of the interface is still travelling inside the
process, and a pinned `lean-eval-generator` could not be dropped in.
"""

import pathlib
import tempfile
import unittest
from unittest import mock

import leaneval_generator as generator
from leaneval_interface import MarkedUpModule, ProblemManifest
from make_comparator_workspace import emit_import, write_tree
from test_leaneval_interface import a_target, A_MODULE, a_manifest


class EmitImportTest(unittest.TestCase):
    def test_only_the_module_and_the_manifest_are_emitted(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = emit_import(A_MODULE, a_manifest(), tmp)
            self.assertEqual(
                sorted(p.name for p in out.iterdir()),
                ["Problem.lean", "manifest.json"],
            )

    def test_the_emitted_pair_rebuilds_the_workspace_exactly(self):
        manifest = a_manifest()
        with tempfile.TemporaryDirectory() as tmp:
            out = emit_import(A_MODULE, manifest, tmp)
            module = MarkedUpModule.parse(
                (out / "Problem.lean").read_text(encoding="utf-8")
            )
            read_back = ProblemManifest.from_json(
                (out / "manifest.json").read_text(encoding="utf-8")
            )
        self.assertEqual(
            generator.generate(module, read_back, a_target()),
            generator.generate(A_MODULE, manifest, a_target()),
        )

    def test_an_existing_directory_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            emit_import(A_MODULE, a_manifest(), tmp)
            with self.assertRaisesRegex(SystemExit, "refusing to overwrite"):
                emit_import(A_MODULE, a_manifest(), tmp)

    def test_the_emitted_directory_is_named_by_the_problem_id(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = emit_import(
                A_MODULE, a_manifest(id="erdos_940.variants.large_integers"), tmp
            )
            self.assertEqual(
                out, pathlib.Path(tmp) / "erdos_940_variants_large_integers"
            )


class WriteTreeTest(unittest.TestCase):
    def test_existing_directory_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp) / "workspace"
            target.mkdir()
            sentinel = target / "keep.txt"
            sentinel.write_text("keep", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "refusing to overwrite"):
                write_tree(target, {"Challenge.lean": "theorem t : True"})
            self.assertEqual(sentinel.read_text(encoding="utf-8"), "keep")

    def test_failed_write_leaves_no_partial_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            target = root / "workspace"
            with mock.patch.object(
                pathlib.Path, "write_text", side_effect=OSError("disk error")
            ):
                with self.assertRaisesRegex(OSError, "disk error"):
                    write_tree(target, {"Challenge.lean": "theorem t : True"})
            self.assertFalse(target.exists())
            self.assertEqual(list(root.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
