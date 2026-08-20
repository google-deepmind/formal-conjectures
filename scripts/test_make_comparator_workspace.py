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
has to be enough. If a workspace cannot be generated from the emitted request
and context directory alone, then some of the interface is still travelling
inside the process, and the pinned `lean-eval-generator` binary could not
reproduce this command's output.
"""

import json
import os
import pathlib
import shutil
import tempfile
import unittest
from unittest import mock

import leaneval_generator_cli as generator_cli
from make_comparator_workspace import (
    CONTEXT_DIR,
    generate_workspaces,
    seam_files,
    write_tree,
)
from test_leaneval_interface import A_MODULE, a_manifest


class SeamFilesTest(unittest.TestCase):
    def test_the_emitted_files_are_the_request_its_context_and_provenance(self):
        _, files = seam_files([(A_MODULE, a_manifest())])
        self.assertEqual(
            sorted(files),
            [
                f"{CONTEXT_DIR}/.lake/build/lib/lean/erdos_940.ilean",
                f"{CONTEXT_DIR}/erdos_940.lean",
                "fc-provenance-erdos_940.json",
                "request.json",
            ],
        )

    def test_the_request_names_a_relative_context_root(self):
        # The emitted artifact must be reproducible from any path, so the
        # request cannot bake in where this machine staged it.
        request, _ = seam_files([(A_MODULE, a_manifest())])
        self.assertEqual(request["contextRoot"], CONTEXT_DIR)

    def test_the_context_module_is_the_request_module_byte_for_byte(self):
        # The generator refuses a request whose `moduleContent` differs from
        # the file at the context root; emitting both from one value is what
        # makes that check pass by construction.
        request, files = seam_files([(A_MODULE, a_manifest())])
        self.assertEqual(
            files[f"{CONTEXT_DIR}/erdos_940.lean"],
            request["problems"][0]["moduleContent"],
        )

    def test_the_ilean_carries_every_declaration(self):
        _, files = seam_files([(A_MODULE, a_manifest())])
        decls = json.loads(
            files[f"{CONTEXT_DIR}/.lake/build/lib/lean/erdos_940.ilean"]
        )["decls"]
        self.assertEqual(
            sorted(decls),
            ["Foo.bar", "erdos_940", "erdos_940_answer"],
        )

    def test_the_provenance_sidecar_is_the_manifest(self):
        # The v1 wire format has no provenance fields, so the FC source
        # commit and declaration id §10 requires travel beside the request.
        _, files = seam_files([(A_MODULE, a_manifest())])
        payload = json.loads(files["fc-provenance-erdos_940.json"])
        self.assertEqual(payload["source"]["commit"], "a" * 40)
        self.assertEqual(payload["source"]["declaration"], "erdos_940")

    def test_two_problems_with_one_id_are_refused(self):
        with self.assertRaisesRegex(SystemExit, "duplicate workspace id"):
            seam_files([(A_MODULE, a_manifest()), (A_MODULE, a_manifest())])


class WriteTreeTest(unittest.TestCase):
    def test_existing_directory_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp) / "ws"
            target.mkdir()
            with self.assertRaisesRegex(SystemExit, "refusing to overwrite"):
                write_tree(target, {"a.txt": "a"})

    def test_failed_write_leaves_no_partial_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = pathlib.Path(tmp) / "ws"
            files = {"a.txt": "a", "b.txt": None}  # None: write_text raises
            with self.assertRaises(Exception):
                write_tree(target, files)
            self.assertFalse(target.exists())
            self.assertEqual(list(pathlib.Path(tmp).iterdir()), [])


@unittest.skipUnless(
    os.environ.get(generator_cli.BINARY_ENV) or shutil.which(generator_cli.BINARY_NAME),
    "pinned lean-eval-generator binary not available",
)
class PinnedGeneratorTest(unittest.TestCase):
    """End to end against the real pinned binary, when one is built.

    CI builds the revision `comparator/tools.toml` pins and exports
    `LEAN_EVAL_GENERATOR_BIN`; locally the test is skipped unless you have
    done the same.
    """

    EXPECTED_FILES = [
        "Challenge.lean",
        "ChallengeDeps.lean",
        "README.md",
        "Solution.lean",
        "Submission.lean",
        "Submission/Helpers.lean",
        "WorkspaceTest.lean",
        "config.json",
        "fc-provenance.json",
        "holes.json",
        "lakefile.toml",
        "lean-toolchain",
    ]

    def test_a_workspace_generates_and_the_seam_reproduces_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = pathlib.Path(tmp) / "out"
            (workspace,) = generate_workspaces([(A_MODULE, a_manifest())], out)
            written = sorted(
                str(p.relative_to(workspace))
                for p in workspace.rglob("*")
                if p.is_file()
            )
            self.assertEqual(written, self.EXPECTED_FILES)
            # The definition hole reaches the config, and the delegation is
            # reducible in the Solution.
            config = json.loads((workspace / "config.json").read_text())
            self.assertEqual(config["definition_names"], ["erdos_940_answer"])
            self.assertIn(
                "@[reducible] noncomputable def erdos_940_answer",
                (workspace / "Solution.lean").read_text(),
            )

    def test_the_emitted_request_yields_identical_digests(self):
        # The seam is real only if the emitted bytes regenerate the same
        # workspace: run the binary on the emitted request, from inside the
        # emitted directory, and compare content digests per file.
        request, files = seam_files([(A_MODULE, a_manifest())])
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            for relative, content in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
            cwd = os.getcwd()
            try:
                os.chdir(root)
                first = generator_cli.generate(request)
                second = generator_cli.generate(request)
            finally:
                os.chdir(cwd)
            self.assertEqual(first, second)
            self.assertEqual(sorted(first), ["erdos_940"])



class SubsetTest(unittest.TestCase):
    def test_the_open_set_lists_one_hundred_declarations(self):
        from make_comparator_workspace import subset_declarations

        names = subset_declarations("FC100OpenSet1")
        self.assertEqual(len(names), 100)
        self.assertIn("OeisA308734.conjecture", names)
        self.assertIn("Erdos125.erdos_125.variants.positive_unequal_density", names)

    def test_a_missing_subset_is_refused(self):
        from make_comparator_workspace import subset_declarations

        with self.assertRaises(SystemExit):
            subset_declarations("NoSuchSet")


class KnownFailuresTest(unittest.TestCase):
    def _load(self, text):
        from make_comparator_workspace import load_known_failures

        with tempfile.NamedTemporaryFile("w", suffix=".toml", delete=False) as f:
            f.write(text)
            name = f.name
        try:
            return load_known_failures(name)
        finally:
            os.unlink(name)

    def test_entries_are_keyed_by_declaration(self):
        failures = self._load(
            '[[failure]]\ndeclaration = "A.b"\nstage = "source"\nreason = "x"\n'
        )
        self.assertEqual(failures["A.b"]["stage"], "source")

    def test_an_unknown_stage_is_refused(self):
        with self.assertRaises(SystemExit):
            self._load(
                '[[failure]]\ndeclaration = "A.b"\nstage = "later"\nreason = "x"\n'
            )

    def test_a_missing_field_is_refused(self):
        with self.assertRaises(SystemExit):
            self._load('[[failure]]\ndeclaration = "A.b"\nstage = "source"\n')


if __name__ == "__main__":
    unittest.main()
