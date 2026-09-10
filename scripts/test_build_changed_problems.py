"""Test early PR builds against real Git diffs and a stub Lake executable."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import build_changed_problems as changed

SCRIPT = Path(changed.__file__).resolve()


class ChangedProblemsTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        self.write("FormalConjectures/Example.lean", "theorem old : True := by trivial\n")
        self.write("README.md", "Test\n")
        self.commit()
        self.base = self.git("rev-parse", "HEAD").strip()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(f"#!{sys.executable}\n"
                        "import json, os, pathlib, sys\n"
                        "pathlib.Path('lake-args.json').write_text(json.dumps(sys.argv[1:]))\n"
                        "raise SystemExit(int(os.environ.get('LAKE_EXIT', '0')))\n")
        lake.chmod(0o755)

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True,
                              capture_output=True, text=True).stdout

    def write(self, path, text="theorem test : True := by trivial\n"):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def commit(self):
        self.git("add", "FormalConjectures", "README.md")
        self.git("commit", "-m", "fixture")

    def run_check(self, base=None, lake_exit="0"):
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--base", base or self.base,
             "--summary", str(self.root / "summary.json")], cwd=self.root,
            env={**os.environ, "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                 "LAKE_EXIT": lake_exit}, capture_output=True, text=True,
        )

    def test_paths_are_passed_as_separate_arguments_without_name_parsing(self):
        paths = ["FormalConjectures/ErdosProblems/1014.lean",
                 "FormalConjectures/Arxiv/1.2 space 'quote'.lean",
                 "FormalConjectures/Examples/é.lean"]
        for path in paths:
            self.write(path)
        self.write("FormalConjectures/All.lean", "-- generated aggregate\n")
        self.write("FormalConjectures/notes.txt", "notes\n")
        self.commit()
        before = self.git("status", "--porcelain", "--untracked-files=no")
        head = self.git("rev-parse", "HEAD")
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads((self.root / "lake-args.json").read_text()),
                         ["--wfail", "build", *sorted(paths)])
        self.assertEqual(self.git("rev-parse", "HEAD"), head)
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), before)
        self.assertTrue((self.root / "summary.json").is_file())

    def test_deleted_files_are_excluded_and_renames_use_new_path(self):
        self.git("mv", "FormalConjectures/Example.lean", "FormalConjectures/New.lean")
        self.commit()
        self.assertEqual(self.run_check().returncode, 0)
        self.assertEqual(json.loads((self.root / "lake-args.json").read_text()),
                         ["--wfail", "build", "FormalConjectures/New.lean"])

    def test_merge_first_parent_excludes_changes_already_on_main(self):
        self.git("checkout", "-b", "topic")
        self.write("FormalConjectures/PR.lean")
        self.commit()
        self.git("checkout", "main")
        self.write("FormalConjectures/Base.lean")
        self.commit()
        self.git("merge", "--no-ff", "topic", "-m", "merge fixture")
        self.assertEqual(self.run_check(base="HEAD^1").returncode, 0)
        self.assertEqual(json.loads((self.root / "lake-args.json").read_text()),
                         ["--wfail", "build", "FormalConjectures/PR.lean"])

    def test_build_failure_is_not_swallowed(self):
        self.write("FormalConjectures/Example.lean", "invalid Lean\n")
        self.commit()
        self.assertEqual(self.run_check(lake_exit="7").returncode, 7)

    def test_empty_scope_and_missing_base_leave_full_build_enabled(self):
        for base in (self.base, "missing-revision"):
            with self.subTest(base=base):
                result = self.run_check(base=base)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("continuing to the full build", result.stdout)
                self.assertFalse((self.root / "lake-args.json").exists())

    def test_deleted_only_scope_does_not_call_lake(self):
        self.git("rm", "FormalConjectures/Example.lean")
        self.git("commit", "-m", "delete")
        self.assertEqual(self.run_check().returncode, 0)
        self.assertFalse((self.root / "lake-args.json").exists())

    def test_broad_change_uses_full_build_without_duplicate_preflight(self):
        for index in range(changed.MAX_FILES + 1):
            self.write(f"FormalConjectures/Example{index}.lean")
        self.commit()
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("early-check limit", result.stdout)
        self.assertFalse((self.root / "lake-args.json").exists())

    def test_workflow_keeps_preflight_before_full_validation(self):
        workflow = (SCRIPT.parent.parent / ".github/workflows/build-and-docs.yml").read_text()
        early = workflow.index("- name: Build changed problem files first")
        full = workflow.index("- name: Build ForMathlib, utilities, and test")
        problems = workflow.index("- name: Build problems")
        self.assertLess(early, full)
        self.assertLess(full, problems)
        self.assertIn("github.event_name == 'pull_request'", workflow[early:full])
        self.assertNotIn("continue-on-error", workflow[early:problems])


if __name__ == "__main__":
    unittest.main()
