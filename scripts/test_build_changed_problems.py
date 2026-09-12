"""Exercise scope selection with real Git merges and retained check diagnostics."""

import contextlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch

import build_changed_problems as changed
import check_category_warnings as categories

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
        self.git("add", ".")
        self.git("commit", "-m", "base")
        self.git("checkout", "-b", "topic")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(f"#!{sys.executable}\n" + textwrap.dedent('''\
            import json, os, pathlib, sys
            with open('calls.jsonl', 'a') as log:
                log.write(json.dumps(sys.argv[1:]) + '\\n')
            if sys.argv[1] == '--wfail':
                raise SystemExit(int(os.environ.get('BUILD_EXIT', '0')))
            if os.environ.get('EXTRACT_EXIT'):
                raise SystemExit(int(os.environ['EXTRACT_EXIT']))
            print(os.environ.get('EXTRACT_JSON', '{"problems": []}'))
            '''))
        lake.chmod(0o755)
        self.env = {**os.environ, "GITHUB_EVENT_NAME": "pull_request",
                    "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                    "GITHUB_OUTPUT": str(self.root / "output"),
                    "GITHUB_STEP_SUMMARY": str(self.root / "summary.md")}

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.root, check=True,
                              capture_output=True, text=True).stdout

    def write(self, path, text="theorem test : True := by trivial\n"):
        file = self.root / path
        file.parent.mkdir(parents=True, exist_ok=True)
        file.write_text(text)

    def merge(self, *paths):
        self.git("add", "--", *paths)
        self.git("commit", "-m", "topic")
        self.git("checkout", "main")
        self.git("merge", "--no-ff", "topic", "-m", "PR merge")

    def command(self, operation, **env):
        args = [sys.executable, str(SCRIPT), operation]
        if operation == "plan":
            args += ["--out", str(self.root / "scope.json")]
        else:
            args += ["--plan", str(self.root / "scope.json"), "--out", str(self.root / "diagnostics")]
        return subprocess.run(args, cwd=self.root, env={**self.env, **env}, capture_output=True, text=True)

    def plan(self, **env):
        result = self.command("plan", **env)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads((self.root / "scope.json").read_text())

    def test_problem_only_merge_checks_paths_and_metadata_without_full_extraction(self):
        paths = ["FormalConjectures/ErdosProblems/1014.lean",
                 "FormalConjectures/Arxiv/1.2 space 'quote'.lean"]
        for path in paths:
            self.write(path)
        self.merge(*paths)
        before = self.git("status", "--porcelain", "--untracked-files=no")
        self.assertEqual(self.plan()["files"], sorted(paths))
        result = self.command("check")
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = [json.loads(line) for line in (self.root / "calls.jsonl").read_text().splitlines()]
        self.assertEqual(calls[0], ["--wfail", "build", *sorted(paths)])
        self.assertEqual(calls[1:], [["exe", "extract_names", path, changed.EXCLUDES] for path in sorted(paths)])
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), before)
        self.assertIn("repository-wide tests wait", (self.root / "summary.md").read_text())
        self.assertFalse((self.root / "site/data/conjectures.json").exists())

    def test_shared_or_mixed_changes_force_full(self):
        self.write("FormalConjectures/Example.lean", "-- changed\n")
        self.write("README.md", "changed guidance\n")
        self.merge("FormalConjectures/Example.lean", "README.md")
        self.assertFalse(self.plan()["targeted"])
        self.assertNotEqual(self.command("check").returncode, 0)
        self.assertFalse((self.root / "calls.jsonl").exists())

    def test_renames_and_deletions_force_full(self):
        self.git("mv", "FormalConjectures/Example.lean", "FormalConjectures/Renamed.lean")
        self.merge("FormalConjectures")
        self.assertFalse(self.plan()["targeted"])

    def test_symlinks_force_full(self):
        file = self.root / "FormalConjectures/Example.lean"
        file.unlink()
        file.symlink_to("../README.md")
        self.merge("FormalConjectures")
        self.assertFalse(self.plan()["targeted"])

    def test_generated_aggregate_forces_full(self):
        self.write("FormalConjectures/All.lean", "-- aggregate\n")
        self.merge("FormalConjectures")
        self.assertFalse(self.plan()["targeted"])

    def test_broad_change_forces_full(self):
        for index in range(changed.MAX_FILES + 1):
            self.write(f"FormalConjectures/Example{index}.lean")
        self.merge("FormalConjectures")
        self.assertFalse(self.plan()["targeted"])

    def test_non_merge_checkout_and_non_pr_events_force_full(self):
        self.assertFalse(self.plan()["targeted"])
        self.write("FormalConjectures/New.lean")
        self.merge("FormalConjectures")
        for event in ("merge_group", "push", "workflow_dispatch", "pull_request_target", ""):
            self.assertFalse(self.plan(GITHUB_EVENT_NAME=event)["targeted"])

    def test_first_parent_excludes_updates_already_on_main(self):
        self.write("FormalConjectures/PR.lean")
        self.git("add", "FormalConjectures")
        self.git("commit", "-m", "PR")
        self.git("checkout", "main")
        self.write("README.md", "main update\n")
        self.git("add", "README.md")
        self.git("commit", "-m", "main update")
        self.git("merge", "--no-ff", "topic", "-m", "PR merge")
        self.assertEqual(self.plan()["files"], ["FormalConjectures/PR.lean"])

    def test_build_extraction_and_category_failures_are_not_swallowed(self):
        self.write("FormalConjectures/Example.lean", "-- changed\n")
        self.merge("FormalConjectures")
        self.plan()
        blocking = {"problems": [{"theorem": "example", "module": "FormalConjectures.Example",
                                  "category": "research open", "hasSorryFreeProof": True}]}
        for env, code in [({"BUILD_EXIT": "7"}, 7), ({"EXTRACT_EXIT": "9"}, 9),
                          ({"EXTRACT_JSON": "invalid JSON"}, 2),
                          ({"EXTRACT_JSON": json.dumps(blocking)}, 1)]:
            with self.subTest(env=env):
                self.assertEqual(self.command("check", **env).returncode, code)

    def test_tampered_scope_is_rejected(self):
        self.write("FormalConjectures/New.lean")
        self.merge("FormalConjectures")
        scope = self.plan()
        scope["files"] = []
        (self.root / "scope.json").write_text(json.dumps(scope))
        self.assertNotEqual(self.command("check").returncode, 0)
        self.assertFalse((self.root / "calls.jsonl").exists())

    def test_category_checker_combines_native_extracts(self):
        first = self.root / "first.json"
        second = self.root / "second.json"
        first.write_text(json.dumps({"problems": []}))
        second.write_text(json.dumps({"problems": [{"theorem": "bad", "module": "FormalConjectures.Second",
                                                    "category": "research open", "hasSorryFreeProof": True}]}))
        with contextlib.redirect_stdout(io.StringIO()), patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(self.root / "summary.md")}):
            self.assertEqual(categories.main([str(first), str(second)]), 1)


class WorkflowScopeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        default = SCRIPT.parent.parent / ".github/workflows/build-and-docs.yml"
        cls.workflow = Path(os.environ.get("FC_BUILD_WORKFLOW", default)).read_text()
        build = cls.workflow.split("  build:\n", 1)[1].split("  # Deployment job", 1)[0]
        cls.steps = dict(re.findall(r"^      - name: ([^\n]+)\n(.*?)(?=^      - name: |\Z)", build, re.M | re.S))

    def enabled(self, name, targeted, site="false", event="pull_request"):
        expr = re.search(r"^        if: (.+)$", self.steps[name], re.M)
        if expr is None:
            return True
        expression = expr[1]
        for key, value in {"steps.scope.outputs.targeted": targeted, "steps.mode.outputs.website_only": "false",
                           "steps.mode.outputs.site": site, "github.event_name": event}.items():
            expression = expression.replace(key, "'" + value + "'")
        self.assertNotRegex(expression, r"steps\.|github\.|always\(")
        result = subprocess.run(["bash", "-c", "[[ " + expression + " ]]"], capture_output=True)
        self.assertIn(result.returncode, (0, 1), result.stderr)
        return result.returncode == 0

    def test_targeted_pr_skips_full_corpus_steps(self):
        self.assertTrue(self.enabled("Validate changed problem files", "true"))
        for name in ("Generate All.lean", "Build ForMathlib, utilities, and test", "Build problems",
                     "Generate conjectures data for website", "Check category warnings", "Build literate source pages"):
            self.assertFalse(self.enabled(name, "true"), name)
        for name in self.steps:
            if "actions/cache/save@" in self.steps[name]:
                self.assertFalse(self.enabled(name, "true"), name)

    def test_full_queue_and_main_keep_validation_and_cache_policy(self):
        for event in ("merge_group", "push"):
            self.assertFalse(self.enabled("Validate changed problem files", "false", event=event))
            for name in ("Generate All.lean", "Build ForMathlib, utilities, and test", "Build problems",
                         "Generate conjectures data for website", "Check category warnings", "Build literate source pages"):
                self.assertTrue(self.enabled(name, "false", "true", event), name)
            cache = "Save Lean build" if "Save Lean build" in self.steps else "Save local lake build"
            self.assertEqual(self.enabled(cache, "false", "true", event), event == "push")

    def test_mode_disables_site_only_for_targeted_scope(self):
        mode = self.steps["Detect build mode"]
        match = re.search(r"        run: \|\n((?:          .*\n|\n)+)", mode)
        with tempfile.TemporaryDirectory() as temp:
            for targeted in ("true", "false"):
                out = Path(temp) / targeted
                env = {**os.environ, "TARGETED_PROBLEMS": targeted, "WEBSITE_ONLY": "false",
                       "GITHUB_OUTPUT": str(out), "EVENT_NAME": "pull_request", "REF_NAME": "pr",
                       "REUSED_SITE": ""}
                # Missing Git diff deliberately takes the existing full-site path.
                subprocess.run(["bash", "-eu", "-c", textwrap.dedent(match[1])], cwd=temp,
                               env=env, capture_output=True, check=True)
                self.assertIn("website_only=false", out.read_text())
                self.assertIn("site=" + ("false" if targeted == "true" else "true"), out.read_text())


if __name__ == "__main__":
    unittest.main()
