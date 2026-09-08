"""End-to-end export tests. Optional Comparator checks use only these trusted fixtures."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from export_problem import ROOT, export, response_files


def local_manifest(workspace):
    """Use the already-built, explicitly selected source checkout for local checks."""
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    manifest["packages"] = [
        {"name": p["name"], "type": "path", "inherited": True,
         "dir": str((ROOT / ".lake/packages" / p["name"]).resolve()),
         "configFile": p["configFile"], "manifestFile": p["manifestFile"]}
        for p in manifest["packages"]
    ] + [{"name": "formal_conjectures", "type": "path", "inherited": False,
          "dir": str(ROOT), "configFile": "lakefile.toml", "manifestFile": "lake-manifest.json"}]
    (workspace / "lake-manifest.json").write_text(json.dumps(manifest))


class ExportTests(unittest.TestCase):
    def test_response_rejects_path_escape(self):
        with self.assertRaisesRegex(ValueError, "Invalid workspace path"):
            response_files({"schemaVersion": 2, "files": [
                {"problemId": "fixture", "path": "../escape", "content": "", "sha256": ""}]}, "fixture")

    @unittest.skipUnless(os.environ.get("LEAN_EVAL_GENERATOR_CHECKOUT"), "Generator checkout required")
    def test_exports(self):
        generator = Path(os.environ["LEAN_EVAL_GENERATOR_CHECKOUT"])
        comparator = os.environ.get("COMPARATOR_BIN")
        cases = {
            "plain": ([], "decide"),
            "localDefinition": ([], "intro n; rfl"),
            "proposition": (["True"], "constructor <;> intro h <;> trivial"),
            "numerical": (["4"], "rfl"),
            "dependent": (["fun n => ⟨0, Nat.zero_lt_succ n⟩"], "intro n; exact Nat.zero_le n"),
            "twoAnswers": (["2", "2"], "rfl"),
            "polymorphic": ([], "intro α x; rfl"),
        }
        with tempfile.TemporaryDirectory() as temporary:
            for name, (answers, proof) in cases.items():
                with self.subTest(name=name):
                    artifact = Path(temporary) / name
                    workspace = export(ROOT / "FormalConjecturesTest/PackageExport.lean",
                                       f"PackageExportFixture.{name}", artifact, generator,
                                       "HEAD", str(ROOT))
                    exported = json.loads((artifact / "export.json").read_text())
                    self.assertEqual(len(exported["declarations"]), len(answers) + 1)
                    self.assertFalse((workspace / "ChallengeDeps.lean").exists())
                    self.assertIn("FormalConjecturesTest", (workspace / "Challenge.lean").read_text())
                    local_manifest(workspace)
                    submission = workspace / "Submission.lean"
                    original = submission.read_text()
                    if comparator and name == "plain":
                        self.check_comparator(workspace, False, "sorryAx")
                        # Importing the source theorem must not bypass the axiom check.
                        submission.write_text(original.replace("sorry", "exact PackageExportFixture.plain"))
                        self.check_comparator(workspace, False, "sorryAx")
                        submission.write_text(original)
                    filled = original
                    for answer in answers:
                        filled = filled.replace("sorry", f"exact {answer}", 1)
                    filled = filled.replace("sorry", proof, 1)
                    self.assertNotIn("sorry", filled)
                    submission.write_text(filled)
                    result = subprocess.run(["lake", "build", "Challenge", "Solution"], cwd=workspace,
                                            text=True, capture_output=True, timeout=600)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    if comparator:
                        self.check_comparator(workspace, True)
                    if comparator and name == "plain":
                        submission.write_text("import FormalConjecturesTest.PackageExport\n"
                                              "namespace Submission\ntheorem fc_problem : True := by trivial\n"
                                              "end Submission\n")
                        self.check_comparator(workspace, False)
                    print(f"PASS {name}: real metadata, package imports, filled Solution", flush=True)

    def check_comparator(self, workspace, accepted, diagnostic=None):
        result = subprocess.run(["lake", "test"], cwd=workspace, text=True,
                                capture_output=True, timeout=600)
        self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)
        if diagnostic:
            self.assertIn(diagnostic, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
