"""End-to-end export tests. Optional Comparator checks use only these trusted fixtures."""

import json
import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest

from export_problem import ROOT, export, response_files


class ExportTests(unittest.TestCase):
    def test_response_rejects_path_escape(self):
        with self.assertRaisesRegex(ValueError, "Invalid workspace path"):
            response_files({"schemaVersion": 2, "files": [
                {"problemId": "fixture", "path": "../escape", "content": "", "sha256": ""}]}, "fixture")

    def test_source_output_cannot_corrupt_json(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "OutputFixture.lean"
            result = Path(directory) / "result.json"
            source.write_text('import FormalConjecturesTest.PackageExport\n'
                              '#eval IO.println "source diagnostic"\n'
                              'theorem output_fixture : True := by trivial\n')
            self.run_checked(["lake", "env", ".lake/build/bin/export_problem", str(source),
                              "OutputFixture", "output_fixture", "--output", str(result)], ROOT)
            self.assertEqual(json.loads(result.read_text())["declaration"], "output_fixture")

    @unittest.skipUnless(os.environ.get("COMPARATOR_BIN"), "Comparator required")
    def test_sandbox_denies_external_write(self):
        landrun = os.environ["COMPARATOR_LANDRUN"]
        self.assertNotIn("fake", landrun)
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "escape"
            result = subprocess.run([landrun, "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec",
                                     "--", "/bin/sh", "-c", 'echo escape > "$1"', "sh", str(marker)],
                                    text=True, capture_output=True, timeout=30)
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(marker.exists())
        # Comparator documents an AF_UNIX restriction for the supported Linux setup.
        import socket
        with self.assertRaises(OSError):
            socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)

    @unittest.skipUnless(os.environ.get("LEAN_EVAL_GENERATOR_CHECKOUT"), "Generator checkout required")
    def test_exports(self):
        generator = Path(os.environ["LEAN_EVAL_GENERATOR_CHECKOUT"])
        comparator = os.environ.get("COMPARATOR_BIN")
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        cases = {
            "plain": ([], "decide"),
            "privateDefinition": ([], "decide"),
            "implicitUniverse": ([], "intro α x; rfl"),
            "proofInType": ([], "rfl"),
            "localDefinition": ([], "intro n; rfl"),
            "proposition": (["True"], "constructor <;> intro h <;> trivial"),
            "numerical": (["4"], "rfl"),
            "dependent": (["fun n => ⟨0, Nat.zero_lt_succ n⟩"], "intro n; exact Nat.zero_le n"),
            "twoAnswers": (["2", "2"], "rfl"),
            "polymorphic": ([], "intro α x; rfl"),
        }
        with tempfile.TemporaryDirectory() as temporary:
            working = Path(temporary) / "working"
            working.mkdir()
            for name, (answers, proof) in cases.items():
                with self.subTest(name=name):
                    artifact = Path(temporary) / name
                    workspace = export(ROOT / "FormalConjecturesTest/PackageExport.lean",
                                       f"PackageExportFixture.{name}", artifact, generator,
                                       revision, os.environ.get("FC_SOURCE_REPOSITORY", str(ROOT)))
                    exported = json.loads((artifact / "export.json").read_text())
                    self.assertEqual(len(exported["declarations"]), len(answers) + 1)
                    self.assertFalse((workspace / "ChallengeDeps.lean").exists())
                    self.assertIn("FormalConjecturesTest", (workspace / "Challenge.lean").read_text())
                    for path in workspace.rglob("*"):
                        if path.is_file():
                            target = working / path.relative_to(workspace)
                            target.parent.mkdir(parents=True, exist_ok=True)
                            shutil.copy2(path, target)
                    workspace = working
                    if name == "plain":
                        # Resolve the exact Git requirements in a fresh workspace.
                        # Reuse this workspace across cases, without editing Lake's manifest.
                        self.run_checked(["lake", "update"], workspace)
                        self.run_checked(["lake", "exe", "cache", "get"], workspace)
                        self.assert_package_pins(workspace, artifact)

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
                    if comparator:
                        # The verifier must build the submitted source inside its sandbox.
                        self.check_comparator(workspace, True)
                    else:
                        self.run_checked(["lake", "build", "Challenge", "Solution"], workspace)
                    if comparator and name == "plain":
                        submission.write_text("import FormalConjecturesTest.PackageExport\n"
                                              "namespace Submission\ntheorem fc_problem : True := by trivial\n"
                                              "end Submission\n")
                        self.check_comparator(workspace, False)
                    print(f"PASS {name}: structured signatures, package imports, filled Solution", flush=True)

    def run_checked(self, command, workspace):
        result = subprocess.run(command, cwd=workspace, text=True, capture_output=True, timeout=1200)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_package_pins(self, workspace, artifact):
        request = json.loads((artifact / "request.json").read_text())
        manifest = json.loads((workspace / "lake-manifest.json").read_text())
        actual = {p["name"]: p for p in manifest["packages"]}
        for dependency in request["dependencies"]:
            package = actual[dependency["name"]]
            self.assertEqual(package["type"], "git")
            self.assertEqual(package["rev"], dependency["rev"])
            self.assertEqual(package["url"], dependency["git"])

    def check_comparator(self, workspace, accepted, diagnostic=None):
        with tempfile.TemporaryDirectory() as temporary:
            output=Path(temporary)/'result.json'
            result = subprocess.run(['lake','env',os.environ['COMPARATOR_BIN'],'config.json','--result-json',str(output)],
                                    cwd=workspace,text=True,capture_output=True,timeout=600)
            self.assertTrue(output.is_file(), 'Comparator did not retain a typed result: '+result.stderr)
            value=json.loads(output.read_text())
            if os.environ.get('COMPARATOR_RESULTS_DIR'):
                import uuid
                retained=Path(os.environ['COMPARATOR_RESULTS_DIR']);retained.mkdir(parents=True,exist_ok=True)
                (retained/(uuid.uuid4().hex+'.json')).write_text(json.dumps({'expected':'pass' if accepted else 'rejected','result':value,'exit_code':result.returncode}))
            self.assertEqual(value['schemaVersion'],1)
            self.assertEqual(value['outcome'],'pass' if accepted else 'rejected',value)
            if accepted:
                self.assertEqual(result.returncode,0);self.assertEqual(value['stage'],'complete')
            if diagnostic:self.assertEqual(value['reason'],'disallowed_axiom',value)


if __name__ == "__main__":
    unittest.main()
