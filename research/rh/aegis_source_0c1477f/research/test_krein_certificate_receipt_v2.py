"""Regression tests for on-disk Krein metadata binding; no Arb/Lean claims."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import krein_certificate_receipt_v2 as receipt

HERE = Path(__file__).resolve().parent


class ReceiptRegressionTests(unittest.TestCase):
    def test_integral_float_spelling_has_one_hash(self):
        self.assertEqual(
            receipt.canonical_sha256({"bounds": [1000000, 8, 1]}),
            receipt.canonical_sha256({"bounds": [1000000.0, 8.0, 1.0]}),
        )

    def test_committed_receipts_validate_after_disk_roundtrip(self):
        for name in receipt.ANCHORS:
            with self.subTest(anchor=name):
                data = json.loads((HERE / f"KREIN_CERTIFICATE_RECEIPT_V2_{name}.json").read_text())
                try:
                    receipt.validate_receipt(data, name)
                except receipt.ReceiptError as exc:
                    self.fail(f"committed receipt rejected: {exc}")

    def test_default_cli_rejects_missing_receipt_instead_of_generating_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            script = Path(tmp) / "research/rh/krein_certificate_receipt_v2.py"
            script.parent.mkdir(parents=True)
            shutil.copy2(HERE / script.name, script)
            result = subprocess.run(
                [sys.executable, str(script), "L1.0"],
                capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(result.returncode, 0, "CLI silently regenerated a missing receipt")

class StrictInputTests(unittest.TestCase):
    def test_boolean_is_not_an_integer_hash(self):
        self.assertNotEqual(receipt.canonical_sha256({'x': True}),
                            receipt.canonical_sha256({'x': 1}))

    def test_nonintegral_values_are_not_rounded_to_integers(self):
        self.assertNotEqual(receipt.canonical_sha256({'x': 0.98}),
                            receipt.canonical_sha256({'x': 1}))

    def test_nonfinite_values_are_rejected(self):
        for value in (float('nan'), float('inf'), -float('inf')):
            with self.subTest(value=value), self.assertRaises(ValueError):
                receipt.canonical_sha256({'x': value})

    def test_string_is_not_a_number_hash(self):
        self.assertNotEqual(receipt.canonical_sha256({'x': '1'}),
                            receipt.canonical_sha256({'x': 1}))

    def test_recomputed_hash_does_not_allow_anchor_mutations(self):
        for name in receipt.ANCHORS:
            data = receipt.make_receipt(name)
            for section, field, value in (
                ('certificate', 'git_blob_sha', 'a' * 40),
                ('lp_candidate', 'generator_git_blob_sha', 'b' * 40),
                ('certificate', 'path', 'wrong/path.json'),
                ('parameters', 'L', True),
            ):
                with self.subTest(anchor=name, field=field):
                    bad = json.loads(json.dumps(data))
                    bad[section][field] = value
                    bad['binding_sha256'] = receipt.canonical_sha256(
                        {k: v for k, v in bad.items() if k != 'binding_sha256'})
                    with self.assertRaises(receipt.ReceiptError):
                        receipt.validate_receipt(bad, name)

    def test_all_six_falsifiers_use_a_valid_loaded_receipt(self):
        for name in receipt.ANCHORS:
            with self.subTest(anchor=name):
                result = receipt.run_falsifiers(name)
                self.assertEqual(len(result['results']), 6)
                self.assertEqual(set(result['results'].values()), {'PASS_REJECTED'})

    def test_cli_rejects_tampered_file_without_rewriting_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp) / 'research/rh'
            directory.mkdir(parents=True)
            script = directory / 'krein_certificate_receipt_v2.py'
            shutil.copy2(HERE / script.name, script)
            path = directory / 'KREIN_CERTIFICATE_RECEIPT_V2_L1.0.json'
            bad = receipt.make_receipt('L1.0')
            bad['authority_effect'] = 'WRITE'
            path.write_text(json.dumps(bad))
            before = path.read_bytes()
            for options in ([], ['--falsify']):
                with self.subTest(options=options):
                    result = subprocess.run([sys.executable, str(script), 'L1.0', *options],
                                            capture_output=True, text=True, check=False)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(path.read_bytes(), before)

    def test_cli_rejects_duplicate_keys_even_when_last_value_is_correct(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp) / 'research/rh'
            directory.mkdir(parents=True)
            script = directory / 'krein_certificate_receipt_v2.py'
            shutil.copy2(HERE / script.name, script)
            path = directory / 'KREIN_CERTIFICATE_RECEIPT_V2_L1.0.json'
            data = json.dumps(receipt.make_receipt('L1.0'))
            data = '{"authority_effect":"WRITE",' + data[1:]
            path.write_text(data)
            result = subprocess.run([sys.executable, str(script), 'L1.0'],
                                    capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('duplicate', result.stderr.lower())


class GitMembershipTests(unittest.TestCase):
    """Real temporary Git objects; these are fixtures, not Arb evidence."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Receipt test fixture")
        self.git("config", "user.email", "receipt-test@example.invalid")
        self.data = receipt.make_receipt("L1.0")
        refs = [
            (self.data["certificate"], "path", "git_blob_sha"),
            (self.data["lp_candidate"], "path", "git_blob_sha"),
            (self.data["lp_candidate"], "generator_path", "generator_git_blob_sha"),
            (self.data["verifier"], "path", "git_blob_sha"),
        ]
        for section, path_key, blob_key in refs:
            path = self.root / section[path_key]
            path.parent.mkdir(parents=True, exist_ok=True)
            if section is self.data["lp_candidate"] and path_key == "path":
                path.write_text(json.dumps(self.lp_payload()))
            else:
                path.write_text("synthetic receipt test fixture: " + path.name + "\n")
            section[blob_key] = self.git("hash-object", "-w", str(path))
        self.git("add", ".")
        self.git("-c", "commit.gpgsign=false", "commit", "-qm", "synthetic fixture")
        self.data["exact_head"] = self.git("rev-parse", "HEAD")

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args], text=True).strip()

    @staticmethod
    def lp_payload(**override):
        lp = {"L": 1.0, "w": 0.02, "uk": [1.02, 1.04], "coef": [0.0] * 7}
        lp.update(override)
        return lp

    def anchor_lp(self, **override):
        path = self.root / "lp_variant.json"
        path.write_text(json.dumps(self.lp_payload(**override)))
        self.data["lp_candidate"]["git_blob_sha"] = self.git("hash-object", "-w", str(path))

    def test_hat_support_outside_minus_L_L_passes(self):
        receipt.verify_hat_support(self.data, self.root)

    def test_hat_reaching_inside_minus_L_L_is_rejected(self):
        self.anchor_lp(uk=[1.019, 1.04])
        with self.assertRaisesRegex(receipt.ReceiptError, "hat support"):
            receipt.verify_hat_support(self.data, self.root)

    def test_coefficient_count_mismatch_is_rejected(self):
        self.anchor_lp(coef=[0.0] * 6)
        with self.assertRaisesRegex(receipt.ReceiptError, "coefficient"):
            receipt.verify_hat_support(self.data, self.root)

    def test_lp_L_must_equal_L_exact(self):
        self.anchor_lp(L=0.99, uk=[1.01, 1.03])
        with self.assertRaisesRegex(receipt.ReceiptError, "L_exact"):
            receipt.verify_hat_support(self.data, self.root)

    def test_non_json_lp_payload_is_rejected(self):
        path = self.root / "garbage.txt"
        path.write_text("not json")
        self.data["lp_candidate"]["git_blob_sha"] = self.git("hash-object", "-w", str(path))
        with self.assertRaises(receipt.ReceiptError):
            receipt.verify_hat_support(self.data, self.root)

    def verify(self, data=None):
        self.assertTrue(callable(getattr(receipt, "verify_git_bindings", None)),
                        "missing actual Git tree membership verification")
        receipt.verify_git_bindings(self.data if data is None else data, self.root)

    def test_real_git_membership_passes(self):
        self.verify()

    def test_blob_existing_elsewhere_is_not_enough(self):
        path = self.root / "elsewhere.txt"
        path.write_text("unrelated blob exists but is not the anchored LP")
        self.data["lp_candidate"]["git_blob_sha"] = self.git("hash-object", "-w", str(path))
        with self.assertRaises(receipt.ReceiptError):
            self.verify()

    def test_missing_head_is_rejected(self):
        self.data["exact_head"] = "0" * 40
        with self.assertRaises(receipt.ReceiptError):
            self.verify()

    def test_blob_cannot_impersonate_a_commit(self):
        self.data["exact_head"] = self.data["certificate"]["git_blob_sha"]
        with self.assertRaises(receipt.ReceiptError):
            self.verify()

    def test_wrong_path_is_rejected(self):
        self.data["certificate"]["path"] = "missing.json"
        with self.assertRaises(receipt.ReceiptError):
            self.verify()

    def test_git_replacement_objects_do_not_rebind_the_anchor(self):
        old_head = self.data["exact_head"]
        path = self.root / self.data["lp_candidate"]["path"]
        path.write_text("changed after anchored commit")
        self.git("add", ".")
        self.git("-c", "commit.gpgsign=false", "commit", "-qm", "later fixture")
        self.git("replace", old_head, self.git("rev-parse", "HEAD"))
        self.verify()

    def test_worktree_changes_do_not_override_committed_blob(self):
        path = self.root / self.data["lp_candidate"]["path"]
        path.write_text("uncommitted change")
        self.verify()

    @contextlib.contextmanager
    def cli_fixture(self):
        anchor = dict(receipt.ANCHORS["L1.0"])
        anchor["certificate_blob"] = self.data["certificate"]["git_blob_sha"]
        anchor["lp_blob"] = self.data["lp_candidate"]["git_blob_sha"]
        with mock.patch.dict(receipt.ANCHORS, {"L1.0": anchor}), mock.patch.multiple(
            receipt, HEAD=self.data["exact_head"],
            VERIFIER_BLOB=self.data["verifier"]["git_blob_sha"],
            LP_GENERATOR_BLOB=self.data["lp_candidate"]["generator_git_blob_sha"],
        ):
            path = self.root / "receipt.json"
            path.write_text(json.dumps(receipt.make_receipt("L1.0")))
            yield path

    def invoke_main(self, *options):
        output = io.StringIO()
        argv = ["receipt-validator", "L1.0", "--repo-root", str(self.root), *map(str, options)]
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(output):
            receipt.main()
        return json.loads(output.getvalue())

    def test_cli_validates_file_and_real_git_membership(self):
        with self.cli_fixture() as path:
            before = path.read_bytes()
            result = self.invoke_main("--receipt", path)
            self.assertEqual(result, json.loads(before))
            self.assertEqual(path.read_bytes(), before)

    def test_cli_falsifiers_validate_the_loaded_file(self):
        with self.cli_fixture() as path:
            result = self.invoke_main("--receipt", path, "--falsify")
            self.assertEqual(set(result["results"].values()), {"PASS_REJECTED"})

    def test_explicit_generation_roundtrips_through_validation(self):
        with self.cli_fixture() as path:
            path.unlink()
            generated = self.invoke_main("--generate", "--out", path)
            self.assertEqual(self.invoke_main("--receipt", path), generated)

    def test_cli_rejects_valid_metadata_when_git_head_is_missing(self):
        with self.cli_fixture() as path:
            data = receipt.load_receipt(path)
            with mock.patch.object(receipt, "HEAD", "0" * 40):
                data["exact_head"] = "0" * 40
                data["binding_sha256"] = receipt.canonical_sha256(
                    {k: v for k, v in data.items() if k != "binding_sha256"})
                path.write_text(json.dumps(data))
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                    self.invoke_main("--receipt", path)
                self.assertEqual(raised.exception.code, 1)

    def test_validation_cannot_overwrite_input_with_falsifier_report(self):
        with self.cli_fixture() as path:
            before = path.read_bytes()
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
                self.invoke_main("--receipt", path, "--falsify", "--out", path)
            self.assertEqual(raised.exception.code, 1)
            self.assertEqual(path.read_bytes(), before)

    def test_generate_and_falsify_cannot_be_combined(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            self.invoke_main("--generate", "--falsify")
        self.assertEqual(raised.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
