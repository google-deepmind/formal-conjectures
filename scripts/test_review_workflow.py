"""Offline boundary tests; these do not establish hosted Actions qualification."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

try:
    import review_workflow as workflow
    from conjectures import execution as w
except ModuleNotFoundError as error:
    if error.name not in ("review_report", "review_eval"):
        raise
    raise unittest.SkipTest(
        "Requires the shared toolkit checkout"
    ) from error


class WorkflowTests(unittest.TestCase):
    def test_authorization_uses_effective_permission_and_exact_command(self):
        event = {"action": "created", "comment": {"body": "/review"}, "issue": {"pull_request": {}}}
        workflow.authorize(event, "write")
        for permission in ("read", "triage", "none"):
            with self.assertRaises(ValueError):
                workflow.authorize(event, permission)
        event["comment"]["body"] = "/review\necho injected"
        with self.assertRaises(ValueError):
            workflow.authorize(event, "admin")


    def test_container_has_no_host_execution_or_credentials(self):
        args = w.container_args("ghcr.io/example/cache@sha256:" + "a" * 64, Path("/tmp/input"))
        for flag in ("--network=none", "--read-only", "--cap-drop=ALL", "--user=65534:65534"):
            self.assertIn(flag, args)
        self.assertNotIn("--privileged", args)
        self.assertNotIn("-e", args)
        self.assertIn(
            (
                "type=bind,src=/private/tmp/input,dst=/input,readonly"
                if Path("/tmp").resolve() != Path("/tmp")
                else "type=bind,src=/tmp/input,dst=/input,readonly"
            ),
            args,
        )
        with self.assertRaises(ValueError):
            w.container_args("ghcr.io/example/cache:latest", Path("/tmp/input"))

    def test_scope_rejects_project_configuration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p = root / "FormalConjectures/Fixture/12.lean"
            p.parent.mkdir(parents=True)
            p.write_text("")
            self.assertEqual(
                w.build_targets(["FormalConjectures/Fixture/12.lean"], root),
                ["«FormalConjectures».«Fixture».«12»"],
            )
            utility = root / "FormalConjectures/Util/ProblemImports.lean"
            utility.parent.mkdir(parents=True)
            utility.write_text("")
            for scope in (
                ["lakefile.toml"],
                ["FormalConjectures/deleted.lean"],
                ["FormalConjectures/Util/ProblemImports.lean"],
            ):
                with self.assertRaises(ValueError):
                    w.build_targets(scope, root)

    def test_timeout_is_an_execution_error(self):
        with patch.object(w.subprocess, "run", side_effect=w.subprocess.TimeoutExpired("docker", 70)):
            self.assertIsNone(w.execute("container", ["lake", "build"])["exit_code"])


if __name__ == "__main__":
    unittest.main()
