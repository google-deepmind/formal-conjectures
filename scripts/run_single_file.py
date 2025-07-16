#!/usr/bin/env python3
"""Run Codex inside Docker on a single file from the Formal Conjectures repo.

This helper mirrors ``run_in_container_single_file.sh`` but defaults to
``/opt/lean_pkgs/private_conjectures`` as the working repository and ensures
both this repository and ``private_mathlib4`` are built before Codex runs.
"""

import argparse
import os
import shlex
import subprocess
import sys


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Codex in Docker")
    parser.add_argument("--image", default="codex_patched", help="Docker image tag")
    parser.add_argument("--name", help="Container name (default: script-<pid>)")
    parser.add_argument("--prep", help="Prepare a single Lean file")
    parser.add_argument(
        "--export", action="append", default=[], help="Files to export from container"
    )
    parser.add_argument(
        "cmd", nargs=argparse.REMAINDER, help="Command run inside Codex"
    )
    args = parser.parse_args()
    if not args.cmd:
        parser.error("Need Codex command")
    return args


def docker(*args, check=True, capture_output=False, text=True):
    return subprocess.run(
        ["docker", *args], check=check, capture_output=capture_output, text=text
    )


def main() -> int:
    args = parse_args()
    repo = "/opt/lean_pkgs/private_conjectures"
    cname = args.name or f"pc-{os.getpid()}"
    dummy_key = "sk-0123456789abcdef0123456789abcdef0123456789ab"
    allowed_domains = [
        "huggingface.co",
        "cdn-lfs.huggingface.co",
        "cdn-lfs.hf.co",
        "generativelanguage.googleapis.com",
        "releases.lean-lang.org",
        "api.github.com",
        "github.com",
        "codeload.github.com",
        "raw.githubusercontent.com",
        "objects.githubusercontent.com",
    ]

    result = docker(
        "run",
        "-d",
        "--name",
        cname,
        "--cap-add=NET_ADMIN",
        "--cap-add=NET_RAW",
        "--security-opt",
        "seccomp=unconfined",
        "-e",
        "HOME=/home/node",
        "-e",
        f"OPENAI_API_KEY={dummy_key}",
        *(
            ["-e", f"GEMINI_API_KEY={os.environ['GEMINI_API_KEY']}"]
            if "GEMINI_API_KEY" in os.environ
            else []
        ),
        args.image,
        "sleep",
        "infinity",
        capture_output=True,
    )
    cid = result.stdout.strip()

    try:
        docker("exec", "--user", "root", cid, "chown", "-R", "1000:1000", repo)
        docker(
            "exec",
            "--user",
            "root",
            cid,
            "bash",
            "-c",
            "mkdir -p /etc/codex && "
            + "printf '%s\n' "
            + " ".join(allowed_domains)
            + " > /etc/codex/allowed_domains.txt && "
            + "chmod 444 /etc/codex/allowed_domains.txt && /usr/local/bin/init_firewall.sh",
        )

        if args.prep:
            docker(
                "exec",
                cid,
                "bash",
                "-euc",
                f"cd {repo} && "
                f"python3 -m scripts.prepare_single_file --lean {args.prep} --out tmp_prep --lean-explore-local && "
                f"cp tmp_prep/AGENTS_single_task.md AGENTS.md && "
                f"cp tmp_prep/$(basename {args.prep}) {args.prep}",
            )

        docker(
            "exec",
            "-it",
            cid,
            "bash",
            "-c",
            "cd /opt/lean_pkgs/private_mathlib4 && lake build FormalConjectures/WrittenOnTheWallII/GraphConjecture1.lean",
        )
        docker(
            "exec",
            "-it",
            cid,
            "bash",
            "-c",
            "cd /opt/lean_pkgs/private_conjectures && lake build FormalConjectures/WrittenOnTheWallII/GraphConjecture1.lean",
        )
        if args.prep:
            docker(
                "exec",
                "-it",
                cid,
                "bash",
                "-c",
                f"cd /opt/lean_pkgs/private_conjectures && lake build {args.prep}",
            )

        quoted = " ".join(shlex.quote(c) for c in args.cmd)
        docker(
            "exec",
            "-it",
            cid,
            "env",
            f"OPENAI_ALLOWED_DOMAINS={' '.join(allowed_domains)}",
            "env",
            "LAKE_PKGS_DISABLE_AUTO_UPDATE=1",
            *(
                ["env", f"GEMINI_API_KEY={os.environ['GEMINI_API_KEY']}"]
                if "GEMINI_API_KEY" in os.environ
                else []
            ),
            "bash",
            "-euo",
            "pipefail",
            "-c",
            f"cd {repo} && codex --provider=gemini --full-auto --model=gemini-2.5-pro {quoted}",
        )

        for path in args.export:
            host_dir = os.path.join(".", os.path.splitext(os.path.basename(path))[0])
            os.makedirs(host_dir, exist_ok=True)
            check = subprocess.run(
                ["docker", "exec", cid, "test", "-e", f"{repo}/{path}"]
            )
            if check.returncode == 0:
                docker("cp", f"{cid}:{repo}/{path}", host_dir + "/")
                print(f"\u2714 copied {path}")
            else:
                print(f"\u26a0 {path} not found in container")

    finally:
        subprocess.run(
            ["docker", "rm", "-f", cid],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

    return 0


if __name__ == "__main__":
    sys.exit(main())
