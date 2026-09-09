"""Credential-free isolated candidate execution."""
import re
import resource
import subprocess
import tempfile
import time
from pathlib import Path
from . import report as rr

def run(*args, **kwargs):
    return subprocess.run(args, check=True, capture_output=True, timeout=120, **kwargs).stdout

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(rr.encode(value))

def container_args(image, snapshot):
    rr.require(
        re.fullmatch(r"(?:[^\s]+@)?sha256:[0-9a-f]{64}", image) is not None,
        "review image must be pinned by registry digest",
    )
    return [
        "docker",
        "run",
        "--rm",
        "-d",
        "--network=none",
        "--read-only",
        "--cap-drop=ALL",
        "--security-opt=no-new-privileges",
        "--pids-limit=256",
        "--memory=6g",
        "--cpus=2",
        "--user=65534:65534",
        "--tmpfs=/tmp:rw,nosuid,size=4g,mode=1777",
        "--mount",
        f"type=bind,src={snapshot.resolve()},dst=/input,readonly",
        "--workdir=/tmp",
        image,
        "sleep",
        "infinity",
    ]


def isolated(image, snapshot):
    container = run(*container_args(image, snapshot)).decode().strip()
    try:
        # The configured image owns the trusted dependency cache and toolchain.
        run(
            "docker",
            "exec",
            container,
            "sh",
            "-c",
            "set -eu; mkdir /tmp/work; cp -R /input/. /tmp/work/; "
            "mkdir /tmp/work/.lake; "
            "ln -s /opt/review-cache/.lake/packages /tmp/work/.lake/packages; "
            "cp -R /opt/review-cache/.lake/build /tmp/work/.lake/build",
        )
        return container
    except BaseException:
        run("docker", "rm", "-f", container)
        raise


def execute(container, command, seconds=60):
    started = time.monotonic()
    try:
        # Bound retained output even when a command floods stdout. The limit applies
        # to the Docker client; the in-container timeout still stops the command.
        with tempfile.TemporaryFile() as output:

            def limit_output():
                resource.setrlimit(resource.RLIMIT_FSIZE, (1024 * 1024, 1024 * 1024))

            proc = subprocess.run(
                [
                    "docker",
                    "exec",
                    "-w",
                    "/tmp/work",
                    container,
                    "timeout",
                    "-k",
                    "2",
                    str(seconds),
                    *command,
                ],
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=seconds + 10,
                check=False,
                preexec_fn=limit_output,
            )
            output.seek(0)
            text = output.read(48000).decode(errors="replace")
        return {
            "command": command,
            "exit_code": proc.returncode,
            "output": text,
            "wall_seconds": round(time.monotonic() - started, 3),
        }
    except subprocess.TimeoutExpired:
        return {
            "command": command,
            "exit_code": None,
            "output": "Controller timeout",
            "wall_seconds": round(time.monotonic() - started, 3),
        }


def build_targets(scope, snapshot):
    # Utility/config/dependency changes need a broader policy; fail closed in this pilot.
    rr.require(
        all(
            p.startswith("FormalConjectures/")
            and not p.startswith(("FormalConjectures/Util/", "FormalConjectures/Subsets/"))
            and p.endswith(".lean")
            and (snapshot / p).is_file()
            for p in scope
        ),
        "automated review supports one to five new or modified problem modules only",
    )
    rr.require(0 < len(scope) <= 5, "pilot scope limit is five modules")
    rr.require(all("»" not in p and "\n" not in p for p in scope), "unsupported module path")
    return [".".join("«" + part + "»" for part in Path(p).with_suffix("").parts) for p in scope]
