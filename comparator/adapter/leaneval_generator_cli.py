#!/usr/bin/env python3
"""Run the pinned `lean-eval-generator` binary on a schema-version-1 request.

`leanprover/lean-eval#536` extracts lean-eval's generator core into
`leanprover/lean-eval-generator`, a deterministic Lean CLI: one JSON request
on stdin, one JSON response on stdout, diagnostics on stderr. This module is
the plumbing that runs it and the context directory it expects; everything
the request and response mean lives in `comparator/adapter/leaneval_interface.py`, and
the pinned revision lives in `comparator/tools.toml` under `[generator]`.

The binary is found through `LEAN_EVAL_GENERATOR_BIN` or `PATH`. Building it
is cheap — the package depends on nothing — so CI clones the pinned revision
and runs `lake build`; `comparator/README.md` shows the same for a local run.

The context root exists because the schema-version-1 contract still resolves two things
from a benchmark checkout rather than from the request: the module source
(which must byte-match the request's `moduleContent`) and each declaration's
span from compiled `.ilean` metadata. This consumer is not a benchmark
checkout, so it materialises a minimal one: the rendered module at
`<root>/<Module>.lean`, and a synthesised `.ilean` carrying exactly the spans
`build_problem` computed. It can do that honestly because it rendered the
module; nothing is guessed.
"""

import json
import os
import pathlib
import shutil
import subprocess

from leaneval_interface import parse_response

BINARY_ENV = "LEAN_EVAL_GENERATOR_BIN"
BINARY_NAME = "lean-eval-generator"


def binary():
    """The pinned generator executable, from the environment or PATH."""
    named = os.environ.get(BINARY_ENV)
    if named:
        path = pathlib.Path(named)
        if not path.is_file():
            raise SystemExit(f"{BINARY_ENV}={named}: no such file")
        return str(path)
    found = shutil.which(BINARY_NAME)
    if found:
        return found
    raise SystemExit(
        f"no `{BINARY_NAME}` on PATH and {BINARY_ENV} is not set; build the "
        "revision pinned under [generator] in comparator/tools.toml and "
        "point either at it"
    )


def context_files(problems):
    """The minimal benchmark checkout for a request, as `{path: content}`.

    `problems` are `(problem, ilean_decls)` pairs from `build_problem`. Each
    module lands at `<Module>.lean` — the byte-match the generator enforces
    against `moduleContent` — and its spans at the `.ilean` path the
    generator reads. This is the one statement of that layout; whoever puts
    the files on disk decides where the root lives.
    """
    files = {}
    for problem, ilean in problems:
        module = problem["moduleName"]
        files[f"{module}.lean"] = problem["moduleContent"]
        files[f".lake/build/lib/lean/{module}.ilean"] = (
            json.dumps({"version": 1, "module": module, "decls": ilean}) + "\n"
        )
    return files


def generate(request):
    """The generator's verified file maps for one request.

    Returns `{problem_id: {path: content}}`.
    """
    proc = subprocess.run(
        [binary()],
        input=json.dumps(request),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise SystemExit(
            f"lean-eval-generator failed:\n{proc.stderr.strip() or proc.stdout.strip()}"
        )
    return parse_response(proc.stdout)
