#!/usr/bin/env python3
"""Import one Formal Conjectures declaration and generate its workspace.

`leanprover/lean-eval` verifies a submission by building it against a Challenge
module whose statement the maintainers trust, under a config that pins the
permitted axioms. This command produces that shape for one Formal Conjectures
declaration, in the two steps `leanprover/lean-eval#536` separates:

    fc_leaneval_importer   FC declaration -> marked-up module + manifest
    lean-eval-generator    v1 request -> workspace file map

The first half is Formal Conjectures'. The second is the pinned
`leanprover/lean-eval-generator` binary — a deterministic Lean CLI with a
versioned JSON contract — run by `scripts/leaneval_generator_cli.py` at the
revision `comparator/tools.toml` pins. `scripts/leaneval_interface.py` builds
the request and checks the response. `comparator/OWNERSHIP.md` says exactly
what belongs to which side. This file is the wiring between them and belongs
to neither.

The marked-up module requires Mathlib and nothing else. lean-eval vendors its
problems, so a Challenge cannot fetch this repository at evaluation time, which
rules out importing the problem's own module. This repository's statements are
not authored self-contained, so the declarations a statement needs are copied
into the module's dependency region, dependencies first, each carrying the
`open`, `variable`, `universe`, `set_option` and `local notation` in force
where it was written.

Copying is a construction and it can be wrong in ways only Lean sees, so
`--verify` elaborates the marked-up module before you trust it.

`comparator/README.md` describes the workspace this produces and the pins it
carries; this file does not restate them.

Lean reports the type of each `answer(sorry)` slot. The importer refuses a case
when it cannot match the reported types to their source positions.

Usage:
  python make_comparator_workspace.py (ID | DECLARATION) [--out DIR]
      [--answer-type T] [--module FILE] [--verify]
  python make_comparator_workspace.py ID --emit-import DIR
  python make_comparator_workspace.py --validate

`--emit-import` writes the exact bytes that cross the seam — the v1 request,
with its context directory — and generates no workspace; running the pinned
binary on that request from inside the emitted directory yields the same file
map this command would have written.

The workspace's own build needs a network fetch of its pinned dependencies, so
this command does not attempt it; generation is offline apart from the
generator binary, and the build belongs to the comparator run.
"""

import argparse
import json
import pathlib
import shutil
import sys
import tempfile

import fc_leaneval_importer as importer
import leaneval_generator_cli as generator_cli
from leaneval_interface import build_problem, build_request, slug

ROOT = importer.ROOT

PROVENANCE_FILE = "fc-provenance.json"

# The request's context directory, relative to the request file, so an
# emitted seam artifact is self-contained and reproducible from any path.
CONTEXT_DIR = "context"


def write_tree(target, files):
    """Write a complete directory without overwriting or leaving a partial one.

    Plumbing, and on neither side of the seam: the generator returns a
    path-to-content mapping and never touches the filesystem, so putting one
    on disk is the command's job whether the mapping is a workspace or the
    request this repository hands over.
    """
    target = pathlib.Path(target)
    if target.exists():
        raise SystemExit(f"refusing to overwrite existing workspace: {target}")
    target.parent.mkdir(parents=True, exist_ok=True)
    staging = pathlib.Path(
        tempfile.mkdtemp(prefix=f".{target.name}.", dir=target.parent)
    )
    try:
        for relative, content in files.items():
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content, encoding="utf-8")
        staging.rename(target)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return target


def seam_files(pairs):
    """The request and context for `(marked_up, manifest)` pairs, as files.

    This is the artifact the FC importer contributes once lean-eval consumes
    the shared generator: the request bytes, the context directory the v1
    contract still reads, and one provenance record per problem — the FC
    source commit and declaration id §10 requires, which the v1 wire format
    has no field for, so they travel beside it rather than through it.
    """
    problems = [build_problem(marked_up, manifest) for marked_up, manifest in pairs]
    target = importer.target_pins()
    template = (
        importer.COMPARATOR_DIR / "templates" / "WorkspaceTest.lean"
    ).read_text(encoding="utf-8")
    request = build_request(
        [problem for problem, _ in problems], target, template, CONTEXT_DIR
    )
    files = {"request.json": json.dumps(request, indent=2, ensure_ascii=False) + "\n"}
    for (problem, ilean), (_, manifest) in zip(problems, pairs):
        module = problem["moduleName"]
        files[f"{CONTEXT_DIR}/{module}.lean"] = problem["moduleContent"]
        files[f"{CONTEXT_DIR}/.lake/build/lib/lean/{module}.ilean"] = (
            json.dumps({"version": 1, "module": module, "decls": ilean}) + "\n"
        )
        files[f"{PROVENANCE_FILE.removesuffix('.json')}-{problem['id']}.json"] = (
            manifest.to_json()
        )
    return request, files


def generate_workspaces(pairs, out_dir):
    """Generate one workspace per pair under `out_dir`, via the pinned binary."""
    request, files = seam_files(pairs)
    staging = pathlib.Path(tempfile.mkdtemp(prefix=".fc-seam."))
    try:
        for relative, content in files.items():
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content, encoding="utf-8")
        request["contextRoot"] = str(staging / CONTEXT_DIR)
        workspaces = generator_cli.generate(request)
    finally:
        shutil.rmtree(staging, ignore_errors=True)
    written = []
    for _, manifest in pairs:
        problem_id = slug(manifest.id)
        if problem_id not in workspaces:
            raise SystemExit(f"the generator returned no files for {problem_id}")
        workspace = dict(workspaces[problem_id])
        # The provenance sidecar rides in the workspace directory, not in the
        # generator's file map: the generator neither knows nor checks it.
        workspace[PROVENANCE_FILE] = manifest.to_json()
        written.append(write_tree(pathlib.Path(out_dir) / problem_id, workspace))
    return written


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "declaration",
        nargs="?",
        help="a problem id, or a declaration name such as erdos_940",
    )
    ap.add_argument("--out", default=str(ROOT / ".comparator"))
    ap.add_argument(
        "--answer-type",
        default=None,
        help="type of a non-Prop answer(sorry) slot; "
        "the problem file's `answer_type` is used when absent",
    )
    ap.add_argument(
        "--module",
        default=None,
        help="the file declaring it, when more than one does; "
        "overrides the problem file's `module`",
    )
    ap.add_argument(
        "--verify",
        action="store_true",
        help="elaborate the marked-up module against this checkout's Mathlib "
        "before accepting it",
    )
    ap.add_argument(
        "--emit-import",
        default=None,
        metavar="DIR",
        help="write only the v1 request and its context, the bytes this "
        "repository hands the pinned generator, and generate no workspace",
    )
    ap.add_argument(
        "--validate",
        action="store_true",
        help="check every problem file resolves, and import nothing",
    )
    args = ap.parse_args(argv)
    if args.validate:
        return importer.validate()
    if not args.declaration:
        ap.error("give a declaration, or --validate")
    marked_up, manifest = importer.import_problem(
        args.declaration, args.answer_type, args.module
    )
    if args.verify:
        importer.elaborate(marked_up)
    if args.emit_import:
        _, files = seam_files([(marked_up, manifest)])
        print(write_tree(pathlib.Path(args.emit_import) / slug(manifest.id), files))
        return 0
    for path in generate_workspaces([(marked_up, manifest)], args.out):
        print(path)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
