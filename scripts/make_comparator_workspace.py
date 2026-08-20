#!/usr/bin/env python3
"""Import one Formal Conjectures declaration and generate its workspace.

`leanprover/lean-eval` verifies a submission by building it against a Challenge
module whose statement the maintainers trust, under a config that pins the
permitted axioms. This command produces that shape for one Formal Conjectures
declaration, in the two steps `leanprover/lean-eval#536` separates:

    fc_leaneval_importer  FC declaration -> marked-up module + manifest
    leaneval_generator    marked-up module + manifest -> workspace

The first half is Formal Conjectures'. The second half is lean-eval's, and is
to be replaced by a pinned dependency on `leanprover/lean-eval-generator`; the
module standing in for it here is the code that gets deleted when that lands.
`comparator/OWNERSHIP.md` says exactly what goes and what stays. This file is
the wiring between them and belongs to neither.

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

The workspace's own build needs a network fetch of its pinned dependencies, so
this command does not attempt it; generation is offline and the build belongs
to the comparator run.
"""

import argparse
import pathlib
import shutil
import sys
import tempfile

import fc_leaneval_importer as importer
import leaneval_generator as generator
from leaneval_interface import slug

ROOT = importer.ROOT


def write_tree(target, files):
    """Write a complete directory without overwriting or leaving a partial one.

    Plumbing, and on neither side of the seam: the generator returns a
    path-to-content mapping and never touches the filesystem, so putting one
    on disk is the command's job whether the mapping is a workspace or the
    pair this repository hands over.
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


def emit_import(marked_up, manifest, out_dir):
    """Write only the pair this repository owns: the module and the manifest.

    This is the artifact the FC importer contributes to a lean-eval problem
    pull request once the generator is a pinned dependency there. Emitting it
    on its own keeps the seam checkable today: the bytes here are the bytes
    the generator gets, and nothing in this directory is workspace layout.
    """
    return write_tree(
        pathlib.Path(out_dir) / slug(manifest.id),
        {"Problem.lean": marked_up.render(), "manifest.json": manifest.to_json()},
    )


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
        help="write only the marked-up module and its manifest, the pair this "
        "repository hands the generator, and generate no workspace",
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
        print(emit_import(marked_up, manifest, args.emit_import))
        return 0
    files = generator.generate(marked_up, manifest)
    print(write_tree(pathlib.Path(args.out) / slug(manifest.id), files))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
