#!/usr/bin/env python3
"""Import one Formal Conjectures declaration and generate its workspace.

`leanprover/lean-eval` verifies a submission by building it against a Challenge
module whose statement the maintainers trust, under a config that pins the
permitted axioms. This command produces that shape for one Formal Conjectures
declaration, in the two steps `leanprover/lean-eval#536` separates:

    fc_leaneval_importer   FC declaration -> marked-up module + manifest
    lean-eval-generator    schema-version-1 request -> workspace file map

The first half is Formal Conjectures'. The second is the pinned
`leanprover/lean-eval-generator` binary — a deterministic Lean CLI with a
versioned JSON contract — run by `comparator/adapter/leaneval_generator_cli.py` at the
revision `comparator/tools.toml` pins. `comparator/adapter/leaneval_interface.py` builds
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
  python make_comparator_workspace.py --set NAME [--out DIR] [--verify]
      [--report FILE] [--known-failures FILE]
  python make_comparator_workspace.py --validate

`--set` imports every declaration of a `FormalConjectures/Subsets` list,
builds one request for all of them, and writes a per-declaration report.
With `--known-failures`, the run fails unless the failures are exactly the
recorded ones: an unexpected failure and a silently fixed one both count,
because a gate that only ever passes proves nothing.

`--emit-import` writes the exact bytes that cross the seam — the schema-version-1 request,
with its context directory — and generates no workspace; running the pinned
binary on that request from inside the emitted directory yields the same file
map this command would have written.

The workspace's own build needs a network fetch of its pinned dependencies, so
this command does not attempt it; generation is offline apart from the
generator binary, and the build belongs to the comparator run.
"""

import argparse
import pathlib
import re
import shutil
import sys
import tempfile
import tomllib

import fc_leaneval_importer as importer
import leaneval_generator_cli as generator_cli
from leaneval_interface import build_problem, build_request, dump_json, sha256_text, slug

ROOT = importer.ROOT

PROVENANCE_STEM = "fc-provenance"
PROVENANCE_FILE = f"{PROVENANCE_STEM}.json"

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


def seam_files(pairs, group=None):
    """The request and context for `(marked_up, manifest)` pairs, as files.

    This is the artifact the FC importer contributes once lean-eval consumes
    the shared generator: the request bytes, the context directory the schema-version-1
    contract still reads, and one provenance record per problem — the FC
    source commit and declaration id §10 requires, which the schema-version-1 wire format
    has no field for, so they travel beside it rather than through it.
    """
    problems = [
        build_problem(marked_up, manifest, group=group)
        for marked_up, manifest in pairs
    ]
    target = importer.target_pins()
    template = (
        importer.COMPARATOR_DIR / "templates" / "WorkspaceTest.lean"
    ).read_text(encoding="utf-8")
    request = build_request(
        [problem for problem, _ in problems], target, template, CONTEXT_DIR
    )
    files = {"request.json": dump_json(request)}
    for path, content in generator_cli.context_files(problems).items():
        files[f"{CONTEXT_DIR}/{path}"] = content
    for (problem, _), (_, manifest) in zip(problems, pairs):
        # Before generation the record binds the module bytes only; the
        # workspace's copy adds the generated files.
        bound = manifest.with_digests(sha256_text(problem["moduleContent"]), {})
        files[f"{PROVENANCE_STEM}-{problem['id']}.json"] = bound.to_json()
    return request, files


def generate_workspaces(pairs, out_dir, group=None):
    """Generate one workspace per pair under `out_dir`, via the pinned binary."""
    request, files = seam_files(pairs, group=group)
    staging = pathlib.Path(tempfile.mkdtemp(prefix=".fc-seam."))
    try:
        # Only the context crosses to the binary; the request goes on stdin
        # and the provenance sidecars are for the written workspaces.
        for relative, content in files.items():
            if not relative.startswith(f"{CONTEXT_DIR}/"):
                continue
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content, encoding="utf-8")
        request["contextRoot"] = str(staging / CONTEXT_DIR)
        workspaces = generator_cli.generate(request)
    finally:
        shutil.rmtree(staging, ignore_errors=True)
    module_content = {p["id"]: p["moduleContent"] for p in request["problems"]}
    written = []
    for _, manifest in pairs:
        problem_id = slug(manifest.id)
        if problem_id not in workspaces:
            raise SystemExit(f"the generator returned no files for {problem_id}")
        workspace = dict(workspaces[problem_id])
        # The provenance sidecar rides in the workspace directory, not in the
        # generator's file map: the generator neither knows nor checks it. It
        # binds the exact module bytes sent and every file received.
        bound = manifest.with_digests(
            sha256_text(module_content[problem_id]),
            {path: sha256_text(content) for path, content in workspace.items()},
        )
        workspace[PROVENANCE_FILE] = bound.to_json()
        written.append(write_tree(pathlib.Path(out_dir) / problem_id, workspace))
    return written


def subset_declarations(set_name):
    """The declaration list of a `FormalConjectures/Subsets` module.

    The subset files hold one `decl_name% <qualified name>` per line; the
    `decl_name%` elaborator is what guarantees each name resolves, so the
    text layer can read the list without re-proving that.
    """
    path = ROOT / "FormalConjectures" / "Subsets" / f"{set_name}.lean"
    if not path.is_file():
        raise SystemExit(f"no subset module at {path}")
    names = re.findall(
        r"decl_name%\s+([\w.«»]+)", path.read_text(encoding="utf-8")
    )
    if not names:
        raise SystemExit(f"{path} lists no decl_name% entries")
    return names


def load_known_failures(path):
    """The recorded failures, `{declaration: {stage, reason}}`."""
    with open(path, "rb") as handle:
        data = tomllib.load(handle)
    failures = {}
    for entry in data.get("failure", []):
        for field in ("declaration", "stage", "reason"):
            if field not in entry:
                raise SystemExit(f"{path}: a failure entry has no `{field}`")
        if entry["stage"] not in ("source", "target"):
            raise SystemExit(
                f"{path}: {entry['declaration']} has stage {entry['stage']!r}; "
                "expected source or target"
            )
        failures[entry["declaration"]] = entry
    return failures


def import_set(set_name, out_dir, verify=False, known_failures=None):
    """Import a whole subset, generate what imports, and report the rest.

    Returns the report object. Source-side failures — the importer refusing,
    or `--verify` elaboration failing — are recorded per declaration rather
    than aborting the run, because the whole-set result is the artifact:
    lean-eval#536 gates the FC import on this audit being reproducible.
    """
    declarations = subset_declarations(set_name)
    pairs, results = [], []
    for declaration in declarations:
        try:
            marked_up, manifest = importer.import_problem(declaration)
            if verify:
                importer.elaborate(marked_up)
        except SystemExit as failure:
            results.append(
                {
                    "declaration": declaration,
                    "status": "source-failed",
                    "reason": str(failure),
                }
            )
            continue
        pairs.append((marked_up, manifest))
        results.append(
            {
                "declaration": declaration,
                "id": slug(manifest.id),
                "category": manifest.category,
                "status": "imported",
            }
        )
    # The set decides the tab: a frozen list stays advertised whole, with
    # solved members marked by their category tag, so every member goes to
    # the open-conjectures group (google-deepmind/formal-conjectures#5075).
    written = (
        generate_workspaces(pairs, out_dir, group="open-conjectures")
        if pairs
        else []
    )
    categories = {}
    for entry in results:
        if entry["status"] == "imported":
            categories[entry["category"]] = categories.get(entry["category"], 0) + 1
    report = {
        "set": set_name,
        "total": len(declarations),
        "imported": len(pairs),
        "source_failed": len(declarations) - len(pairs),
        "categories": dict(sorted(categories.items())),
        "workspaces": [str(path) for path in written],
        "declarations": results,
    }
    if known_failures is not None:
        expected = {
            name
            for name, entry in known_failures.items()
            if entry["stage"] == "source"
        }
        actual = {
            entry["declaration"]
            for entry in results
            if entry["status"] == "source-failed"
        }
        unexpected = sorted(actual - expected)
        fixed = sorted(expected - actual)
        if unexpected or fixed:
            for name in unexpected:
                print(f"unexpected source failure: {name}", file=sys.stderr)
            for name in fixed:
                print(
                    f"{name} is recorded as a known source failure but "
                    "imported; remove it from the record",
                    file=sys.stderr,
                )
            report["known_failures_match"] = False
        else:
            report["known_failures_match"] = True
    return report


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
        help="write only the schema-version-1 request and its context, the bytes this "
        "repository hands the pinned generator, and generate no workspace",
    )
    ap.add_argument(
        "--validate",
        action="store_true",
        help="check every problem file resolves, and import nothing",
    )
    ap.add_argument(
        "--set",
        default=None,
        metavar="NAME",
        help="import every declaration of FormalConjectures/Subsets/NAME.lean",
    )
    ap.add_argument(
        "--report",
        default=None,
        metavar="FILE",
        help="with --set: write the per-declaration report here as JSON",
    )
    ap.add_argument(
        "--known-failures",
        default=None,
        metavar="FILE",
        help="with --set: fail unless the failures are exactly the recorded ones",
    )
    args = ap.parse_args(argv)
    if args.validate:
        return importer.validate()
    if args.set:
        known = (
            load_known_failures(args.known_failures)
            if args.known_failures
            else None
        )
        report = import_set(
            args.set, args.out, verify=args.verify, known_failures=known
        )
        text = dump_json(report)
        if args.report:
            pathlib.Path(args.report).write_text(text, encoding="utf-8")
        print(text, end="")
        if known is not None and not report.get("known_failures_match", True):
            return 1
        return 0
    if not args.declaration:
        ap.error("give a declaration, --set, or --validate")
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
