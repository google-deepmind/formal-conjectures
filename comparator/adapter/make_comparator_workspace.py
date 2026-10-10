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
import json
import pathlib
import re
import shutil
import sys
import tempfile

from known_failures import gate, load_known_failures
import fc_leaneval_importer as importer
import fc_source
import leaneval_generator_cli as generator_cli
from leaneval_interface import (
    ImportPolicy,
    PROVENANCE_FILE,
    PROVENANCE_STEM,
    build_problem,
    build_request,
    dump_json,
    sha256_text,
    slug,
)


# The request's context directory, relative to the request file, so an
# emitted seam artifact is self-contained and reproducible from any path.
CONTEXT_DIR = "context"


def _write_files(directory, files):
    """Materialise a `{relative path: content}` mapping under `directory`.

    Every destination must land inside `directory`: the mapping may contain
    paths from a response, and `parse_response` already refuses unsafe ones,
    but the writer is the last line and checks for itself.
    """
    directory = pathlib.Path(directory)
    base = directory.resolve()
    for relative, content in files.items():
        destination = directory / relative
        if not destination.resolve().is_relative_to(base):
            raise SystemExit(f"{relative}: escapes the output directory")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(content, encoding="utf-8")


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
        _write_files(staging, files)
        staging.rename(target)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return target


def import_policy(group=None):
    """The intake policy this command submits under, stated in one place.

    Destination group, lifecycle status, visibility, statement revision and
    submitter are LeanEval's decisions; the schema-version-1 request requires
    them inline, so the command instantiates the draft-intake values
    explicitly rather than leaving them as wire-module constants. A real
    LeanEval intake would build this from the catalog's own state.
    """
    return ImportPolicy(
        group=group or "",
        status="draft",
        visible=True,
        statement_revision=1,
        submitter="formal-conjectures-importer",
        tags=("formal-conjectures",),
    )


def _seam(pairs, group=None):
    """The request and its `build_problem` outputs for `(marked_up, manifest)` pairs."""
    policy = import_policy(group)
    problems = [
        build_problem(marked_up, manifest, policy)
        for marked_up, manifest in pairs
    ]
    target = importer.target_pins()
    template = (
        importer.comparator_dir() / "templates" / "WorkspaceTest.lean"
    ).read_text(encoding="utf-8")
    request = build_request(
        [problem for problem, _ in problems], target, template, CONTEXT_DIR
    )
    return request, problems


def seam_files(pairs, group=None):
    """The request and context for `(marked_up, manifest)` pairs, as files.

    This is the artifact the FC importer contributes once lean-eval consumes
    the shared generator: the request bytes, the context directory the schema-version-1
    contract still reads, and one provenance record per problem — the FC
    source commit and declaration id §10 requires, which the schema-version-1 wire format
    has no field for, so they travel beside it rather than through it.
    """
    request, problems = _seam(pairs, group=group)
    request_text = dump_json(request)
    producer = importer.producer_record()
    files = {"request.json": request_text}
    for path, content in generator_cli.context_files(problems).items():
        files[f"{CONTEXT_DIR}/{path}"] = content
    for (problem, _), (_, manifest) in zip(problems, pairs):
        # Before generation the record binds the module bytes only; the
        # workspace's copy adds the generated files.
        bound = manifest.with_digests(
            sha256_text(problem["moduleContent"]),
            {},
            request_sha256=sha256_text(request_text),
        ).with_producer(producer)
        files[f"{PROVENANCE_STEM}-{problem['id']}.json"] = bound.to_json()
    return request, files


def generate_workspaces(pairs, out_dir, group=None, emit_request=None):
    """Generate one workspace per pair under `out_dir`, via the pinned binary.

    With `emit_request`, the exact request bytes piped to the binary are also
    written to that path — a set audit's artifact should carry the request
    that produced it, not just the reports about it.
    """
    request, problems = _seam(pairs, group=group)
    # One serialisation, used everywhere: the string piped to the binary is
    # the string `--emit-import` writes and the sidecar digests. The request
    # keeps its relative `contextRoot`; the binary runs with the staging
    # directory as its working directory, which is where that root resolves.
    request_text = dump_json(request)
    staging = pathlib.Path(tempfile.mkdtemp(prefix=".fc-seam."))
    try:
        # Only the context crosses to the binary; the request goes on stdin
        # and the provenance sidecars belong to the written workspaces, so
        # neither is staged here.
        _write_files(staging / CONTEXT_DIR, generator_cli.context_files(problems))
        workspaces = generator_cli.generate(
            request_text,
            cwd=staging,
            expected_ids=[p["id"] for p in request["problems"]],
        )
    finally:
        shutil.rmtree(staging, ignore_errors=True)
    if emit_request is not None:
        emit_request = pathlib.Path(emit_request)
        emit_request.parent.mkdir(parents=True, exist_ok=True)
        emit_request.write_text(request_text, encoding="utf-8")
    module_content = {p["id"]: p["moduleContent"] for p in request["problems"]}
    producer = importer.producer_record()
    # Every refusal — digest, identity, sidecar, target-already-exists —
    # happens before the first workspace lands, so a refused batch writes
    # nothing rather than a prefix of itself.
    outputs = []
    for _, manifest in pairs:
        problem_id = slug(manifest.id)
        workspace = dict(workspaces[problem_id])
        # The provenance sidecar rides in the workspace directory, not in the
        # generator's file map: the generator neither knows nor checks it. It
        # binds the exact request and module bytes sent and every file
        # received.
        # The sidecar's `permitted_axioms` is an assertion about the
        # generated Comparator config; check it against the config actually
        # produced, so the recorded policy cannot drift from the enforced one.
        config = json.loads(workspace.get("config.json", "{}"))
        generated_axioms = tuple(config.get("permitted_axioms", ()))
        if sorted(generated_axioms) != sorted(manifest.permitted_axioms):
            raise SystemExit(
                f"{problem_id}: the generated config permits axioms "
                f"{sorted(generated_axioms)}, but the manifest records "
                f"{sorted(manifest.permitted_axioms)}"
            )
        bound = manifest.with_digests(
            sha256_text(module_content[problem_id]),
            {path: sha256_text(content) for path, content in workspace.items()},
            request_sha256=sha256_text(request_text),
        ).with_producer(producer)
        workspace[PROVENANCE_FILE] = bound.to_json()
        outputs.append((pathlib.Path(out_dir) / problem_id, workspace))
    for target, _ in outputs:
        if target.exists():
            raise SystemExit(f"refusing to overwrite existing workspace: {target}")
    return [write_tree(target, files) for target, files in outputs]


def subset_declarations(set_name):
    """The declaration list of a `FormalConjectures/Subsets` module.

    The subset files hold one `decl_name% <qualified name>` per line; the
    `decl_name%` elaborator is what guarantees each name resolves, so the
    text layer can read the list without re-proving that.
    """
    path = fc_source.ROOT / "FormalConjectures" / "Subsets" / f"{set_name}.lean"
    if not path.is_file():
        raise SystemExit(f"no subset module at {path}")
    names = re.findall(
        r"decl_name%\s+([\w.«»]+)", path.read_text(encoding="utf-8")
    )
    if not names:
        raise SystemExit(f"{path} lists no decl_name% entries")
    return names




def import_set(set_name, out_dir, verify=False, known_failures=None):
    """Import a whole subset, generate what imports, and report the rest.

    Returns the report object. Source-side failures — the importer refusing,
    or `--verify` elaboration failing — are recorded per declaration rather
    than aborting the run, because the whole-set result is the artifact:
    lean-eval#536 gates the FC import on this audit being reproducible.
    """
    declarations = subset_declarations(set_name)
    # One batched extractor run pays the Mathlib import once for the whole
    # set. A declaration whose module cannot even be located is skipped here
    # and fails in its own import below, exactly as it always did.
    statement_pairs = []
    for declaration in declarations:
        try:
            statement_pairs.append(importer.statement_pair(declaration))
        except SystemExit:
            continue
    fc_source.prefetch_elaborator_facts(statement_pairs)
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
        generate_workspaces(
            pairs,
            out_dir,
            group="open-conjectures",
            emit_request=pathlib.Path(out_dir) / "request.json",
        )
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
        actual = {
            entry["declaration"]
            for entry in results
            if entry["status"] == "source-failed"
        }
        report["known_failures_match"] = gate(
            known_failures, actual, "source", "declaration"
        )
    return report


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "declaration",
        nargs="?",
        help="a problem id, or a declaration name such as erdos_940",
    )
    ap.add_argument("--out", default=str(fc_source.ROOT / ".comparator"))
    ap.add_argument(
        "--answer-type",
        default=None,
        help="type of a non-Prop answer(sorry) slot, for the rare "
        "statement whose slots the elaborated environment cannot type apart",
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
        if known is None:
            print(
                "no --known-failures: this run reports failures but gates nothing",
                file=sys.stderr,
            )
        if known is not None and not report["known_failures_match"]:
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
