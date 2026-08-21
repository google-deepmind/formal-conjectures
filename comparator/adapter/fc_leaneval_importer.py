#!/usr/bin/env python3
"""Map one Formal Conjectures declaration to a LeanEval module and manifest.

This is the Formal Conjectures side of the ownership split in
`leanprover/lean-eval#536`, and it is the part this repository owns
permanently. It resolves a declaration against an exact Formal Conjectures
commit, asks Lean what the elaborated environment knows about it, copies the
declarations it depends on, types each `answer(sorry)` slot, and records where
all of that came from.

What it produces is the pair defined in `comparator/adapter/leaneval_interface.py`: one
marked-up Mathlib-only Lean module, and one manifest carrying the FC source
commit and declaration id. Turning that pair into a Challenge / Solution /
Submission workspace is the pinned `leanprover/lean-eval-generator` binary's
job, not this module's; `leaneval_interface.build_request` is where the pair
becomes that binary's input.

Nothing here writes a workspace file, names a workspace layout, or decides
which generated module imports which. If a change to this file would do one of
those, it belongs on the other side of the seam.

Two source-boundary facts may live in `comparator/problems/<id>.toml`, one
file per problem: which file is meant when two declare the same name, and an
explicit source-only proof dependency when Lean's opaque-value erasure makes
that dependency unrecoverable from the compiled environment.
"""

import pathlib
import re
import subprocess
import sys
import tempfile
import tomllib

from leaneval_interface import (
    MarkedUpModule,
    ProblemManifest,
    SourceRecord,
    TargetRecord,
)
from fc_source import (
    DECL_START,
    docstring_reference,
    elaborator_facts,
    file_scoped_preamble,
    find_declaration,
    flatten_declared_name,
    hoist_answers,
    localise_notation,
    module_name,
    module_source_path,
    notation_blocks,
    pins,
    replace_proof_with_sorry,
    ROOT,
    slice_range,
    strip_decorations,
    strip_fc_attributes,
    unwrap_answers,
)
COMPARATOR_DIR = ROOT / "comparator"
MANIFEST_DIR = COMPARATOR_DIR / "problems"

SOURCE_REPOSITORY = "https://github.com/google-deepmind/formal-conjectures"

PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")


def _tools_file():
    """comparator/tools.toml is the one machine-readable source of pins, and
    this module refuses to restate it."""
    with (COMPARATOR_DIR / "tools.toml").open("rb") as handle:
        return tomllib.load(handle)


def target_pins():
    """LeanEval's pins, where a generated workspace is built and checked.

    They are not this repository's, and the importer neither chooses them nor
    elaborates against them. It records them because a workspace that is
    vendored into lean-eval has to be buildable there, and because a manifest
    that carries both pin sets makes the gap between where the hole types were
    read and where they will be used a readable fact rather than an assumption.
    """
    target = _tools_file()["target"]
    return TargetRecord(
        lean_toolchain=target["lean_toolchain"],
        mathlib_revision=target["mathlib_revision"],
    )


def explicit_copy_dependencies(problem_file):
    """Source-only dependencies the compiled environment cannot retain.

    Lean erases the values of opaque theorem constants.  If the source body
    of a copied definition invokes such a theorem only to construct a proof
    argument, the compiled definition refers to a generated `_proof_*`
    constant and no longer records which source theorem produced it.  The
    marked-up module still copies source text, so that theorem must be named
    explicitly and audibly in the problem manifest.
    """
    records, generated = [], []
    for entry in problem_file.get("copy_dependencies", []):
        if set(entry) != {"declaration", "module"}:
            raise SystemExit(
                "each `copy_dependencies` entry must contain exactly "
                "`declaration` and `module`"
            )
        relative = pathlib.Path(entry["module"])
        if (
            relative.is_absolute()
            or ".." in relative.parts
            or not relative.parts
            or relative.parts[0]
            not in {"FormalConjectures", "FormalConjecturesForMathlib"}
        ):
            raise SystemExit(
                f"copy dependency module must stay under a source tree: {relative}"
            )
        path = ROOT / relative
        if not path.is_file() or relative.suffix != ".lean":
            raise SystemExit(f"copy dependency module does not exist: {relative}")
        module = module_name(relative)
        facts = elaborator_facts(module, entry["declaration"])
        records.extend(facts.get("dependencies", []))
        records.append(
            {
                "name": facts["name"],
                "module": module,
                "range": facts["range"],
            }
        )
        generated.extend(facts.get("generatedDependencies", []))
    return records, generated


def merge_dependency_records(*groups):
    """Deduplicate topologically ordered dependency records, fail closed."""
    merged, seen = [], {}
    for group in groups:
        for record in group:
            name = record["name"]
            if name in seen:
                if seen[name] != record:
                    raise SystemExit(f"conflicting dependency records for {name}")
                continue
            seen[name] = record
            merged.append(record)
    return merged


def load_manifest(problem_id):
    """Read the rare source-boundary facts Lean cannot select by itself.

    When two files declare the same name, nothing in the Lean environment says
    which one was meant, so the importer refuses until a module is named.
    `copy_dependencies` is the other exceptional field: it names a theorem
    used only in copied source proof text when opaque-value erasure removes
    the reference from Lean's compiled dependency graph.

    `leanprover/lean-eval` keeps one TOML per problem, and the reason is worth
    copying: two pull requests adding different problems never touch the same
    file.

      id           the filename stem, and the workspace directory name
      declaration  the Lean name, which need not be unique across the repository
      module       the file declaring it, relative to the repository root
      copy_dependencies  exact declaration/module pairs to copy before the
                    environment-derived closure

    Anything Formal Conjectures already states stays where it is stated. The
    source citation is read from the module docstring rather than copied here,
    because a copy can drift from the docstring the repository maintains. An
    ambiguous answer-slot type is a `--answer-type` argument: it is rare, and
    a field no problem uses is a format nobody can check.
    """
    path = MANIFEST_DIR / f"{problem_id}.toml"
    if not path.exists():
        return {}
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    if data.get("id") != problem_id:
        raise SystemExit(
            f"{path} declares id {data.get('id')!r}, but its filename says "
            f"{problem_id!r}; the two must agree"
        )
    if "declaration" not in data:
        raise SystemExit(f"{path} has no `declaration` field")
    return data


def manifest_ids():
    return sorted(p.stem for p in MANIFEST_DIR.glob("*.toml"))


def closure_region(
    dependencies, generated, declaration, opened_namespaces=(), target_name=None
):
    """A declaration's FC-local closure, copied, needing Mathlib and nothing else.

    lean-eval vendors problems, so a generated Challenge cannot fetch this
    repository at evaluation time and has to stand on Mathlib alone. That
    rules out importing the problem's own module, and brings back the failure
    modes an import does not have: file-scoped `open` and `variable` lost,
    `local notation` unrecognised, a namespace swallowing what follows.

    So each declaration is emitted inside its own `section`, carrying the
    preamble in force where it was written and reopening the namespace it was
    written in. That is a construction, not a proof, and the only check that
    covers every one of those failure modes at once is elaborating the
    marked-up module, which `--verify` does.
    """
    copied = [dep["name"] for dep in dependencies]
    # The statement's own `match` and `proof` auxiliaries have the statement
    # as their ancestor, and the statement is restated in the workspace, so
    # re-elaborating it regenerates them; only an auxiliary of something not
    # being copied at all is unreachable.
    ancestors = copied + ([target_name] if target_name else [])
    orphans = [
        name
        for name in generated
        if not any(name.startswith(parent + ".") for parent in ancestors)
    ]
    if orphans:
        raise SystemExit(
            f"{declaration}: {len(orphans)} elaborator-generated constant(s) "
            "have no copied ancestor, so copying the closure would not "
            f"reproduce them: {', '.join(orphans[:5])}"
        )

    # A constructor, a `where` auxiliary and a `_sparseCasesOn` all carry a
    # source range inside the declaration that produces them, so copying them
    # in their own right either duplicates a declaration or slices a fragment
    # of one. `MonochromaticQuantumGraph.EdgeN.mk` covers line 88 of a
    # structure spanning 83 to 93; `pmSumListAux._sparseCasesOn_1` has exactly
    # its parent's range. Copying the outer declaration reproduces both.
    def covered_by_another(dep):
        inner = dep["range"]
        for other in dependencies:
            if other is dep or other["module"] != dep["module"]:
                continue
            outer = other["range"]
            if outer is None or inner is None:
                continue
            if not (
                outer["startLine"] <= inner["startLine"]
                and outer["endLine"] >= inner["endLine"]
            ):
                continue
            same_span = (
                outer["startLine"] == inner["startLine"]
                and outer["endLine"] == inner["endLine"]
            )
            # A tie on the span is broken by name: the parent is the prefix.
            if not same_span or len(other["name"]) < len(dep["name"]):
                return True
        return False

    subsumed = [dep["name"] for dep in dependencies if covered_by_another(dep)]
    dependencies = [dep for dep in dependencies if dep["name"] not in subsumed]

    blocks, provenance = [], []
    # `open X` on a namespace nothing has declared yet is an error, and a
    # copied preamble may open a namespace whose declaring block comes later
    # in the copy, or never: with the problem's module no longer imported,
    # only the copy itself can make a name exist. An empty namespace block
    # up front is enough, and creating one that a later declaration fills is
    # harmless. This covers the statement's own namespace stack and every
    # namespace a copied preamble opens.
    created = []
    for dep in dependencies:
        if dep["range"] is None:
            continue
        dep_path = module_source_path(dep["module"])
        dep_lines = dep_path.read_text(encoding="utf-8").split("\n")
        dep_preamble, dep_namespaces = file_scoped_preamble(
            dep_lines, slice_range(dep_lines, dep["range"])[1]
        )
        for entry in dep_preamble:
            words = entry.split("\n")[0].split()
            if not words or words[0] != "open":
                continue
            for word in words[1:]:
                if word == "scoped":
                    continue
                if not re.fullmatch(r"[\w.«»]+", word):
                    break
                created.append(word)
        created.extend(
            ".".join(dep_namespaces[: depth + 1])
            for depth in range(len(dep_namespaces))
        )
    created.extend(
        ".".join(opened_namespaces[: depth + 1])
        for depth in range(len(opened_namespaces))
    )
    seen_namespaces = set()
    for namespace in created:
        if namespace in seen_namespaces:
            continue
        seen_namespaces.add(namespace)
        blocks.append(f"namespace {namespace}\nend {namespace}")
    for dep in dependencies:
        if dep["range"] is None:
            raise SystemExit(f"{declaration}: {dep['name']} has no source range")
        path = module_source_path(dep["module"])
        lines = path.read_text(encoding="utf-8").split("\n")
        text, start = slice_range(lines, dep["range"])
        preamble, namespaces = file_scoped_preamble(lines, start)
        body = strip_fc_attributes(text).strip("\n")
        if not body:
            raise SystemExit(f"{declaration}: {dep['name']} sliced to nothing")
        namespace = ".".join(namespaces)
        chunk = [
            f"-- {dep['name']}, from {path.relative_to(ROOT)}",
            "noncomputable section",
        ]
        chunk += preamble
        if namespace:
            chunk.append(f"namespace {namespace}")
        chunk += ["", body, ""]
        if namespace:
            chunk.append(f"end {namespace}")
        chunk.append("end")
        blocks.append("\n".join(chunk))
        provenance.append((dep["name"], body))

    listing = "\n".join(f"* `{name}`" for name, _ in provenance)
    return (
        "/-!\n"
        f"The Formal Conjectures declarations `{declaration}` needs, copied so\n"
        "that the statement requires Mathlib and nothing else. Dependencies\n"
        "come before the declarations that use them:\n\n"
        f"{listing}\n"
        "-/\n\n" + "\n\n".join(blocks) + "\n"
    ), provenance


def source_record(
    declaration, module, source_path, fc_rev, dependencies, original, mathlib_rev
):
    """Where the copied statement and its dependencies came from.

    lean-eval#536 requires the manifest to record the FC source commit and
    declaration id, and it is the FC side that has to supply them: the
    generator sees a Lean module, not a repository. They are also what makes
    the importer's regeneration duty possible — when Formal Conjectures fixes
    a misformalisation upstream, this record says which problem to redo.
    """
    blob = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", f"{fc_rev}:{source_path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    return SourceRecord(
        repository=SOURCE_REPOSITORY,
        commit=fc_rev,
        path=str(source_path),
        blob_sha=blob.stdout.strip() or "",
        module=module,
        declaration=declaration,
        copied_dependencies=tuple(dependencies),
        original_declaration=original,
        lean_toolchain=(ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        mathlib_revision=mathlib_rev,
    )


def import_problem(problem, answer_type=None, module=None):
    """Map one declaration to a marked-up module and a manifest.

    Importing a closure out of a repository full of `sorry` is safe because
    Comparator checks axioms. A solution closing the goal with a copied
    statement reports `sorryAx`, which `permitted_axioms` does not allow.
    """
    problem_file = load_manifest(problem)
    declaration = problem_file.get("declaration", problem)
    # An argument given on the command line is explicit, so it wins over the
    # problem file; the file is the durable record of the same choice.
    module = module or problem_file.get("module")
    path, _imports, module_doc, _body = find_declaration(declaration, module)
    fc_module = module_name(path.relative_to(ROOT))
    facts = elaborator_facts(fc_module, declaration)
    if facts["range"] is None:
        raise SystemExit(f"{declaration}: no source range recorded")
    explicit_dependencies, explicit_generated = explicit_copy_dependencies(problem_file)
    facts["dependencies"] = merge_dependency_records(
        explicit_dependencies, facts.get("dependencies", [])
    )
    facts["generatedDependencies"] = list(
        dict.fromkeys(explicit_generated + facts.get("generatedDependencies", []))
    )

    source_lines = path.read_text(encoding="utf-8").split("\n")
    original, lo = slice_range(source_lines, facts["range"])
    statement = original

    preamble, namespaces_at_target = file_scoped_preamble(source_lines, lo)
    dependencies, copied = closure_region(
        facts.get("dependencies", []),
        facts.get("generatedDependencies", []),
        declaration,
        namespaces_at_target,
        target_name=facts.get("name"),
    )

    statement = strip_decorations(statement)
    statement = replace_proof_with_sorry(statement)
    declared = None
    for line in statement.split("\n"):
        dm = DECL_START.match(line)
        if dm:
            declared = re.match(r"\s*([\w.«»]+)", line[dm.end() :]).group(1)
            break
    if declared is None:
        raise SystemExit(f"{declaration}: no declaration line in the slice")
    original_declared = declared
    if "." in declared:
        # The generator anchors on the declaration's last name component —
        # its own sources always declare a plain identifier inside a
        # namespace — so a dotted name like `erdos_100.variants.strong`
        # would come out as `theorem strong`, and `parts.i` as `theorem i`.
        # Restate the declaration under its slug instead: single identifier,
        # still meaningful, and the provenance sidecar records the FC name.
        declared, statement = flatten_declared_name(declared, statement)
    statement, holes = hoist_answers(
        statement, declared, facts.get("answerTypes", []), answer_type
    )
    # A `research solved` statement carries its answer rather than a `sorry`
    # slot, so nothing above removed it and `answer(` would reach a workspace
    # that cannot parse it.
    statement = unwrap_answers(statement)

    args = [b["name"] for b in facts["binders"] if b["explicit"]]
    bad = [a for a in args if "✝" in a or "._" in a]
    if bad:
        raise SystemExit(
            f"{declared} has inaccessible explicit binders {bad}; the "
            "Solution adapter cannot apply them by name"
        )

    # `open A`, then `open A.B`: opening the inner namespace does not open the
    # outer one, and a statement may name siblings from either. With nothing
    # copied there are no siblings to name and nothing declares the
    # namespace, so an open would be an unresolvable orphan in a generated
    # file that has no ChallengeDeps to import.
    opens = (
        [
            f"open {'.'.join(namespaces_at_target[: i + 1])}"
            for i in range(len(namespaces_at_target))
        ]
        if copied
        else []
    )

    mathlib_rev, fc_rev = pins(path.relative_to(ROOT))
    preamble = localise_notation(preamble)
    scope_text = "\n".join(opens + preamble)
    # Notation is text, not a constant: a statement or copied declaration
    # spelled with an FC-defined token needs the defining command copied too,
    # and the elaborated closure cannot say so.
    # Namespaces the module opens, at its scope and inside every copied
    # block: a scoped notation can only have been in force where one of
    # these opens it.
    opened_for_notation = set()
    for line in (dependencies + "\n" + scope_text).split("\n"):
        words = line.split()
        if words[:1] == ["open"]:
            opened_for_notation.update(w for w in words[1:] if w != "scoped")
    notations = notation_blocks(
        [dependencies, scope_text, statement], opened_for_notation
    )
    if notations:
        # A notation whose right-hand side names a copied declaration must
        # come after the block declaring it; every other notation comes
        # first, because copied declarations may use its token textually. A
        # single notation needing both would need interleaving; none does,
        # and `--verify` is what says so.
        copied_last_components = {name.rsplit(".", 1)[-1] for name, _ in copied}
        before, after = [], []
        for block in notations:
            rhs = block.split("=>", 1)[-1]
            names = set(re.findall(r"[\w«»'.]+", rhs))
            names |= {name.rsplit(".", 1)[-1] for name in names}
            if names & copied_last_components:
                after.append(block)
            else:
                before.append(block)
        if before:
            dependencies = "\n\n".join(before) + "\n\n" + dependencies
        if after:
            dependencies = dependencies + "\n\n" + "\n\n".join(after)
    marked_up = MarkedUpModule(
        dependencies=dependencies,
        scope=scope_text,
        holes="\n\n".join(hole.declaration() for hole in holes),
        statement=statement,
        dependency_declarations=tuple(copied),
    )
    # The FC name, under the namespaces the source declared it in; the
    # workspace statement may carry the flattened `declared` instead, and
    # this is what ties the two together.
    qualified = ".".join(namespaces_at_target + [original_declared])
    manifest = ProblemManifest(
        # The default id is the qualified name: two modules declaring
        # `conjecture` in different namespaces must not share a workspace.
        id=problem_file.get("id", qualified),
        theorem=declared,
        qualified_theorem=qualified,
        apply_arguments=tuple(args),
        holes=tuple(holes),
        permitted_axioms=PERMITTED_AXIOMS,
        source=source_record(
            qualified,
            fc_module,
            path.relative_to(ROOT),
            fc_rev,
            [dep["name"] for dep in facts.get("dependencies", [])],
            original,
            mathlib_rev,
        ),
        source_url=docstring_reference(module_doc),
        category=facts.get("category") or "",
    )
    return marked_up, manifest


def elaborate(marked_up):
    """Elaborate the marked-up module against this checkout's Mathlib.

    Copying a closure is a construction, and its failure modes are the ones
    Lean sees and a reader does not: a lost `open`, an unrecognised
    `local notation`, a namespace that no longer exists because nothing
    declares it any more. Each of those is a clean build away from being
    caught and a long review away from being spotted.

    The check runs here rather than on a generated workspace because the
    module is what this repository hands over: an FC-side defect should fail
    on the FC side, not in lean-eval's CI. It is offline, and it runs at this
    repository's Lean and Mathlib, which are the manifest's `source` pins and
    not its `target` pins: a module that elaborates here is not thereby known
    to elaborate at LeanEval's toolchain, and only a build there settles that.
    It checks elaboration, not a lakefile; a Comparator run exercises the
    build.
    """
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, encoding="utf-8"
    ) as handle:
        handle.write(marked_up.render())
        combined = handle.name
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", combined],
            capture_output=True,
            text=True,
            cwd=ROOT,
            check=False,
        )
    finally:
        pathlib.Path(combined).unlink(missing_ok=True)
    output = (proc.stdout + proc.stderr).replace(combined, "Problem")
    # Only errors fail the check. The target statement's proof is `sorry` by
    # construction and each `answer(sorry)` hole is one the solver fills, so
    # those warnings are the importer working. Linter warnings such as
    # `unused variable` come from the copied source and say nothing about
    # whether the copy is faithful.
    errors = [line for line in output.splitlines() if "error:" in line]
    if proc.returncode != 0 or errors:
        raise SystemExit(
            "the marked-up module does not elaborate:\n"
            + "\n".join(errors or output.splitlines()[-10:])
        )
    return 0


def validate():
    """Check every FC problem file resolves to exactly one declaration.

    Run this rather than discovering a stale `module` field when someone
    imports the problem months later.
    """
    bad = 0
    for problem_id in manifest_ids():
        try:
            problem_file = load_manifest(problem_id)
            declaration = problem_file["declaration"]
            path, _i, _d, _b = find_declaration(declaration, problem_file.get("module"))
            elaborator_facts(module_name(path.relative_to(ROOT)), declaration)
        except SystemExit as exc:
            print(f"{problem_id}: {exc}", file=sys.stderr)
            bad += 1
            continue
        print(f"{problem_id}: {declaration} in {path.relative_to(ROOT)}")
    if bad:
        print(f"{bad} problem file(s) do not resolve", file=sys.stderr)
    return 1 if bad else 0
