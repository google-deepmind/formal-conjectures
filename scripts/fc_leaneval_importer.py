#!/usr/bin/env python3
"""Map one Formal Conjectures declaration to a LeanEval module and manifest.

This is the Formal Conjectures side of the ownership split in
`leanprover/lean-eval#536`, and it is the part this repository owns
permanently. It resolves a declaration against an exact Formal Conjectures
commit, asks Lean what the elaborated environment knows about it, copies the
declarations it depends on, types each `answer(sorry)` slot, and records where
all of that came from.

What it produces is the pair defined in `scripts/leaneval_interface.py`: one
marked-up Mathlib-only Lean module, and one manifest carrying the FC source
commit and declaration id. Turning that pair into a Challenge / Solution /
Submission workspace is the generator's job, not this module's; see
`scripts/leaneval_generator.py`, which is the part that goes away when
`leanprover/lean-eval-generator` is extracted.

Nothing here writes a workspace file, names a workspace layout, or decides
which generated module imports which. If a change to this file would do one of
those, it belongs on the other side of the seam.

Two things the Lean source cannot settle live in `comparator/problems/<id>.toml`,
one file per problem: an answer type Lean reports ambiguously, and which file
is meant when two declare the same name. See that directory's README.
"""

import json
import pathlib
import re
import subprocess
import sys
import tempfile
import tomllib

from leaneval_interface import (
    DefinitionHole,
    MarkedUpModule,
    ProblemManifest,
    SourceRecord,
)

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_DIRS = [ROOT / "FormalConjectures"]
COMPARATOR_DIR = ROOT / "comparator"
MANIFEST_DIR = COMPARATOR_DIR / "problems"

SOURCE_REPOSITORY = "https://github.com/google-deepmind/formal-conjectures"

PERMITTED_AXIOMS = ("propext", "Quot.sound", "Classical.choice")

DECL_START = re.compile(
    # `local notation` and `scoped notation` carry the modifier before the
    # keyword. Without them here, Erdos 125's `local notation "A" => ...` typed
    # as nothing and was dropped, and its statements lost the sets they name.
    r"^(?:noncomputable\s+|private\s+|protected\s+|local\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|notation)\s",
)
KEEP_LOOSE = re.compile(
    r"^(open|variable|universe|section|namespace|end|attribute|set_option)\b"
)


def tool_pins():
    """The locked external tool revisions; comparator/tools.toml is the one
    machine-readable source, and this module refuses to restate it."""
    with (COMPARATOR_DIR / "tools.toml").open("rb") as handle:
        return tomllib.load(handle)["tools"]


def elaborator_facts(module, declaration):
    """What the elaborated environment knows about a declaration.

    Runs `lake exe comparator_facts`, which imports the module and reports the
    declaration's source range, its binders with real explicitness, and the
    inferred type of each `answer(sorry)` slot. Every one of these used to be
    reconstructed from text, and each reconstruction had failure modes the
    elaborator does not.
    """
    proc = subprocess.run(
        ["lake", "exe", "comparator_facts", module, declaration],
        capture_output=True,
        text=True,
        cwd=ROOT,
    )
    if proc.returncode != 0:
        raise SystemExit(
            f"comparator_facts {declaration}: "
            f"{proc.stderr.strip() or proc.stdout.strip()}"
        )
    out = proc.stdout
    if "{" not in out:
        raise SystemExit(f"comparator_facts {declaration}: no JSON in output")
    return json.loads(out[out.index("{") :])


def file_scoped_preamble(lines, start_line):
    """Directives in force at `start_line`, and the namespace stack there.

    Lean scopes `open`, `variable`, `universe`, `set_option` and notation to
    the file, so the marked-up module has to restate them; nothing in the
    olean records them. A directive counts only if it precedes the statement
    and its scope still encloses it.
    """
    stack, preamble, depth = [], [], 0
    for line in lines[: start_line - 1]:
        if depth == 0 and KEEP_LOOSE.match(line) and not line.rstrip().endswith(" in"):
            kind = line.split()[0]
            parts = line.split(None, 1)
            name = parts[1].strip() if len(parts) > 1 else None
            if kind in ("namespace", "section"):
                stack.append((kind, name))
            elif kind == "end":
                if stack and (
                    stack[-1][1] == name or (name is None and stack[-1][0] == "section")
                ):
                    stack.pop()
            else:
                preamble.append((line, list(stack)))
        depth += len(re.findall(r"/-", line)) - len(re.findall(r"-/", line))
        depth = max(depth, 0)
    scope = list(stack)
    in_force = [text for text, s in preamble if s == scope[: len(s)]]
    return in_force, [n for k, n in scope if k == "namespace" and n]


def load_manifest(problem_id):
    """Read explicit choices that Lean source cannot select by itself.

    An FC problem file selects the module when names collide. It may also
    override an answer-slot type when Lean reports several types that cannot
    be matched to source positions. The importer refuses both cases without an
    explicit choice.

    `leanprover/lean-eval` keeps one TOML per problem, and the reason is worth
    copying: two pull requests adding different problems never touch the same
    file.

      id           the filename stem, and the workspace directory name
      declaration  the Lean name, which need not be unique across the repository
      module       the file declaring it, relative to the repository root
      answer_type  the type of a non-`Prop` answer slot
      notes        free text for a reviewer
      source       a citation or URL
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


def module_name(rel_path):
    """The Lean module name for a path under `FormalConjectures/`.

    Most problem files are named for a number, which is not an identifier, so
    the component is written in guillemets:
    `FormalConjectures.ErdosProblems.«940»`.
    """
    parts = [
        c if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", c) else f"«{c}»"
        for c in str(rel_path)[: -len(".lean")].split("/")
    ]
    return ".".join(parts)


def find_declaration(basename, module=None):
    """Locate the file declaring `basename`. Returns (path, imports, doc, body).

    `module` names the file when more than one declares the name, and comes
    from the problem's FC problem file.
    """
    if module is not None:
        named = ROOT / module
        if not named.exists():
            raise SystemExit(f"manifest names {module}, which does not exist")
        return _read_source(named)
    hits = []
    for src in SOURCE_DIRS:
        for path in sorted(src.rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            if re.search(
                rf"(?:theorem|lemma)\s+(?:[\w.«»]*\.)?{re.escape(basename)}[\s:]", text
            ):
                hits.append(path)
    if not hits:
        raise SystemExit(
            f"no declaration named {basename!r} found under FormalConjectures/"
        )
    if len(hits) > 1:
        raise SystemExit(
            f"{basename!r} is ambiguous: "
            + ", ".join(str(h.relative_to(ROOT)) for h in hits)
            + "; pass --module to choose one, or record the choice in "
            "comparator/problems/<id>.toml"
        )
    return _read_source(hits[0])


def _read_source(path):
    text = path.read_text(encoding="utf-8")
    # Drop the license header; keep the module docstring; the rest is the body.
    text = re.sub(r"\A/-.*?-/\s*", "", text, flags=re.DOTALL)
    doc = ""
    m = re.match(r"\s*(/-!.*?-/)\s*", text, flags=re.DOTALL)
    if m:
        doc = m.group(1)
        text = text[m.end() :]
    # Imports precede the docstring in source order; recover them from the original.
    imports = re.findall(
        r"^import\s+(\S+)", path.read_text(encoding="utf-8"), re.MULTILINE
    )
    return path, imports, doc, text


def strip_decorations(block_text):
    """Remove the docstring, line comments and attributes from a declaration.

    These interleave. Erdos 918 puts a `--` formalisation note between its
    docstring and its `@[category ...]` line, and one anchored pass each left
    the attribute in place. `@[category research open, AMS 5]` then reached the
    marked-up module, where the workspace has no such attribute, and Lean
    parsed as far as the `open` inside it before giving up.
    """
    # `open X in` binds to the declaration and has to survive, but it sits
    # above the docstring, so stripping anchored at the start would stop dead
    # on it.
    prefix = ""
    m = re.match(r"\A\s*(open\b[^\n]*\bin)\n", block_text)
    if m:
        prefix = m.group(1) + "\n"
        block_text = block_text[m.end() :]
    while True:
        stripped = re.sub(r"\A\s*/--.*?-/\s*", "", block_text, flags=re.DOTALL)
        stripped = re.sub(r"\A\s*--[^\n]*\n", "", stripped)
        stripped = re.sub(r"\A\s*@\[[^\]]*\]\s*", "", stripped, flags=re.DOTALL)
        if stripped == block_text:
            return prefix + stripped
        block_text = stripped


# Attributes this repository defines. A generated workspace requires Mathlib
# and nothing else, so these have to go; everything else has to stay.
FC_ATTRIBUTES = ("category", "AMS", "formal_proof")


def strip_fc_attributes(block_text):
    """Remove this repository's own attributes from a copied declaration.

    Unlike `strip_decorations`, which clears every attribute off the target
    statement, this keeps the rest. A dependency is copied to be elaborated,
    not restated, and dropping `simp`, `reducible` or `instance` attributes
    changes how the declarations after it in the same closure elaborate.
    """

    def replace(match):
        inner = match.group(1)
        # Nested brackets mean an argument this simple split would cut in
        # half, so leave the whole attribute alone rather than mangle it.
        if "[" in inner:
            return match.group(0)
        kept = [
            part.strip()
            for part in inner.split(",")
            if part.strip() and part.strip().split()[0] not in FC_ATTRIBUTES
        ]
        return f"@[{', '.join(kept)}]" if kept else ""

    text = re.sub(r"@\[([^\]]*)\]", replace, block_text)
    # An attribute line that emptied out leaves a blank line behind.
    return re.sub(r"^[ \t]*\n", "", text, flags=re.MULTILINE)


def module_source_path(module):
    """The file declaring a dotted Lean module name, undoing guillemets."""
    parts = [
        component[1:-1] if component.startswith("«") else component
        for component in module.split(".")
    ]
    path = ROOT.joinpath(*parts).with_suffix(".lean")
    if not path.is_file():
        raise SystemExit(f"{module}: no source file at {path}")
    return path


def slice_range(lines, source_range):
    """The source text a declaration range covers, and the line it starts on.

    `open X in` binds to the declaration below it but sits above what the
    range covers in some toolchains, so it is pulled in when present.
    """
    lo, hi = source_range["startLine"], source_range["endLine"]
    end_column = source_range.get("endColumn")
    while (
        lo > 1
        and lines[lo - 2].rstrip().endswith(" in")
        and KEEP_LOOSE.match(lines[lo - 2])
    ):
        lo -= 1
    sliced = lines[lo - 1 : hi]
    if end_column is not None and sliced:
        sliced = sliced[:-1] + [sliced[-1][:end_column]]
    return "\n".join(sliced), lo


def closure_region(dependencies, generated, declaration, opened_namespaces=()):
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
    orphans = [
        name
        for name in generated
        if not any(name.startswith(parent + ".") for parent in copied)
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
        chunk = [f"-- {dep['name']}, from {path.relative_to(ROOT)}", "section"]
        chunk += preamble
        if namespace:
            chunk.append(f"namespace {namespace}")
        chunk += ["", body, ""]
        if namespace:
            chunk.append(f"end {namespace}")
        chunk.append("end")
        blocks.append("\n".join(chunk))
        provenance.append(dep["name"])

    # The statement reopens the namespace stack the target sat in, so it can
    # name siblings short. `open` on a namespace nothing has declared is an
    # error, and with the problem's module no longer imported only the copied
    # declarations can declare one. An empty namespace block is enough to make
    # the name exist.
    declared_namespaces = {name.rsplit(".", 1)[0] for name in provenance if "." in name}
    for depth in range(len(opened_namespaces)):
        prefix = ".".join(opened_namespaces[: depth + 1])
        if not any(
            ns == prefix or ns.startswith(prefix + ".") for ns in declared_namespaces
        ):
            blocks.append(f"namespace {prefix}\nend {prefix}")

    listing = "\n".join(f"* `{name}`" for name in provenance)
    return (
        "/-!\n"
        f"The Formal Conjectures declarations `{declaration}` needs, copied so\n"
        "that the statement requires Mathlib and nothing else. Dependencies\n"
        "come before the declarations that use them:\n\n"
        f"{listing}\n"
        "-/\n\n" + "\n\n".join(blocks) + "\n"
    ), provenance


def replace_proof_with_sorry(text):
    """Cut the proof body after `:=`, keeping the statement.

    A tactic proof is found by `:= by`, which a statement cannot contain,
    `by` being a keyword. A term proof leaves only a bare `:=` to cut at, and
    a statement can contain one of those: a structure literal `{ a := b }`
    inside the statement would be cut in half. With more than one candidate
    the importer refuses, as everywhere else it cannot decide.
    """
    m = re.search(r":=\s*by\b", text)
    if m:
        return text[: m.start()].rstrip() + " := by\n  sorry"
    if text.count(":=") > 1:
        raise SystemExit(
            "the declaration has a term-mode proof and more than one `:=`, so "
            "the start of the proof cannot be read off the text"
        )
    m = re.search(r":=", text)
    if m:
        return text[: m.start()].rstrip() + " := by\n  sorry"
    return text.rstrip() + " := by\n  sorry"


def answer_spans(text):
    """Return the source spans of syntactic `answer(...)` calls.

    This small lexer skips strings and nested line/block comments and balances
    parentheses, so an answer term may itself contain parentheses. It is not a
    Lean parser; malformed or unterminated syntax is refused.
    """
    spans = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        pair = text[i : i + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
            elif pair == "-/":
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif text[i] == "\\":
                escaped = True
            elif text[i] == '"':
                in_string = False
            i += 1
            continue
        if pair == "/-":
            block_depth = 1
            i += 2
            continue
        if pair == "--":
            newline = text.find("\n", i + 2)
            i = len(text) if newline < 0 else newline + 1
            continue
        if text[i] == '"':
            in_string = True
            i += 1
            continue
        if text.startswith("answer", i) and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")
        ):
            j = i + len("answer")
            while j < len(text) and text[j].isspace():
                j += 1
            if j < len(text) and text[j] == "(":
                depth = 1
                k = j + 1
                nested_string = False
                nested_escaped = False
                nested_comment = 0
                while k < len(text) and depth:
                    nested_pair = text[k : k + 2]
                    if nested_comment:
                        if nested_pair == "/-":
                            nested_comment += 1
                            k += 2
                        elif nested_pair == "-/":
                            nested_comment -= 1
                            k += 2
                        else:
                            k += 1
                        continue
                    if nested_string:
                        if nested_escaped:
                            nested_escaped = False
                        elif text[k] == "\\":
                            nested_escaped = True
                        elif text[k] == '"':
                            nested_string = False
                        k += 1
                        continue
                    if nested_pair == "/-":
                        nested_comment = 1
                        k += 2
                    elif nested_pair == "--":
                        newline = text.find("\n", k + 2)
                        k = len(text) if newline < 0 else newline + 1
                    elif text[k] == '"':
                        nested_string = True
                        k += 1
                    else:
                        if text[k] == "(":
                            depth += 1
                        elif text[k] == ")":
                            depth -= 1
                        k += 1
                if depth:
                    raise SystemExit("unterminated answer(...) term")
                spans.append((i, k, text[j + 1 : k - 1]))
                i = k
                continue
        i += 1
    if block_depth or in_string:
        raise SystemExit("unterminated comment or string while reading answers")
    return spans


def unwrap_answers(statement):
    """Replace any surviving `answer(t)` with `(t)`.

    `answer` is this repository's own elaborator, so a Mathlib-only workspace
    cannot parse it. `hoist_answers` removes the `answer(sorry)` slots by
    turning them into definition holes; a slot that already carries its answer,
    which is how a `research solved` statement is written, is left behind and
    used to reach the marked-up module as literal text that does not parse.

    Unwrapping is faithful. In the default `postpone` mode the elaborator
    elaborates the term and attaches an annotation
    (`FormalConjecturesUtil/Answer.lean`), so `answer(t)` and `t` denote the
    same term and only the annotation is lost. The annotation is what marks
    which part of the statement was the question, and the manifest records
    that instead.
    """
    for start, end, argument in reversed(answer_spans(statement)):
        statement = statement[:start] + f"({argument.strip()})" + statement[end:]
    return statement


def hoist_answers(statement, basename, slot_types, override=None):
    """Replace each `answer(sorry)` with a named definition hole.

    The slot types come from the elaborated environment, where the `answer`
    elaborator ran with the expected type in hand; the old surface-syntax
    guess (an `↔` beside the slot means `Prop`) and the FC problem file's
    hand-kept `answer_type` both survive only as overrides. Slots of different
    types in one statement are refused: the environment reports the types as a
    set, and matching them to positions would be a guess.
    """
    holes = []
    calls = answer_spans(statement)
    selected = [call for call in calls if call[2].strip() == "sorry"]
    count = len(selected)
    if count == 0:
        return statement, holes
    # Under the default `alwaysTrue` setting, the `answer` elaborator erases a
    # slot to `True` if and only if its expected type is `Prop`
    # (FormalConjecturesUtil/Answer.lean). So a slot the environment carries
    # no annotation for is a `Prop` slot by the elaborator's own rule, not by
    # guesswork, and no postpone build is needed.
    missing = count - len(slot_types)
    if override:
        types = [override] * count
    elif missing == count:
        types = ["Prop"] * count
    elif missing == 0 and len(set(slot_types)) == 1:
        types = [slot_types[0]] * count
    elif missing == 0:
        raise SystemExit(
            f"{basename} has {count} answer slots of differing types "
            f"{slot_types}; pass --answer-type"
        )
    else:
        # Some slots are Prop and some are not: which positions are which
        # cannot be read off an unordered set, so refuse rather than assign.
        raise SystemExit(
            f"{basename}: {missing} Prop slot(s) and {len(slot_types)} typed "
            f"slot(s) {slot_types} cannot be matched to positions; pass "
            "--answer-type"
        )
    replacements = []
    for i, (start, end, _argument) in enumerate(selected):
        name = f"{basename}_answer" if count == 1 else f"{basename}_answer_{i + 1}"
        holes.append(DefinitionHole(name=name, type=types[i]))
        replacements.append((start, end, name))
    for start, end, name in reversed(replacements):
        statement = statement[:start] + name + statement[end:]
    return statement, holes


def pins(source_path=None):
    """Revisions the workspace's own build can actually fetch.

    The FC pin must be reachable from the upstream repository the lakefile
    names, so it is the merge-base with `origin/main`, not HEAD: a local
    branch commit would generate a workspace whose build fails at fetch time.
    The importer stops if the selected source differs from that revision.
    Otherwise it could combine a working-tree statement with an older imported
    context.
    """
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib_rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
    merge_base = subprocess.run(
        ["git", "-C", str(ROOT), "merge-base", "HEAD", "origin/main"],
        capture_output=True,
        text=True,
    )
    if merge_base.returncode != 0 or not merge_base.stdout.strip():
        raise SystemExit("cannot resolve the Formal Conjectures source revision")
    fc_rev = merge_base.stdout.strip()
    if source_path is not None:
        comparison = subprocess.run(
            ["git", "-C", str(ROOT), "diff", "--quiet", fc_rev, "--", str(source_path)]
        )
        if comparison.returncode not in (0, 1):
            raise SystemExit(f"cannot compare {source_path} with {fc_rev[:12]}")
        if comparison.returncode == 1:
            raise SystemExit(
                f"{source_path} differs from pinned revision {fc_rev[:12]}; "
                "land the source on upstream main before generating"
            )
    return mathlib_rev, fc_rev


def source_record(declaration, module, source_path, fc_rev, dependencies, original):
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
    answer_type = answer_type or problem_file.get("answer_type")
    module = module or problem_file.get("module")
    path, _imports, _module_doc, _body = find_declaration(declaration, module)
    fc_module = module_name(path.relative_to(ROOT))
    facts = elaborator_facts(fc_module, declaration)
    if facts["range"] is None:
        raise SystemExit(f"{declaration}: no source range recorded")

    source_lines = path.read_text(encoding="utf-8").split("\n")
    original, lo = slice_range(source_lines, facts["range"])
    statement = original

    preamble, namespaces_at_target = file_scoped_preamble(source_lines, lo)
    dependencies, copied = closure_region(
        facts.get("dependencies", []),
        facts.get("generatedDependencies", []),
        declaration,
        namespaces_at_target,
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
    # outer one, and a statement may name siblings from either.
    opens = [
        f"open {'.'.join(namespaces_at_target[: i + 1])}"
        for i in range(len(namespaces_at_target))
    ]

    mathlib_rev, fc_rev = pins(path.relative_to(ROOT))
    marked_up = MarkedUpModule(
        dependencies=dependencies,
        scope="\n".join(opens + preamble),
        holes="\n\n".join(hole.declaration() for hole in holes),
        statement=statement,
    )
    manifest = ProblemManifest(
        id=problem_file.get("id", declared),
        theorem=declared,
        qualified_theorem=".".join(namespaces_at_target + [declared]),
        apply_arguments=tuple(args),
        holes=tuple(holes),
        permitted_axioms=PERMITTED_AXIOMS,
        lean_toolchain=(ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        mathlib_revision=mathlib_rev,
        source=source_record(
            declared,
            fc_module,
            path.relative_to(ROOT),
            fc_rev,
            [dep["name"] for dep in facts.get("dependencies", [])],
            original,
        ),
        tools=tool_pins(),
        source_url=str(problem_file.get("source", "")),
        notes=str(problem_file.get("notes", "")),
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
    on the FC side, not in lean-eval's CI. It is offline, and it uses the
    Mathlib revision the manifest pins because that is this checkout's. It
    checks elaboration, not a lakefile; a Comparator run exercises the build.
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
