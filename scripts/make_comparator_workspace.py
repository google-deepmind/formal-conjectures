#!/usr/bin/env python3
"""Generate a comparator workspace for one problem statement.

`leanprover/lean-eval` verifies a submission by building it against a Challenge
module whose statement the maintainers trust, under a config that pins the
permitted axioms. This script generates that shape for one Formal Conjectures
declaration.

Challenge.lean imports the problem's own module. lean-eval's generated
Challenge is one `import Mathlib` and one statement, because its problems are
authored self-contained; this repository's are not, so the import here is the
problem's module and the statement's context comes with it. Only what Lean
scopes to a file has to be copied: `open`, `variable`, `universe`,
`set_option` and `local notation`.

Layout produced:

  <out>/<id>/
    lakefile.toml       pins: this checkout's Mathlib rev and FC commit
    Challenge.lean      the import, the file-scoped preamble, the target
                        statement with attributes stripped and its proof
                        replaced by `sorry`, and each `answer(sorry)` hoisted
                        into a definition hole the solver must fill
    Submission.lean     where the solver works; helper modules go under
                        Submission/
    Solution.lean       fixed: restates the statement and closes it with the
                        Submission theorem, so the statement cannot drift
    WorkspaceTest.lean  `lake test` runs comparator on config.json
    README.md           what the solver needs to know, cache fetch included
    config.json         theorem and definition names, permitted axioms
    holes.json          the extracted blocks, for tooling and for review

Lean reports the type of each `answer(sorry)` slot. The generator refuses a
case when it cannot match the reported types to their source positions.

Two things the source cannot settle live in `comparator/problems/<id>.toml`,
one file per problem: that answer type, and which file is meant when two
declare the same name. See that directory's README.

Usage:
  python make_comparator_workspace.py (ID | DECLARATION) [--out DIR]
      [--answer-type T] [--module FILE]
  python make_comparator_workspace.py --validate

The workspace's own build needs a network fetch of its pinned dependencies, so
this script does not attempt it; generation is offline and the build belongs to
the comparator run.
"""

import argparse
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_DIRS = [ROOT / "FormalConjectures"]
COMPARATOR_DIR = ROOT / "comparator"
MANIFEST_DIR = COMPARATOR_DIR / "problems"


def tool_pins():
    """The locked external tool revisions; comparator/tools.toml is the one
    machine-readable source, and this module refuses to restate it."""
    with (COMPARATOR_DIR / "tools.toml").open("rb") as handle:
        return tomllib.load(handle)["tools"]


PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]

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
    the file, so Challenge.lean has to restate them; nothing in the olean
    records them. A directive counts only if it precedes the statement and
    its scope still encloses it.
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


def slug(name):
    """A Lake package name and directory name for a declaration.

    A Lake package name is an identifier, so the dots in a qualified
    declaration cannot go into one verbatim.
    """
    return re.sub(r"[^0-9A-Za-z_]", "_", name)


def load_manifest(problem_id):
    """Read explicit choices that Lean source cannot select by itself.

    A manifest selects the module when names collide. It may also override an
    answer-slot type when Lean reports several types that cannot be matched to
    source positions. The generator refuses both cases without an explicit
    choice.

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
    """Locate the file declaring `basename`. Returns (path, module_docstring, body).

    `module` names the file when more than one declares the name, and comes
    from the problem's manifest.
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
    the attribute in place. `@[category research open, AMS 5]` then reached
    Challenge.lean, where the workspace has no such attribute, and Lean parsed
    as far as the `open` inside it before giving up.
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


def replace_proof_with_sorry(text):
    """Cut the proof body after `:=`, keeping the statement.

    A tactic proof is found by `:= by`, which a statement cannot contain,
    `by` being a keyword. A term proof leaves only a bare `:=` to cut at, and
    a statement can contain one of those: a structure literal `{ a := b }`
    inside the statement would be cut in half. With more than one candidate
    the script refuses, as everywhere else it cannot decide.
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


def hoist_answers(statement, basename, slot_types, override=None):
    """Replace each `answer(sorry)` with a named definition hole.

    The slot types come from the elaborated environment, where the `answer`
    elaborator ran with the expected type in hand; the old surface-syntax
    guess (an `↔` beside the slot means `Prop`) and the manifest's hand-kept
    `answer_type` both survive only as overrides. Slots of different types in
    one statement are refused: the environment reports the types as a set,
    and matching them to positions would be a guess.
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
        hole = f"{basename}_answer" if count == 1 else f"{basename}_answer_{i + 1}"
        holes.append(f"noncomputable def {hole} : {types[i]} := sorry")
        replacements.append((start, end, hole))
    for start, end, hole in reversed(replacements):
        statement = statement[:start] + hole + statement[end:]
    return statement, holes


def pins(source_path=None):
    """Revisions the workspace's own build can actually fetch.

    The FC pin must be reachable from the upstream repository the lakefile
    names, so it is the merge-base with `origin/main`, not HEAD: a local
    branch commit would generate a workspace whose build fails at fetch time.
    The generator stops if the selected source differs from that revision.
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


def lakefile(workspace_id, mathlib_rev, fc_rev):
    return f"""name = "{workspace_id}"
testDriver = "workspace_test"
defaultTargets = ["Challenge", "Solution", "Submission"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{mathlib_rev}"

[[require]]
name = "formal_conjectures"
git = "https://github.com/google-deepmind/formal-conjectures.git"
rev = "{fc_rev}"

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Submission"

[[lean_exe]]
name = "workspace_test"
root = "WorkspaceTest"
"""


def hole_names_of(holes):
    return [h.split()[2] for h in holes]


def write_workspace(target, files):
    """Write a complete workspace without overwriting or leaving a partial one."""
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


def generate(basename, out_dir, answer_type=None, module=None):
    """Write a comparator workspace for one declaration.

    Challenge.lean imports the problem's own module rather than restating its
    dependencies. `leanprover/lean-eval` generates a Challenge that is one
    `import` and one statement, and reconstructing the surrounding definitions
    by hand instead cost six defects that only Lean could find: file-scoped
    `open` and `variable` lost, `local notation` unrecognised, a `namespace`
    swallowing the declaration below it, `section` lines left unclosed. An
    import has none of those failure modes.

    Importing a repository full of `sorry` is safe here because comparator
    checks axioms. A solution closing the goal with the imported statement
    reports `sorryAx`, which `permitted_axioms` does not allow.
    """
    manifest = load_manifest(basename)
    declaration = manifest.get("declaration", basename)
    # An argument given on the command line is explicit, so it wins over the
    # manifest; the manifest is the durable record of the same choice.
    answer_type = answer_type or manifest.get("answer_type")
    module = module or manifest.get("module")
    path, _imports, _module_doc, body = find_declaration(declaration, module)
    fc_module = module_name(path.relative_to(ROOT))
    facts = elaborator_facts(fc_module, declaration)
    if facts["range"] is None:
        raise SystemExit(f"{declaration}: no source range recorded")

    source_lines = path.read_text(encoding="utf-8").split("\n")
    lo, hi = facts["range"]["startLine"], facts["range"]["endLine"]
    end_col = facts["range"].get("endColumn")
    # `open X in` is part of the command but sits above what the range covers
    # in some toolchains; pull it in when the line above ends with ` in`.
    while (
        lo > 1
        and source_lines[lo - 2].rstrip().endswith(" in")
        and KEEP_LOOSE.match(source_lines[lo - 2])
    ):
        lo -= 1
    sliced = source_lines[lo - 1 : hi]
    if end_col is not None and sliced:
        sliced = sliced[:-1] + [sliced[-1][:end_col]]
    original = "\n".join(sliced)
    statement = original

    preamble, namespaces_at_target = file_scoped_preamble(source_lines, lo)

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
        f"open {'.'.join(namespaces_at_target[:i + 1])}"
        for i in range(len(namespaces_at_target))
    ]

    # One header shared by all three Lean files: the statement's text is
    # identical in each, so what it needs to elaborate must be too.
    header = (
        ("\n".join(opens) + "\n" if opens else "")
        + ("\n".join(preamble) + "\n" if preamble else "")
        + ("\n" if opens or preamble else "")
    )
    suffix = ":= by\n  sorry"
    signature = statement.rstrip()
    if signature.endswith(suffix):
        signature = signature[: -len(suffix)].rstrip()

    challenge = (
        f"import {fc_module}\n\n"
        + header
        + "\n\n".join(holes)
        + ("\n\n" if holes else "")
        + statement
        + "\n"
    )

    # The participant's file. The statement sits inside `namespace Submission`
    # so nothing here can collide with, or stand in for, the trusted names.
    submission = (
        f"import {fc_module}\nimport Submission.Helpers\n\n"
        + header
        + "namespace Submission\n\n"
        + "\n\n".join(holes)
        + ("\n\n" if holes else "")
        + statement
        + "\n\n"
        + "end Submission\n"
    )

    # The fixed adapter, lean-eval's shape: it restates the trusted statement
    # and closes it with the Submission theorem, so it fails to compile the
    # moment the submission proves anything else. The participant never edits
    # it, which is what keeps the statement pinned.
    delegated = [
        h.rsplit(":= sorry", 1)[0] + ":= Submission." + hn
        for h, hn in zip(holes, hole_names_of(holes))
    ]
    solution = (
        f"import {fc_module}\nimport Submission\n\n"
        + header
        + "\n\n".join(delegated)
        + ("\n\n" if delegated else "")
        + signature
        + " :=\n  Submission."
        + declared
        + ("".join(" " + a for a in args))
        + "\n"
    )

    mathlib_rev, fc_rev = pins(path.relative_to(ROOT))
    full_name = ".".join(namespaces_at_target + [declared])
    hole_names = hole_names_of(holes)

    workspace_id = slug(manifest.get("id", declared))
    ws = pathlib.Path(out_dir) / workspace_id
    holes_line = (
        "\nFill each definition hole in `Submission.lean` too. Hole answers "
        "also get a\nhuman check, because a hole can be gamed in ways the "
        "comparator cannot see.\nChecking holes needs a comparator built at "
        f"commit `{tool_pins()['comparator'][:8]}`, which\nadded definition "
        "support.\n"
        if holes
        else ""
    )
    manifest_lines = "".join(
        f"- {field.capitalize()}: {' '.join(str(manifest[field]).split())}\n"
        for field in ("source", "notes")
        if manifest.get(field)
    )
    workspace_readme = (
        f"# {workspace_id}\n\n"
        f"A comparator challenge for `{declared}`, generated from\n"
        f"`{path.relative_to(ROOT)}` in google-deepmind/formal-conjectures.\n\n"
        + manifest_lines
        + "\nProve the statement in `Submission.lean`, keeping it as it stands; "
        "put helper\nmodules under `Submission/` if you need them. Do not "
        "modify `Challenge.lean` or\n`Solution.lean`: the trusted statement "
        "lives there, and `Solution.lean` closes it\nwith your `Submission` "
        "theorem, so it fails to compile if the submission proves\nanything "
        "else.\n"
        "\nComparator accepts the workspace only if the statement is proved "
        "under the\naxioms in `config.json`. `sorry` adds `sorryAx`, which is "
        "not permitted, and\nclosing the goal with the imported original "
        "fails the same way, since that is\n`sorry` too. `lake test` runs "
        "comparator, from `PATH` or `COMPARATOR_BIN`.\n"
        "\nIf comparator fails with `incompatible header` on an `.olean`, the "
        "mismatch is\nbetween this workspace's toolchain and the one "
        "`lean4export` was built with,\nnever a problem with the proof: copy "
        "this workspace's `lean-toolchain` into\nyour `lean4export` checkout, "
        "rebuild it, and clear `.lake/build` here.\n"
        + holes_line
        + "\nFetch the Mathlib cache before the first build; a cold build takes "
        "the best\npart of an hour without it:\n\n"
        "    lake exe cache get\n"
        "    lake build\n"
    )
    helper = (
        "import Mathlib\n\n"
        "/-! Helper lemmas for the submission go here, or in further modules\n"
        "under `Submission/`, each imported from `Submission.lean`. -/\n\n"
        "namespace Submission\n\nend Submission\n"
    )
    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [declared],
        "permitted_axioms": PERMITTED_AXIOMS,
        "enable_nanoda": False,
    }
    if hole_names:
        # Comparator's documented no-hole config carries no such field.
        config["definition_names"] = hole_names
    holes_payload = {
        "id": manifest.get("id", declared),
        "module": str(path.relative_to(ROOT)),
        "holes": [
            {
                "name": ".".join(namespaces_at_target + [hn]),
                "basename": hn,
                "kind": "def",
                "body": body_,
            }
            for hn, body_ in zip(hole_names, holes)
        ]
        + [
            {
                "name": full_name,
                "basename": declared,
                "kind": "theorem",
                "body": original,
            }
        ],
    }
    write_workspace(
        ws,
        {
            "lakefile.toml": lakefile(workspace_id, mathlib_rev, fc_rev),
            "lean-toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
            "README.md": workspace_readme,
            "Challenge.lean": challenge,
            "Solution.lean": solution,
            "Submission.lean": submission,
            "Submission/Helpers.lean": helper,
            "WorkspaceTest.lean": (
                COMPARATOR_DIR / "templates" / "WorkspaceTest.lean"
            ).read_text(encoding="utf-8"),
            "config.json": json.dumps(config, indent=2) + "\n",
            "holes.json": json.dumps(holes_payload, indent=2, ensure_ascii=False)
            + "\n",
        },
    )
    return ws


def validate():
    """Check every manifest resolves to exactly one declaration.

    Run this rather than discovering a stale `module` field when someone
    generates the workspace months later.
    """
    bad = 0
    for problem_id in manifest_ids():
        try:
            manifest = load_manifest(problem_id)
            declaration = manifest["declaration"]
            path, _i, _d, _b = find_declaration(declaration, manifest.get("module"))
            elaborator_facts(module_name(path.relative_to(ROOT)), declaration)
        except SystemExit as exc:
            print(f"{problem_id}: {exc}", file=sys.stderr)
            bad += 1
            continue
        print(f"{problem_id}: {declaration} in {path.relative_to(ROOT)}")
    if bad:
        print(f"{bad} manifest(s) do not resolve", file=sys.stderr)
    return 1 if bad else 0


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "declaration",
        nargs="?",
        help="a manifest id, or a declaration name such as erdos_940",
    )
    ap.add_argument("--out", default=str(ROOT / ".comparator"))
    ap.add_argument(
        "--answer-type",
        default=None,
        help="type of a non-Prop answer(sorry) slot; "
        "the manifest's `answer_type` is used when absent",
    )
    ap.add_argument(
        "--module",
        default=None,
        help="the file declaring it, when more than one does; "
        "overrides the manifest's `module`",
    )
    ap.add_argument(
        "--validate",
        action="store_true",
        help="check every manifest resolves, and generate nothing",
    )
    args = ap.parse_args(argv)
    if args.validate:
        return validate()
    if not args.declaration:
        ap.error("give a declaration, or --validate")
    ws = generate(args.declaration, args.out, args.answer_type, args.module)
    print(ws)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
