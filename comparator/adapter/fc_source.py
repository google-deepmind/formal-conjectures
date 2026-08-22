#!/usr/bin/env python3
"""Reading Formal Conjectures source.

Everything here answers questions about this repository's own Lean files:
where a declaration is, which file-scoped directives were in force where it
was written, which FC-defined notation it uses, where its `answer(sorry)`
slots are and what types the elaborated environment gives them, and which
pins the text was read at. Nothing here knows what a workspace, a request or
a manifest is; `fc_leaneval_importer.py` assembles those from these answers.
"""


import json
import pathlib
import re
import subprocess

from leaneval_interface import (
    DefinitionHole,
)

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent

SOURCE_DIRS = [ROOT / "FormalConjectures"]

DECL_START = re.compile(
    # `local notation` and `scoped notation` carry the modifier before the
    # keyword. Without them here, Erdos 125's `local notation "A" => ...` typed
    # as nothing and was dropped, and its statements lost the sets they name.
    r"^(?:noncomputable\s+|private\s+|protected\s+|local\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|notation)\s",
)

KEEP_LOOSE = re.compile(
    # `local notation`, `local macro` and friends scope to the file exactly
    # like `open` does, and a statement that names what they define does not
    # parse without them. `noncomputable section` is a section for the scope
    # stack and a compilation mode for everything inside it.
    r"^(?:(?:local|scoped)\s+)?"
    r"(open|variable|universe|section|namespace|end|attribute|set_option"
    r"|notation|postfix|prefix|infixl|infixr|infix|macro|syntax|macro_rules)\b"
    r"|^noncomputable section\b"
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
    the file, so the marked-up module has to restate them; nothing in the
    olean records them. A directive counts only if it precedes the statement
    and its scope still encloses it.
    """
    stack, preamble, depth = [], [], 0
    lines = lines[: start_line - 1]
    index = 0
    while index < len(lines):
        line = lines[index]
        if depth == 0 and KEEP_LOOSE.match(line) and not line.rstrip().endswith(" in"):
            kind = line.split()[0]
            if kind == "noncomputable":
                # `noncomputable section [name]` opens a section.
                kind = "section"
                parts = line.split(None, 2)
                name = parts[2].strip() if len(parts) > 2 else None
            else:
                parts = line.split(None, 1)
                name = parts[1].strip() if len(parts) > 1 else None
            if kind in ("namespace", "section"):
                stack.append((kind, name, line))
            elif kind == "end":
                if stack and (
                    stack[-1][1] == name or (name is None and stack[-1][0] == "section")
                ):
                    stack.pop()
            else:
                # A `macro` or `notation` body may continue on indented
                # lines; a single kept line would be broken syntax.
                text = [line]
                while index + 1 < len(lines) and (
                    lines[index + 1][:1].isspace() and lines[index + 1].strip()
                ):
                    index += 1
                    text.append(lines[index])
                preamble.append(("\n".join(text), list(stack)))
        depth += len(re.findall(r"/-", line)) - len(re.findall(r"-/", line))
        depth = max(depth, 0)
        index += 1
    scope = list(stack)
    in_force = [text for text, s in preamble if s == scope[: len(s)]]
    # A statement inside `noncomputable section` restates the mode, since the
    # copy has left the section behind and a noncomputable definition in the
    # statement's closure would otherwise fail to compile.
    if any(k == "section" and line.startswith("noncomputable") for k, _, line in scope):
        in_force.append("noncomputable section")
    return in_force, [n for k, n, _ in scope if k == "namespace" and n]

def docstring_reference(module_doc):
    """The source citation Formal Conjectures already writes in the module.

    Module docstrings carry a `*Reference:*` line naming where the problem
    comes from, sometimes with several links under it. The first is the
    problem's own; later ones are commentary and proof notes.
    """
    if not module_doc:
        return ""
    after = module_doc.split("*Reference:*", 1)
    if len(after) != 2:
        return ""
    link = re.search(r"\]\((https?://[^)\s]+)\)", after[1])
    return link.group(1) if link else ""

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

def _declaring_files(name):
    """The files whose text declares `name` as a theorem or lemma."""
    pattern = re.compile(
        rf"(?:theorem|lemma)\s+(?:[\w.«»]*\.)?{re.escape(name)}[\s:]"
    )
    hits = []
    for src in SOURCE_DIRS:
        for path in sorted(src.rglob("*.lean")):
            if pattern.search(path.read_text(encoding="utf-8")):
                hits.append(path)
    return hits

def _declares_namespaces(text, components):
    """True if the file opens namespaces spelling out `components` in order.

    A single `namespace A.B` line declares both at once, so the check is on
    the concatenated stack, not line by line. Text-level and approximate on
    purpose — the elaborated environment settles the truth later; this only
    ranks candidate files.
    """
    stack = []
    for line in text.split("\n"):
        m = re.match(r"\s*namespace\s+([\w.«»]+)", line)
        if m:
            stack.extend(m.group(1).split("."))
    return any(
        stack[i : i + len(components)] == list(components)
        for i in range(len(stack) - len(components) + 1)
    )

def find_declaration(basename, module=None):
    """Locate the file declaring `basename`. Returns (path, imports, doc, body).

    A fully qualified name resolves through the enclosing `namespace` stack;
    `module` names the file when more than one declares the name, and comes
    from the problem's FC problem file.
    """
    if module is not None:
        named = ROOT / module
        if not named.exists():
            raise SystemExit(f"manifest names {module}, which does not exist")
        return _read_source(named)
    hits = _declaring_files(basename)
    if not hits and "." in basename:
        # A fully qualified request such as `OeisA303656.conjecture` names a
        # declaration whose file spells only `conjecture`, the prefix coming
        # from an enclosing `namespace`. Try each split of the request into
        # (namespace prefix, declared suffix), keeping files that declare the
        # suffix inside that namespace. Splits are tried longest-suffix first,
        # because a declared name may itself contain dots
        # (`erdos_125.variants.positive_unequal_density`).
        parts = basename.split(".")
        for cut in range(1, len(parts)):
            prefix, suffix = parts[:cut], ".".join(parts[cut:])
            hits = [
                path
                for path in _declaring_files(suffix)
                if _declares_namespaces(path.read_text(encoding="utf-8"), prefix)
            ]
            if hits:
                break
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
    """Return (path, imports, module docstring, body after the licence header).

    The docstring is read but not removed. It sits below the imports rather
    than at the top, so it is found by searching; the body deliberately still
    contains it, because `strip_decorations` removes docstrings per
    declaration and the generated files are compared byte for byte.
    """
    original = path.read_text(encoding="utf-8")
    text = re.sub(r"\A/-.*?-/\s*", "", original, flags=re.DOTALL)
    found = re.search(r"/-!.*?-/", text, flags=re.DOTALL)
    doc = found.group(0) if found else ""
    imports = re.findall(r"^import\s+(\S+)", original, re.MULTILINE)
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

def split_module(module):
    """The components of a dotted module name, respecting guillemet quoting.

    A guillemet-quoted component may itself contain dots —
    `FormalConjectures.Arxiv.«0912.2382».CurlingNumberConjecture` names the
    directory `0912.2382` — so splitting on every dot decodes a path that
    does not exist. This is the one place a module name is taken apart;
    `module_name` is its inverse and a test holds the pair to that.
    """
    parts = re.findall(r"«[^»]*»|[^.«»]+", module)
    if ".".join(parts) != module:
        raise SystemExit(f"{module!r} is not a well-formed module name")
    return [p[1:-1] if p.startswith("«") else p for p in parts]

def module_source_path(module):
    """The file declaring a dotted Lean module name, undoing guillemets."""
    parts = split_module(module)
    # Not `with_suffix`: a final component containing a dot would lose its
    # tail to the suffix replacement.
    path = ROOT.joinpath(*parts[:-1], parts[-1] + ".lean")
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

NOTATION_COMMAND = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:scoped\[[\w.«»]+\]\s+)?(?:scoped\s+)?"
    r"(?:notation[0-9]*|postfix|prefix|infixl|infixr|infix)[:\s]"
)

_NOTATION_CACHE = None

def fc_notation_commands():
    """Every exportable notation command an FC module defines, with its token.

    A notation is not a constant, so the elaborated closure never reports it:
    a statement written as `ℝ²` names `EuclideanSpace ℝ (Fin 2)` in the
    environment and `ℝ²` only in its text. The copy carries the text, so the
    commands that make such tokens parse have to be found at the text layer.
    `local` notations are file-scoped at their origin and cannot be in force
    in a problem file, so they are not candidates.

    Returns `[(tokens, command, namespaces)]`, where `tokens` are the
    command's string literals that contain a non-ASCII character — the
    distinctive ones worth matching on — and `namespaces` is the stack a
    plain `scoped` command needs restated around it.
    """
    global _NOTATION_CACHE
    if _NOTATION_CACHE is not None:
        return _NOTATION_CACHE
    commands = []
    roots = [ROOT / "FormalConjecturesForMathlib", ROOT / "FormalConjecturesUtil"]
    for src in roots + SOURCE_DIRS:
        for path in sorted(src.rglob("*.lean")):
            lines = path.read_text(encoding="utf-8").split("\n")
            for index, line in enumerate(lines):
                if not NOTATION_COMMAND.match(line):
                    continue
                text = [line]
                follow = index + 1
                while follow < len(lines) and (
                    lines[follow][:1].isspace() and lines[follow].strip()
                ):
                    text.append(lines[follow])
                    follow += 1
                command = "\n".join(text)
                tokens = [
                    token
                    for token in re.findall(r'"([^"]+)"', command)
                    if any(ord(c) > 127 for c in token)
                ]
                if not tokens:
                    continue
                bracket = re.match(r"^(?:@\[[^\]]*\]\s*)?scoped\[([\w.«»]+)\]", line)
                if bracket:
                    scope = bracket.group(1)
                elif re.match(r"^scoped\s", line):
                    _, namespaces = file_scoped_preamble(lines, index + 1)
                    scope = ".".join(namespaces)
                else:
                    scope = None
                # A global notation in FormalConjecturesForMathlib or
                # FormalConjecturesUtil is in force in every problem file,
                # which imports both; one in a problem module is not, since
                # problem files do not import each other, and the problem
                # file's own notations travel with the preamble.
                shared = src.name != "FormalConjectures"
                commands.append((tokens, command, scope, shared))
    _NOTATION_CACHE = commands
    return commands

NOTATION_FAMILY = re.compile(r"^(?:notation[0-9]*|postfix|prefix|infixl|infixr|infix)[:\s]")

def localise_notation(preamble):
    """File-scope the preamble's notation commands, with their set_options.

    The generator reconstructs each workspace file's context by re-extracting
    these commands from the module, so a *global* notation ends up declared
    both in `ChallengeDeps` and in the file importing it — two identical
    notations, and every use becomes ambiguous. `local` keeps each copy to
    its own file. A standalone `set_option quotPrecheck false` does not
    survive that reconstruction, so a notation that needs it gets it
    attached as part of its own command.
    """
    precheck_off = any(
        entry.split("\n")[0].strip() == "set_option quotPrecheck false"
        for entry in preamble
    )
    out = []
    for entry in preamble:
        if NOTATION_FAMILY.match(entry):
            entry = "local " + entry
        if precheck_off and re.match(r"^(?:local\s+)?(?:notation|postfix|prefix|infix)", entry):
            entry = "set_option quotPrecheck false in\n" + entry
        out.append(entry)
    return out

def notation_blocks(module_texts, opened):
    """The FC notation commands the module's text uses, as copyable blocks.

    A token match alone over-copies: `⊆` from a modal-logic module matched
    every statement about sets. A scoped notation can only have been in
    force in the source file if its namespace is among the file's opens, so
    `opened` — the namespaces the module's scope and copied preambles open —
    gates every scoped command. A global `notation` in a module nothing
    imports was never in force either, but the corpus keeps global notation
    in the problem file itself, which the preamble already carries, so
    unscoped commands from other files are not candidates at all.
    """
    combined = "\n".join(module_texts)
    blocks, seen = [], set()
    for tokens, command, scope, shared in fc_notation_commands():
        if scope:
            if scope not in opened:
                continue
        elif not shared:
            continue
        if command in seen or command in combined:
            continue
        if not any(token in combined for token in tokens):
            continue
        seen.add(command)
        # A plain `scoped` command needs its namespace restated around it;
        # the bracket form carries its own scope. A global command becomes
        # `local`: the generator re-extracts it into every file that needs
        # it, and a module-crossing global would be declared twice.
        if scope and not command.startswith("scoped["):
            command = f"namespace {scope}\n{command}\nend {scope}"
        elif not scope:
            command = "local " + command
        blocks.append(command)
    return blocks

def flatten_declared_name(declared, statement):
    """Restate a dotted declaration name as its slug, in the statement text.

    Returns `(new_name, new_statement)`. Only the declaring occurrence is
    rewritten — a statement does not reference its own name — and the
    rewrite is refused rather than guessed if the name cannot be found where
    the declaration keyword put it.
    """
    from leaneval_interface import slug

    flattened = slug(declared)
    lines = statement.split("\n")
    for index, line in enumerate(lines):
        match = DECL_START.match(line)
        if not match:
            continue
        name = re.match(r"\s*([\w.«»]+)", line[match.end() :])
        if name and name.group(1) == declared:
            start = match.end() + name.start(1)
            lines[index] = line[:start] + flattened + line[start + len(declared) :]
            return flattened, "\n".join(lines)
    raise SystemExit(f"{declared}: cannot find the declaring occurrence to rename")

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

def _ascribed_type(statement, start, end):
    """The `T` of `(answer(sorry) : T)`, when the slot is written that way.

    A type ascription is the one place the surface syntax states a slot's
    type at its position, and it matters because the elaborated environment
    can lose the annotation for exactly this shape: the ascribed term is
    applied or rewritten during elaboration and the metadata does not
    survive into the stored statement type.
    """
    before = statement[:start].rstrip()
    if not before.endswith("("):
        return None
    index = end
    while index < len(statement) and statement[index].isspace():
        index += 1
    if index >= len(statement) or statement[index] != ":":
        return None
    index += 1
    depth, cursor = 1, index
    while cursor < len(statement):
        char = statement[cursor]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                ascribed = statement[index:cursor].strip()
                return ascribed or None
        cursor += 1
    return None

def hoist_answers(statement, basename, slot_types, override=None):
    """Replace each `answer(sorry)` with a named definition hole.

    A slot written `(answer(sorry) : T)` states its own type at its own
    position, and that reading wins. For the rest, the types come from the
    elaborated environment, where the `answer` elaborator ran with the
    expected type in hand; the old surface-syntax guess (an `↔` beside the
    slot means `Prop`) and the FC problem file's hand-kept `answer_type`
    both survive only as overrides. Unascribed slots of differing types are
    refused: the environment reports the types as a set, and matching them
    to positions would be a guess.
    """
    holes = []
    calls = answer_spans(statement)
    selected = [call for call in calls if call[2].strip() == "sorry"]
    count = len(selected)
    if count == 0:
        return statement, holes
    types = [None] * count
    if override:
        types = [override] * count
    else:
        remaining_env = list(slot_types)
        for i, (start, end, _argument) in enumerate(selected):
            ascribed = _ascribed_type(statement, start, end)
            if ascribed is not None:
                types[i] = ascribed
                # The environment may have reported this slot too; retire one
                # matching entry so the counting below stays honest.
                if ascribed in remaining_env:
                    remaining_env.remove(ascribed)
        remaining = [i for i in range(count) if types[i] is None]
        # Under the default `alwaysTrue` setting, the `answer` elaborator
        # erases a slot to `True` if and only if its expected type is `Prop`
        # (FormalConjecturesUtil/Answer.lean). So a slot the environment
        # carries no annotation for is a `Prop` slot by the elaborator's own
        # rule, not by guesswork, and no postpone build is needed.
        missing = len(remaining) - len(remaining_env)
        if missing == len(remaining):
            for i in remaining:
                types[i] = "Prop"
        elif missing == 0 and remaining and len(set(remaining_env)) == 1:
            for i in remaining:
                types[i] = remaining_env[0]
        elif missing == 0 and not remaining:
            pass
        elif missing == 0:
            raise SystemExit(
                f"{basename} has {len(remaining)} answer slots of differing "
                f"types {remaining_env}; pass --answer-type"
            )
        else:
            # Some slots are Prop and some are not: which positions are which
            # cannot be read off an unordered set, so refuse rather than
            # assign.
            raise SystemExit(
                f"{basename}: {missing} Prop slot(s) and {len(remaining_env)} "
                f"typed slot(s) {remaining_env} cannot be matched to "
                "positions; pass --answer-type"
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
