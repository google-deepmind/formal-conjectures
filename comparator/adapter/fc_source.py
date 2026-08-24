#!/usr/bin/env python3
"""Reading Formal Conjectures source.

Everything here answers questions about this repository's own Lean files:
where a declaration is, which file-scoped directives were in force where it
was written, which FC-defined notation it uses, where its `answer(sorry)`
slots are and what types the elaborated environment gives them, and which
pins the text was read at. Nothing here knows what a workspace, a request or
a manifest is; `fc_leaneval_importer.py` assembles those from these answers.
"""


import dataclasses
import functools
import json
import pathlib
import re
import subprocess


def slug(name):
    """A Lake package name and directory name for a problem id.

    A Lake package name is an identifier, so the dots in a qualified
    declaration cannot go into one verbatim.
    """
    return re.sub(r"[^0-9A-Za-z_]", "_", name)


@dataclasses.dataclass(frozen=True)
class DefinitionHole:
    """One `answer(sorry)` slot, hoisted into a definition the solver fills.

    `name` is the unqualified definition name as it appears in the module's
    `holes` region; `type` is the type the elaborated environment reported for
    the slot, which surface syntax does not carry.
    """

    name: str
    type: str

    def declaration(self):
        return f"noncomputable def {self.name} : {self.type} := sorry"


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
    r"|omit|include"
    r"|notation|postfix|prefix|infixl|infixr|infix|macro|syntax|macro_rules)\b"
    r"|^noncomputable section\b"
)

@dataclasses.dataclass(frozen=True)
class FactsRecord:
    """One declaration's elaborator facts, held to the payload the extractor emits.

    The fourth JSON boundary in the adapter, made as strict as the other
    three: the provenance sidecar, the problem files and the failure ledger
    all refuse keys nothing reads, and the extractor payload now does too, so
    a drift between `comparator_facts` and this side fails at the seam
    instead of surfacing as a missing default somewhere downstream.
    """

    declaration: str
    name: str
    category: str
    range: dict
    binders: tuple
    answer_types: tuple
    dependencies: tuple
    generated_dependencies: tuple

    PAYLOAD_KEYS = frozenset(
        {
            "declaration",
            "name",
            "category",
            "range",
            "binders",
            "answerTypes",
            "dependencies",
            "generatedDependencies",
        }
    )
    BINDER_KEYS = frozenset({"name", "explicit"})
    DEPENDENCY_KEYS = frozenset({"name", "module", "range"})

    @classmethod
    def from_payload(cls, payload, declaration):
        unknown = sorted(set(payload) - cls.PAYLOAD_KEYS)
        missing = sorted(cls.PAYLOAD_KEYS - set(payload))
        if unknown or missing:
            raise SystemExit(
                f"comparator_facts {declaration}: payload keys do not match the "
                f"wire format (unknown: {unknown or 'none'}, "
                f"missing: {missing or 'none'})"
            )
        for binder in payload["binders"]:
            if set(binder) != cls.BINDER_KEYS:
                raise SystemExit(
                    f"comparator_facts {declaration}: malformed binder {binder}"
                )
        for dep in payload["dependencies"]:
            if set(dep) != cls.DEPENDENCY_KEYS:
                raise SystemExit(
                    f"comparator_facts {declaration}: malformed dependency {dep}"
                )
        return cls(
            declaration=payload["declaration"],
            name=payload["name"],
            category=payload["category"],
            range=payload["range"],
            binders=tuple(payload["binders"]),
            answer_types=tuple(payload["answerTypes"]),
            dependencies=tuple(payload["dependencies"]),
            generated_dependencies=tuple(payload["generatedDependencies"]),
        )


_FACTS_CACHE = {}


def prefetch_elaborator_facts(pairs):
    """Fill the facts cache from one batched extractor run.

    `pairs` are `(module, declaration)` tuples. The Mathlib import dominates
    a `comparator_facts` launch, so a batch pays it once for the whole set.
    A pair the batch reports an error for is left out of the cache: the
    caller's own `elaborator_facts` call re-runs it singly and fails with
    exactly the message a single run always produced.
    """
    wanted = [pair for pair in dict.fromkeys(pairs) if pair not in _FACTS_CACHE]
    if not wanted:
        return
    try:
        proc = subprocess.run(
            ["lake", "exe", "comparator_facts", "--batch"],
            input="".join(
                json.dumps({"module": module, "declaration": declaration}) + "\n"
                for module, declaration in wanted
            ),
            capture_output=True,
            text=True,
            cwd=ROOT,
            # Generous: a cold run imports Mathlib and may build the
            # extractor first. A hang should end the run, not the day.
            timeout=1800 + 30 * len(wanted),
        )
    except subprocess.TimeoutExpired:
        # The batch is an optimisation; the per-declaration path is the
        # arbiter of what fails and how it is reported.
        return
    if proc.returncode != 0:
        return
    requested = set(wanted)
    for line in proc.stdout.splitlines():
        if not line.startswith("{"):
            # `lake` progress lines share stdout with the payload; anything
            # non-JSON is theirs. Error entries are also left uncached, so
            # the single re-run reproduces the exact message.
            continue
        entry = json.loads(line)
        key = (entry["module"], entry["declaration"])
        if key not in requested:
            raise SystemExit(
                f"comparator_facts --batch answered for {key[1]} in {key[0]}, "
                "which nothing asked about"
            )
        if "facts" in entry:
            _FACTS_CACHE[key] = entry["facts"]


def elaborator_facts(module, declaration):
    """What the elaborated environment knows about a declaration.

    Runs `lake exe comparator_facts`, which imports the module and reports the
    declaration's source range, its binders with real explicitness, and the
    inferred type of each `answer(sorry)` slot. Every one of these used to be
    reconstructed from text, and each reconstruction had failure modes the
    elaborator does not. A batch import fills `_FACTS_CACHE` first, so a set
    run pays the Mathlib import once.
    """
    cached = _FACTS_CACHE.get((module, declaration))
    if cached is not None:
        return FactsRecord.from_payload(cached, declaration)
    try:
        proc = subprocess.run(
            ["lake", "exe", "comparator_facts", module, declaration],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=1800,
        )
    except subprocess.TimeoutExpired:
        raise SystemExit(
            f"comparator_facts {declaration}: no answer within 30 minutes"
        ) from None
    if proc.returncode != 0:
        raise SystemExit(
            f"comparator_facts {declaration}: "
            f"{proc.stderr.strip() or proc.stdout.strip()}"
        )
    out = proc.stdout
    if "{" not in out:
        raise SystemExit(f"comparator_facts {declaration}: no JSON in output")
    return FactsRecord.from_payload(json.loads(out[out.index("{") :]), declaration)

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
        code = line
        if depth == 0:
            # A `/-` inside a string or after `--` is not a comment opener;
            # inside an open block comment the raw line is what counts.
            code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', code)
            # `--` opens a line comment unless it is the tail of the
            # doc-comment opener `/--`.
            m = re.search(r"(?<!/)--", code)
            if m:
                code = code[: m.start()]
        depth += len(re.findall(r"/-", code)) - len(re.findall(r"-/", code))
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

    Module docstrings carry a `*Reference:*` or `*References:*` line naming
    where the problem comes from, sometimes with several links under it. The
    first is the problem's own; later ones are commentary and proof notes.
    """
    if not module_doc:
        return ""
    marker = re.search(r"\*References?:\*", module_doc)
    if not marker:
        return ""
    link = re.search(r"\]\((https?://[^)\s]+)\)", module_doc[marker.end() :])
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

@functools.lru_cache(maxsize=1)
def _declared_names():
    """Every `theorem`/`lemma` name token in the tree, one pass, cached.

    `{path: [name, ...]}` in sorted path order. A batch import looks up
    hundreds of declarations; one scan of the tree replaces a full rglob and
    re-read per lookup.
    """
    token = re.compile(r"(?:theorem|lemma)\s+([\w.«»]+)[\s:]")
    index = {}
    for src in SOURCE_DIRS:
        for path in sorted(src.rglob("*.lean")):
            index[path] = token.findall(path.read_text(encoding="utf-8"))
    return index


def _declaring_files(name):
    r"""The files whose text declares `name` as a theorem or lemma.

    A declared token matches when it equals `name` or ends in `.name` —
    the same reading as the old per-file regex, whose optional prefix was
    `[\w.«»]*\.` over the identical character class.
    """
    dotted = "." + name
    return [
        path
        for path, names in _declared_names().items()
        if any(t == name or t.endswith(dotted) for t in names)
    ]

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
    # An attribute line that emptied out leaves a blank line behind; other
    # blank lines are content — a multi-line string may contain one.
    return re.sub(r"^[ \t]*\n", "", text, count=1) if text != block_text else text

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

    Returns `[(tokens, command, scope, shared, path)]`, where `tokens` are
    the command's distinctive string literals, `scope` is the namespace a
    `scoped` command needs restated around it, and `path` is the defining
    file relative to ROOT — a copied command's text is a read source input,
    so the snapshot check needs to know where it came from.
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
                # A command's distinctive tokens decide whether a module
                # uses it: `J(` or `α(` says something, the closing `")"`
                # matches every text. So delimiter-only literals are dropped,
                # while ASCII tokens with letters stay candidates — the old
                # non-ASCII rule hid `J(`, `L(` and `e` from the shared
                # library and their consumers failed to elaborate.
                tokens = [
                    token
                    for token in re.findall(r'"([^"]+)"', command)
                    if any(c.isalnum() or ord(c) > 127 for c in token)
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
                commands.append(
                    (tokens, command, scope, shared, path.relative_to(ROOT))
                )
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

    Returns `[(block, path)]`: each copyable block with the file it was read
    from, so the caller can hold that file to the source pin.
    """
    combined = "\n".join(module_texts)
    blocks, seen = [], set()
    for tokens, command, scope, shared, path in fc_notation_commands():
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
        blocks.append((command, path))
    return blocks

def flatten_declared_name(declared, statement):
    """Restate a dotted declaration name as its slug, in the statement text.

    Returns `(new_name, new_statement)`. Only the declaring occurrence is
    rewritten — a statement does not reference its own name — and the
    rewrite is refused rather than guessed if the name cannot be found where
    the declaration keyword put it.
    """
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
    """Cut the proof body after the top-level `:=`, keeping the statement.

    Only a `:=` at bracket depth zero can start the proof: an autoParam
    binder default `(h : Fact P := by norm_num)` and a structure literal
    `{ a := b }` both live inside brackets and are statement text. A tactic
    proof is the first top-level `:= by`; a term proof leaves a bare
    top-level `:=`, and with more than one of those the importer refuses,
    as everywhere else it cannot decide.
    """
    openers = "([{⟨"
    closers = ")]}⟩"
    depth = 0
    assigns = []
    i = 0
    while i < len(text):
        i, _ = _next_code(text, i)
        if i >= len(text):
            break
        char = text[i]
        if char in openers:
            depth += 1
        elif char in closers:
            depth = max(depth - 1, 0)
        elif depth == 0 and text.startswith(":=", i):
            j = i + 2
            while j < len(text) and text[j].isspace():
                j += 1
            tactic = text.startswith("by", j) and (
                j + 2 >= len(text)
                or not (text[j + 2].isalnum() or text[j + 2] in "_'")
            )
            if tactic:
                return text[: i].rstrip() + " := by\n  sorry"
            assigns.append(i)
            i = j
            continue
        i += 1
    if len(assigns) > 1:
        raise SystemExit(
            "the declaration has a term-mode proof and more than one "
            "top-level `:=`, so the start of the proof cannot be read off "
            "the text"
        )
    if assigns:
        return text[: assigns[0]].rstrip() + " := by\n  sorry"
    return text.rstrip() + " := by\n  sorry"

def _next_code(text, i):
    """The first index at or after `i` holding code, skipping comments and strings.

    Whenever the scan is at code, the lexical state is empty by construction,
    so no state threads between calls. Returns `(index, unterminated)`, with
    `index == len(text)` at the end and `unterminated` reporting a comment or
    string still open there.
    """
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
        return i, False
    return i, bool(block_depth or in_string)


def answer_spans(text):
    """Return the source spans of syntactic `answer(...)` calls.

    This small lexer skips strings and nested line/block comments and balances
    parentheses, so an answer term may itself contain parentheses. It is not a
    Lean parser; malformed or unterminated syntax is refused.
    """
    spans = []
    i = 0
    while i < len(text):
        i, unterminated = _next_code(text, i)
        if i >= len(text):
            if unterminated:
                raise SystemExit(
                    "unterminated comment or string while reading answers"
                )
            break
        if text.startswith("answer", i) and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")
        ):
            j = i + len("answer")
            while j < len(text) and text[j].isspace():
                j += 1
            if j < len(text) and text[j] == "(":
                depth = 1
                k = j + 1
                while k < len(text) and depth:
                    k, _ = _next_code(text, k)
                    if k >= len(text):
                        break
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
    slot means `Prop`) survives only as the `--answer-type` override. Unascribed slots of differing types are
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
        if not remaining:
            # Every slot stated its own type. An environment entry that
            # survived is one of those same slots spelled the way the
            # elaborator prints types, not an extra slot to place.
            pass
        elif missing == len(remaining):
            for i in remaining:
                types[i] = "Prop"
        elif missing == 0 and remaining and len(set(remaining_env)) == 1:
            for i in remaining:
                types[i] = remaining_env[0]
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

@functools.lru_cache(maxsize=1)
def _base_pins():
    """The Mathlib revision and the FC merge-base, invariant for one run.

    Only the per-path dirty check in `pins` varies between calls, so the
    subprocess and manifest parse run once per batch rather than once per
    declaration.
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
    return mathlib_rev, merge_base.stdout.strip()


def pins(source_paths=None):
    """Revisions the workspace's own build can actually fetch.

    The FC pin must be reachable from the upstream repository the lakefile
    names, so it is the merge-base with `origin/main`, not HEAD: a local
    branch commit would generate a workspace whose build fails at fetch time.
    The importer stops if any file it read differs from that revision —
    `source_paths` is every file whose text reached the workspace, not just
    the statement's own — so the record names one revision and the copied
    text all comes from it. A path the revision does not track fails too:
    `git diff` is silent about untracked files, so tracking is checked first.
    """
    mathlib_rev, fc_rev = _base_pins()
    if source_paths is not None:
        if isinstance(source_paths, (str, pathlib.Path)):
            source_paths = [source_paths]
        paths = sorted({str(path) for path in source_paths})
        tracked = subprocess.run(
            ["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", fc_rev, "--"]
            + paths,
            capture_output=True,
            text=True,
        )
        if tracked.returncode != 0:
            raise SystemExit(f"cannot list {fc_rev[:12]}: {tracked.stderr.strip()}")
        missing = sorted(set(paths) - set(tracked.stdout.split("\n")))
        if missing:
            raise SystemExit(
                f"{', '.join(missing)}: not tracked at pinned revision "
                f"{fc_rev[:12]}; land the source on upstream main before "
                "generating"
            )
        comparison = subprocess.run(
            ["git", "-C", str(ROOT), "diff", "--quiet", fc_rev, "--"] + paths
        )
        if comparison.returncode not in (0, 1):
            raise SystemExit(f"cannot compare {', '.join(paths)} with {fc_rev[:12]}")
        if comparison.returncode == 1:
            changed = subprocess.run(
                ["git", "-C", str(ROOT), "diff", "--name-only", fc_rev, "--"] + paths,
                capture_output=True,
                text=True,
            )
            raise SystemExit(
                f"{changed.stdout.strip() or ', '.join(paths)} differs from "
                f"pinned revision {fc_rev[:12]}; land the source on upstream "
                "main before generating"
            )
    return mathlib_rev, fc_rev


def importer_state():
    """The commit this importer ran as, and whether its own files were edited.

    The generated record separates two questions the source pin cannot answer:
    which adapter produced the artifact (HEAD, not the merge-base — the
    adapter itself is allowed to be branch work), and whether that adapter was
    running with uncommitted edits under `comparator/`.
    """
    head = subprocess.run(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
    )
    if head.returncode != 0 or not head.stdout.strip():
        raise SystemExit("cannot resolve the importer's own commit")
    status = subprocess.run(
        ["git", "-C", str(ROOT), "status", "--porcelain", "--", "comparator"],
        capture_output=True,
        text=True,
    )
    return head.stdout.strip(), bool(status.stdout.strip())
