#!/usr/bin/env python3
"""The one interface between the Formal Conjectures importer and the generator.

`leanprover/lean-eval#536` splits this work in two, and the generator half now
exists: `leanprover/lean-eval-generator` is a deterministic Lean CLI with a
versioned JSON contract, pinned in `comparator/tools.toml`. The consumer sends
one request on stdin — target pins, templates, and per problem a Lean module
with resolved hole ranges — and receives the complete workspace file map with
a SHA-256 digest per file. The Formal Conjectures side owns an importer that
maps FC declarations and metadata to that request. The FC importer does not
fork the generation logic.

This module is that seam, and nothing else. It holds the values that cross it
and the code that turns them into contract JSON:

    MarkedUpModule   one Mathlib-only Lean module, in four internal regions
    ProblemManifest  the facts about the problem that the module's text does
                     not carry, including the FC source commit and the FC
                     declaration id; written beside the generated workspace
                     as `fc-provenance.json`, because the schema-version-1 contract has no
                     provenance fields of its own
    build_request    (module, manifest) pairs -> the schema-version-1 request object
    parse_response   response text -> file maps, digests checked

`comparator/adapter/fc_leaneval_importer.py` produces the pairs.
`comparator/adapter/leaneval_generator_cli.py` runs the pinned binary. Nothing on the FC
side decides a workspace file's contents any more.

## Why one module rather than a bag of strings

The generator's job includes the import and scope fidelity work from
lean-eval#531: deciding which generated file imports which, and where the
file-scoped `open`, `variable` and notation have to be restated so that the
same statement text elaborates in Challenge, Submission and Solution alike.
That decision belongs to the generator, so the importer must not pre-split the
source. It emits one module that elaborates on its own against Mathlib, and
the generator slices it by the hole ranges the request carries.

Emitting one module also gives the importer a check it could not otherwise
have: the module it is about to hand over is exactly the text it can elaborate
locally (`--verify`), so a copied closure that has lost an `open` fails on the
FC side rather than in lean-eval's CI. For the same reason the module carries
no `@[eval_problem]` markers: that attribute does not exist outside lean-eval,
and the ranges in the request already say where the holes are.

The regions, in the order they are rendered:

    dependencies  the FC-local closure of the statement, copied, Mathlib-only
    scope         the `open` and file-scoped directives the statement needs
    holes         one `noncomputable def <name> : <type> := sorry` per
                  `answer(sorry)` slot the importer hoisted
    statement     the target statement, its proof replaced by `sorry`

The regions are an internal structure. What crosses the seam is the rendered
module inside the request, byte for byte.
"""

import dataclasses
import hashlib
import json
import re

REGIONS = ("dependencies", "scope", "holes", "statement")

MODULE_PREAMBLE = "import Mathlib\n"

MANIFEST_SCHEMA_VERSION = 1


def sha256_text(text):
    """The digest the generator response uses: SHA-256 of the UTF-8 bytes."""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def dump_json(obj, sort_keys=False):
    """The one JSON serialisation every artifact here uses: readable, UTF-8, newline-terminated."""
    return json.dumps(obj, indent=2, ensure_ascii=False, sort_keys=sort_keys) + "\n"

# The generator's frozen wire format; `schemas/request-v1.schema.json` and
# `response-v1.schema.json` in the pinned revision are normative.
CONTRACT_VERSION = 1


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


@dataclasses.dataclass(frozen=True)
class SourceRecord:
    """Where the marked-up module's text came from.

    lean-eval#536 requires that each manifest record the FC source commit and
    declaration id. Neither is recoverable from the Lean text, and neither is
    something the generator can supply: the generator sees a module, not a
    repository. So they cross the seam here, and the generator's only duty is
    to carry them into the workspace unaltered.

    `lean_toolchain` and `mathlib_revision` are Formal Conjectures' own, and
    are not the pins the workspace is built with. They are here because the
    hole types in the manifest were read from an environment elaborated at
    them, so a reader comparing them with `TargetRecord` can see whether the
    types were read where they will be used.
    """

    repository: str
    commit: str
    path: str
    blob_sha: str
    module: str
    declaration: str
    copied_dependencies: tuple
    original_declaration: str
    lean_toolchain: str
    mathlib_revision: str


@dataclasses.dataclass(frozen=True)
class TargetRecord:
    """The pins a generated workspace is built and checked with.

    These belong to whoever consumes the generator: lean-eval#536 says
    LeanEval "remains the trusted statement repository and supplies the pin
    regime and CI". So they are an argument to `generate`, not a field of the
    manifest — a manifest carrying them would be Formal Conjectures asserting
    another repository's regime, and would go stale the moment that repository
    bumped anything, with nothing here to notice.

    Formal Conjectures keeps the full pin set under `[target]` in
    `comparator/tools.toml`; this record carries only the two fields the schema-version-1
    request consumes. The comparator and lean4export pins are read from the
    TOML directly by the CI job that runs them.
    """

    lean_toolchain: str
    mathlib_revision: str


@dataclasses.dataclass(frozen=True)
class ProblemManifest:
    """What the marked-up module's text does not say.

    `theorem` is the statement's own unqualified name, which the generator
    needs for the Solution adapter, and `qualified_theorem` is that name under
    the namespace the scope region reopens, which is what Comparator checks.
    `apply_arguments` are the statement's explicit declaration parameters, in
    order: the Solution adapter applies them by name, and `∀` binders in the
    conclusion are not among them.
    """

    id: str
    theorem: str
    qualified_theorem: str
    apply_arguments: tuple
    holes: tuple
    permitted_axioms: tuple
    source: SourceRecord
    source_url: str = ""
    # The `@[category ...]` tag as the source spells it: `research open`,
    # `research solved`, `textbook` or `test`. lean-eval keeps open
    # conjectures out of its evaluation set, so which group a problem joins
    # is decided by this and nothing else; recording the raw tag rather than
    # the mapped group keeps the mapping in one place, beside the request.
    category: str = ""
    # Digests bind the record to bytes: the exact `moduleContent` that crossed
    # the seam, and every generated file the response returned for it. With
    # them a workspace carries its own chain — FC commit → module bytes →
    # generated bytes — and a reader can check each link without this
    # repository. The sidecar is the schema-version-1 provenance boundary by design
    # (lean-eval-generator keeps its wire format frozen), so it has to be
    # strict and deterministic as well: unknown keys are refused on load and
    # serialisation is key-sorted.
    module_sha256: str = ""
    file_sha256: tuple = ()

    def with_digests(self, module_sha256, files):
        """The same manifest, bound to the module bytes and generated files."""
        return dataclasses.replace(
            self,
            module_sha256=module_sha256,
            file_sha256=tuple(sorted((path, digest) for path, digest in files.items())),
        )

    def __post_init__(self):
        for field in ("id", "theorem", "qualified_theorem"):
            if not getattr(self, field):
                raise SystemExit(f"manifest has no {field}")
        # lean-eval#536 names these two explicitly, and a manifest without
        # them cannot be traced back to a revision of this repository or
        # regenerated when FC fixes a misformalisation upstream.
        if not self.source.commit:
            raise SystemExit(f"manifest {self.id} records no FC source commit")
        if not self.source.declaration:
            raise SystemExit(f"manifest {self.id} records no FC declaration id")

    def hole_names(self):
        return [hole.name for hole in self.holes]

    def to_json_object(self):
        payload = {
            "schema_version": MANIFEST_SCHEMA_VERSION,
            "id": self.id,
            "theorem": self.theorem,
            "qualified_theorem": self.qualified_theorem,
            "category": self.category,
            "apply_arguments": list(self.apply_arguments),
            "holes": [dataclasses.asdict(hole) for hole in self.holes],
            "permitted_axioms": list(self.permitted_axioms),
            "source": {
                **dataclasses.asdict(self.source),
                "copied_dependencies": list(self.source.copied_dependencies),
            },
        }
        if self.source_url:
            payload["source_url"] = self.source_url
        if self.module_sha256:
            payload["digests"] = {
                "module": self.module_sha256,
                "files": dict(self.file_sha256),
            }
        return payload

    KNOWN_KEYS = frozenset(
        {
            "schema_version", "id", "theorem", "qualified_theorem", "category",
            "apply_arguments", "holes", "permitted_axioms", "source",
            "source_url", "digests",
        }
    )

    @classmethod
    def from_json_object(cls, payload):
        version = payload.get("schema_version")
        if version != MANIFEST_SCHEMA_VERSION:
            raise SystemExit(
                f"manifest schema version {version!r} is not "
                f"{MANIFEST_SCHEMA_VERSION}"
            )
        unknown = sorted(set(payload) - cls.KNOWN_KEYS)
        if unknown:
            raise SystemExit(f"provenance record has unknown keys: {', '.join(unknown)}")
        source = dict(payload["source"])
        source["copied_dependencies"] = tuple(source["copied_dependencies"])
        unknown = sorted(set(source) - {f.name for f in dataclasses.fields(SourceRecord)})
        if unknown:
            raise SystemExit(f"provenance source has unknown keys: {', '.join(unknown)}")
        digests = dict(payload.get("digests", {}))
        unknown = sorted(set(digests) - {"module", "files"})
        if unknown:
            raise SystemExit(f"provenance digests have unknown keys: {', '.join(unknown)}")
        return cls(
            id=payload["id"],
            theorem=payload["theorem"],
            qualified_theorem=payload["qualified_theorem"],
            apply_arguments=tuple(payload["apply_arguments"]),
            holes=tuple(DefinitionHole(**hole) for hole in payload["holes"]),
            permitted_axioms=tuple(payload["permitted_axioms"]),
            source=SourceRecord(**source),
            source_url=payload.get("source_url", ""),
            category=payload.get("category", ""),
            module_sha256=digests.get("module", ""),
            file_sha256=tuple(sorted(dict(digests.get("files", {})).items())),
        )

    def to_json(self):
        # Key-sorted: the same record always serialises to the same bytes.
        return dump_json(self.to_json_object(), sort_keys=True)

    @classmethod
    def from_json(cls, text):
        return cls.from_json_object(json.loads(text))


@dataclasses.dataclass(frozen=True)
class MarkedUpModule:
    """One Mathlib-only Lean module, in the four labelled regions.

    `dependency_declarations` names each copied declaration and the exact
    text the dependencies region carries for it, in order. The contract wants
    a source span per declaration, and only the renderer knows which bytes
    belong to which copied name.
    """

    dependencies: str
    scope: str
    holes: str
    statement: str
    dependency_declarations: tuple = ()

    def __post_init__(self):
        # Rendering separates the regions itself, so leading and trailing
        # blank lines are not part of a region's content.
        for name in REGIONS:
            object.__setattr__(self, name, getattr(self, name).strip("\n"))

    def regions(self):
        return {name: getattr(self, name) for name in REGIONS}

    def render(self):
        """The module as handed over: plain Lean, no markers of any kind."""
        parts = [MODULE_PREAMBLE]
        for body in self.regions().values():
            body = body.strip("\n")
            if body:
                parts.append("\n" + body + "\n")
        return "".join(parts)


# The `@[category ...]` tags that name a problem, and the lean-eval group
# each belongs to. `research open` is the point of the FC import and goes to
# the open-conjectures display; everything already settled — solved research,
# textbook and test statements — is evaluation material. `API` declarations
# and untagged ones are not problems and are refused.
CATEGORY_GROUPS = {
    "research open": "open-conjectures",
    "research solved": "formalization-evaluation",
    "textbook": "formalization-evaluation",
    "test": "formalization-evaluation",
}


def problem_group(manifest):
    """The lean-eval problem group for an imported declaration's category."""
    group = CATEGORY_GROUPS.get(manifest.category)
    if group is None:
        raise SystemExit(
            f"{manifest.id}: category {manifest.category!r} is not a "
            "problem category; expected one of "
            + ", ".join(sorted(CATEGORY_GROUPS))
        )
    return group


MATHLIB_GIT = "https://github.com/leanprover-community/mathlib4.git"

SUBMITTER = "formal-conjectures-importer"


def module_declarations(marked_up, manifest):
    """Every declaration in the rendered module, in order.

    Returns `(name, body, kind, explicit_parameters)` tuples: the copied
    dependencies first, then the hoisted answer holes, then the statement.
    The generator needs a span for each — holes to slice, dependencies to
    keep or drop per generated file — and the bodies are what the spans are
    computed from.
    """
    declarations = [
        (name, body, "helper", None)
        for name, body in marked_up.dependency_declarations
    ]
    declarations += [
        (hole.name, hole.declaration(), "def", None) for hole in manifest.holes
    ]
    # `open X in` prefix lines travel inside the statement slice, but the
    # span the generator receives must start at the declaration keyword:
    # the generator re-attaches whatever sits between the previous span and
    # this one as the declaration's prefix, and a prefix hidden inside the
    # span would be dropped from the reconstructed files.
    statement = marked_up.statement
    lines = statement.split("\n")
    start = 0
    while start < len(lines) - 1 and lines[start].rstrip().endswith(" in"):
        start += 1
    declarations.append(
        (
            manifest.theorem,
            "\n".join(lines[start:]),
            "theorem",
            list(manifest.apply_arguments),
        )
    )
    return declarations


def _positions(text):
    """Codepoint offset of the start of each 1-indexed line."""
    starts = [0]
    for line in text.split("\n")[:-1]:
        starts.append(starts[-1] + len(line) + 1)
    return starts


def _utf16_column(line_text, column):
    """The UTF-16 code-unit column for a codepoint column.

    `.ilean` files store LSP ranges, and LSP counts UTF-16 code units; a
    supplementary-plane character (𝔽, 𝕜) earlier in the line makes the two
    disagree.
    """
    return sum(2 if ord(c) > 0xFFFF else 1 for c in line_text[:column])


def declaration_spans(module_text, declarations):
    """A source span for each declaration, located by its exact text.

    The renderer wrote every declaration into the module verbatim, so each
    body appears in the text; a body appearing more than once would make the
    span a guess, and is refused. Lines are 1-indexed. `codepoint` columns
    are what the contract's `resolvedHoles` carry; `utf16` columns are what
    an `.ilean` carries.
    """
    line_starts = _positions(module_text)
    lines = module_text.split("\n")

    def line_of(offset):
        low, high = 0, len(line_starts) - 1
        while low < high:
            mid = (low + high + 1) // 2
            if line_starts[mid] <= offset:
                low = mid
            else:
                high = mid - 1
        return low

    spans = []
    for name, body, kind, explicit in declarations:
        body = body.strip("\n")
        first = module_text.find(body)
        if first < 0:
            raise SystemExit(f"{name}: declaration text not found in the module")
        if module_text.find(body, first + 1) >= 0:
            raise SystemExit(
                f"{name}: declaration text appears more than once in the module"
            )
        end = first + len(body)
        start_line, end_line = line_of(first), line_of(end)
        start_col = first - line_starts[start_line]
        end_col = end - line_starts[end_line]
        spans.append(
            {
                "name": name,
                "kind": kind,
                "explicitParameters": explicit,
                "startLine": start_line + 1,
                "startColumn": start_col,
                "endLine": end_line + 1,
                "endColumn": end_col,
                "utf16StartColumn": _utf16_column(lines[start_line], start_col),
                "utf16EndColumn": _utf16_column(lines[end_line], end_col),
            }
        )
    return spans


def build_problem(marked_up, manifest, module_name=None, group=None):
    """One problem entry of the schema-version-1 request, and its `.ilean` declaration map.

    The module name is a single identifier on purpose: the generator resolves
    module names to paths by splitting on every dot, guillemets included, so
    a dotted or quoted name would trip the same decoder defect this
    repository fixed on its own side.

    `group` overrides the category-derived group for members of a frozen
    set: the set decides the display tab, because the list is immutable
    while its members keep getting solved, and the category rides along as
    a tag. The category is still validated either way — a declaration that
    is not a problem has no business in any group.

    Returns `(problem, ilean_decls)`. The `.ilean` payload exists because the
    generator reads helper-declaration spans from compiled metadata it
    expects to find under the context root; this consumer synthesises that
    metadata from the spans it computed, which it can do exactly because it
    rendered the module.
    """
    module_name = module_name or slug(manifest.id)
    text = marked_up.render()
    spans = declaration_spans(text, module_declarations(marked_up, manifest))
    resolved, ilean = [], {}
    for span in spans:
        # `.ilean` lines are 0-indexed; `loadIleanDeclRanges` adds one back.
        ilean[span["name"]] = [
            span["startLine"] - 1,
            span["utf16StartColumn"],
            span["endLine"] - 1,
            span["utf16EndColumn"],
        ]
        if span["kind"] == "helper":
            continue
        resolved.append(
            {
                "declarationName": span["name"],
                "module": module_name,
                "startLine": span["startLine"],
                "startColumn": span["startColumn"],
                "endLine": span["endLine"],
                "endColumn": span["endColumn"],
                "explicitParameters": span["explicitParameters"],
                "sameModuleDependencies": (
                    [name for name, _ in marked_up.dependency_declarations]
                    if span["kind"] == "theorem"
                    else []
                ),
                "holeDependentDependencies": [],
                "kind": span["kind"],
            }
        )
    category_group = problem_group(manifest)
    problem = {
        "id": slug(manifest.id),
        "title": manifest.qualified_theorem,
        "group": group or category_group,
        "status": "draft",
        "visible": True,
        "statementRevision": 1,
        "tags": ["formal-conjectures", manifest.category.replace(" ", "-")],
        "moduleName": module_name,
        "holes": [entry["declarationName"] for entry in resolved],
        "submitter": SUBMITTER,
        "notes": None,
        "source": manifest.source_url or None,
        "informalSolution": None,
        "moduleContent": text,
        "resolvedHoles": resolved,
    }
    return problem, ilean


def build_request(problems, target, workspace_test, context_root):
    """The complete schema-version-1 request for a batch of `(problem, ilean)` pairs.

    `problems` are the entries `build_problem` returned; the ilean halves go
    to whoever writes the context root, not into the request. Ids must be
    unique across the batch — two problems generating into one directory is
    the collision the qualified default id exists to prevent.
    """
    seen = set()
    for problem in problems:
        if problem["id"] in seen:
            raise SystemExit(f"duplicate workspace id {problem['id']!r}")
        seen.add(problem["id"])
    return {
        "schemaVersion": CONTRACT_VERSION,
        "contextRoot": str(context_root),
        "leanToolchain": target.lean_toolchain,
        "mathlib": {
            "name": "mathlib",
            "git": MATHLIB_GIT,
            "rev": target.mathlib_revision,
        },
        "templates": {"workspaceTest": workspace_test},
        "problems": problems,
    }


def parse_response(text):
    """The generator's file maps, with every digest checked.

    Returns `{problem_id: {path: content}}`. A digest mismatch means the
    bytes were damaged in transit or the pinned generator is not the one
    this code was written against; either way the workspace cannot be
    trusted, so refuse.
    """
    payload = json.loads(text)
    version = payload.get("schemaVersion")
    if version != CONTRACT_VERSION:
        raise SystemExit(
            f"generator response schema version {version!r} is not {CONTRACT_VERSION}"
        )
    workspaces = {}
    for entry in payload["files"]:
        if sha256_text(entry["content"]) != entry["sha256"]:
            raise SystemExit(
                f"{entry['problemId']}/{entry['path']}: content does not match "
                "its digest"
            )
        files = workspaces.setdefault(entry["problemId"], {})
        if entry["path"] in files:
            raise SystemExit(
                f"{entry['problemId']}/{entry['path']}: appears twice in response"
            )
        files[entry["path"]] = entry["content"]
    return workspaces
