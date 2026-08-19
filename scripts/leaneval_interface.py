#!/usr/bin/env python3
"""The one interface between the Formal Conjectures importer and the generator.

`leanprover/lean-eval#536` splits this work in two. The generator core inside
lean-eval's `EvalTools` — the part that turns a marked-up Lean module plus a
manifest into a Challenge / Solution / Submission workspace — is being
extracted into `leanprover/lean-eval-generator` and consumed as a pinned
dependency. The Formal Conjectures side owns an importer that maps FC
declarations and metadata to LeanEval modules and manifests. The FC importer
does not fork the generation logic.

This module is that seam, and nothing else. It holds the two values the
importer hands the generator and no code that produces or consumes them:

    MarkedUpModule   one Mathlib-only Lean module, in labelled regions
    ProblemManifest  the facts about the problem that the module's text does
                     not carry, including the FC source commit and the FC
                     declaration id

`scripts/fc_leaneval_importer.py` produces both. `scripts/leaneval_generator.py`
consumes both and returns a workspace. When `lean-eval-generator` lands, the
generator module goes and this file becomes an import from the pinned package;
the importer keeps building the same two values and does not change.

## Why a marked-up module rather than a bag of strings

The generator's job includes the import and scope fidelity work from
lean-eval#531: deciding which generated file imports which, and where the
file-scoped `open`, `variable` and notation have to be restated so that the
same statement text elaborates in Challenge, Submission and Solution alike.
That decision belongs to the generator, so the importer must not pre-split the
source into those files. It emits one module that elaborates on its own
against Mathlib, with the four parts labelled, and the generator slices it.

Emitting one module also gives the importer a check it could not otherwise
have: the module it is about to hand over is exactly the text it can elaborate
locally (`--verify`), so a copied closure that has lost an `open` fails on the
FC side rather than in lean-eval's CI.

The regions, in the order they must appear:

    dependencies  the FC-local closure of the statement, copied, Mathlib-only
    scope         the `open` and file-scoped directives the statement needs
    holes         one `noncomputable def <name> : <type> := sorry` per
                  `answer(sorry)` slot the importer hoisted
    statement     the target statement, its proof replaced by `sorry`
"""

import dataclasses
import json
import re

REGION_MARKER = "-- @region "
REGIONS = ("dependencies", "scope", "holes", "statement")

MODULE_PREAMBLE = "import Mathlib\n"

MANIFEST_SCHEMA_VERSION = 1


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
    """

    repository: str
    commit: str
    path: str
    blob_sha: str
    module: str
    declaration: str
    copied_dependencies: tuple
    original_declaration: str


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
    lean_toolchain: str
    mathlib_revision: str
    source: SourceRecord
    tools: dict
    source_url: str = ""
    notes: str = ""

    def __post_init__(self):
        for field in ("id", "theorem", "qualified_theorem", "lean_toolchain"):
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
            "apply_arguments": list(self.apply_arguments),
            "holes": [dataclasses.asdict(hole) for hole in self.holes],
            "permitted_axioms": list(self.permitted_axioms),
            "lean_toolchain": self.lean_toolchain,
            "mathlib_revision": self.mathlib_revision,
            "source": {
                **dataclasses.asdict(self.source),
                "copied_dependencies": list(self.source.copied_dependencies),
            },
            "tools": dict(self.tools),
        }
        if self.source_url:
            payload["source_url"] = self.source_url
        if self.notes:
            payload["notes"] = self.notes
        return payload

    @classmethod
    def from_json_object(cls, payload):
        version = payload.get("schema_version")
        if version != MANIFEST_SCHEMA_VERSION:
            raise SystemExit(
                f"manifest schema version {version!r} is not "
                f"{MANIFEST_SCHEMA_VERSION}"
            )
        source = dict(payload["source"])
        source["copied_dependencies"] = tuple(source["copied_dependencies"])
        return cls(
            id=payload["id"],
            theorem=payload["theorem"],
            qualified_theorem=payload["qualified_theorem"],
            apply_arguments=tuple(payload["apply_arguments"]),
            holes=tuple(DefinitionHole(**hole) for hole in payload["holes"]),
            permitted_axioms=tuple(payload["permitted_axioms"]),
            lean_toolchain=payload["lean_toolchain"],
            mathlib_revision=payload["mathlib_revision"],
            source=SourceRecord(**source),
            tools=dict(payload["tools"]),
            source_url=payload.get("source_url", ""),
            notes=payload.get("notes", ""),
        )

    def to_json(self):
        return json.dumps(self.to_json_object(), indent=2, ensure_ascii=False) + "\n"

    @classmethod
    def from_json(cls, text):
        return cls.from_json_object(json.loads(text))


@dataclasses.dataclass(frozen=True)
class MarkedUpModule:
    """One Mathlib-only Lean module, in the four labelled regions.

    Rendering and parsing are inverse on the region bodies, so the artifact
    the importer emits for review is the artifact the generator reads.
    """

    dependencies: str
    scope: str
    holes: str
    statement: str

    def __post_init__(self):
        # Rendering separates the regions itself, so leading and trailing
        # blank lines are not part of a region's content. Normalising them
        # here is what makes rendering and parsing inverse.
        for name in REGIONS:
            object.__setattr__(self, name, getattr(self, name).strip("\n"))

    def regions(self):
        return {name: getattr(self, name) for name in REGIONS}

    def render(self):
        parts = [MODULE_PREAMBLE]
        for name, body in self.regions().items():
            body = body.strip("\n")
            # A copied declaration carrying a line that reads as a marker
            # would split the module somewhere the importer did not choose,
            # and the generator would never know. Refuse instead.
            for line in body.split("\n"):
                if line.startswith(REGION_MARKER):
                    raise SystemExit(
                        f"the {name} region contains a region marker: {line!r}"
                    )
            parts.append(f"\n{REGION_MARKER}{name}\n" + (body + "\n" if body else ""))
        return "".join(parts)

    @classmethod
    def parse(cls, text):
        """Read a rendered module back, refusing anything the shape forbids."""
        bodies, current = {}, None
        for line in text.split("\n"):
            if line.startswith(REGION_MARKER):
                current = line[len(REGION_MARKER) :].strip()
                if current not in REGIONS:
                    raise SystemExit(f"unknown region {current!r} in marked-up module")
                if current in bodies:
                    raise SystemExit(f"region {current!r} appears twice")
                bodies[current] = []
                continue
            if current is not None:
                bodies[current].append(line)
        missing = [name for name in REGIONS if name not in bodies]
        if missing:
            raise SystemExit(
                "marked-up module has no " + ", ".join(f"`{m}`" for m in missing)
                + " region"
            )
        if list(bodies) != list(REGIONS):
            raise SystemExit(
                "marked-up module regions are out of order: "
                + ", ".join(bodies)
                + f"; expected {', '.join(REGIONS)}"
            )
        return cls(
            **{name: "\n".join(lines) for name, lines in bodies.items()}
        )
