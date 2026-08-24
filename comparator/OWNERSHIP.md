# What this repository owns, and what it hands over

[`lean-eval#536`](https://github.com/leanprover/lean-eval/pull/536) §10 divides
this integration in two, and the other half now exists:
[`leanprover/lean-eval-generator`](https://github.com/leanprover/lean-eval-generator)
is the extracted generator core — the part that turns a Lean module plus hole
metadata into a Challenge / Solution / Submission workspace, with the import
and scope fidelity work from
[`lean-eval#531`](https://github.com/leanprover/lean-eval#531). It is a
deterministic Lean CLI with a frozen, versioned JSON contract, consumed at the
exact revision `comparator/tools.toml` pins under `[generator]`. **The Formal
Conjectures importer does not fork the generation logic.** It maps FC
declarations and metadata to a schema-version-1 request, and records the FC source commit
and declaration id for every problem.

## The seam

    comparator/adapter/fc_source.py              reading FC source: where a declaration
                                                 is, its preamble, notation, answer slots
    comparator/adapter/fc_leaneval_importer.py   FC declaration -> (module, manifest),
                                                 assembled from those answers
    comparator/adapter/leaneval_interface.py     the request built from them, the
                                                 response checked against its digests
    comparator/adapter/leaneval_generator_cli.py runs the pinned binary, nothing else

`comparator/adapter/make_comparator_workspace.py` is the command that runs one after the
other. The arrow points one way: the CLI plumbing imports the interface and
never the importer, and a test asserts that.

### What crosses it

One **v1 request** (`schemas/request-v1.schema.json` at the pinned generator
revision is normative). Per problem it carries:

| Field | Comes from |
|---|---|
| `moduleContent` | the rendered marked-up module: the statement's copied FC-local closure, the scope directives in force where it was written, one `noncomputable def <name> : <type> := sorry` per `answer(sorry)` slot, and the statement with its proof replaced by `sorry` — in that order, requiring Mathlib and nothing else |
| `resolvedHoles` | a source span, kind, and explicit parameters for each hole, computed from the rendered text — exactly, because this side rendered it |
| `holes`, `id`, `moduleName` | the qualified declaration name, slugged; two modules declaring `conjecture` in different namespaces must not share a workspace |
| `group` | for a frozen-set import, the set itself: the list is immutable while its members keep getting solved, so every member stays in the open-conjectures display and the category rides along as a tag. For a single import, the declaration's `@[category ...]` tag decides; a declaration that is not a problem is refused either way |
| `leanToolchain`, `mathlib` | LeanEval's pins, from `[target]` in `tools.toml` — the consumer's, never this repository's |
| `templates.workspaceTest` | `comparator/templates/WorkspaceTest.lean`, which stays FC-supplied: the contract requires the consumer to provide it |
| `contextRoot` | a directory this side materialises: the module file the generator byte-checks against `moduleContent`, and a synthesised `.ilean` carrying the spans above, because generator schema version 1 still resolves declaration spans from compiled metadata |

The module carries no markers of any kind. `@[eval_problem]` does not exist
outside lean-eval, so a module carrying it could not elaborate under
`--verify`; the ranges in the request already say where the holes are.

The module is one file rather than four strings because the importer can then
elaborate exactly what it is about to hand over: `--verify` runs the module
through this checkout's Mathlib, so an FC-side defect — a lost `open`, an
unrecognised `local notation`, a namespace nothing declares any more — fails
here and not in lean-eval's CI.

The response is the complete workspace file map with a SHA-256 digest per
file, and every digest is checked before a byte lands on disk.

### Provenance rides beside the request, not in it

lean-eval#536 requires each imported problem to record the FC source commit
and declaration id. The schema-version-1 wire format has no field for either — its optional
`source` is one free-text line — and lean-eval keeps that format frozen on
purpose, so the sidecar is the schema-version-1 provenance boundary **by design**, not a
stopgap (kim-em on #4951, 2026-08-21); a typed provenance object is a future-contract-revision
matter and does not gate the FC100 import. The manifest this repository
builds (`ProblemManifest`: commit, path, blob, module, declaration, copied
dependencies, the pins the hole types were read at) is written beside the
generated workspace as `fc-provenance.json`, and beside the emitted request
as `fc-provenance-<id>.json`.

Three properties make it fit to be that boundary. It is **strict**: a record
with a key the schema does not name is refused on load. It is
**deterministic**: serialisation is key-sorted, so the same record is the
same bytes. And it is **digested**: it carries the SHA-256 of the exact
`moduleContent` that crossed the seam and of every generated file the
response returned, so a workspace holds its own chain — FC commit → module
bytes → generated bytes — and each link can be checked without this
repository. It is also what makes regeneration possible when Formal
Conjectures corrects a misformalisation upstream.

## What stays Formal Conjectures' permanently

| File | Why it cannot move |
|---|---|
| `comparator/adapter/fc_source.py` | reads this repository's own Lean: where a declaration is, the file-scoped directives in force where it was written, the FC-defined notation it uses, its `answer(sorry)` slots and their elaborated types, and the pins the text was read at. Holds the strict `FactsRecord` boundary for the extractor's payload, and the prefetch cache a set run fills through the extractor's `--batch` arm so the Mathlib import is paid once |
| `comparator/adapter/fc_leaneval_importer.py` | assembles the marked-up module and the provenance record from those answers: resolves the declaration against an exact FC commit, copies the FC-local closure, hoists each slot, and records the provenance |
| `comparator/adapter/ComparatorFacts/` and `comparator_facts.lean` | the Lean extractor (a small library — `Binders.lean` recovers declaration-header binder boundaries from source syntax, `Extract.lean` reads the elaborated environment — and a thin executable): source ranges, declaration-header binder boundaries, elaborated binder names/explicitness, answer-slot types (anywhere in the statement, hypothesis binders included), and the `@[category ...]` tag. One `module declaration` pair per invocation, or `--batch` pairs on stdin sharing a single environment, one JSON object per line in input order. The parsed source distinguishes header parameters from `∀` binders in the conclusion; every emitted binder fact still comes from the elaborated environment. |
| `comparator/adapter/leaneval_interface.py` | the request builder and response checker — the FC side of the wire format, permanently, since the consumer owns hole resolution under the schema-version-1 contract |
| `comparator/adapter/leaneval_generator_cli.py` | plumbing for the pinned binary |
| `comparator/adapter/make_comparator_workspace.py` | the command, the emitted seam artifact, and the whole-set batch run|
| `comparator/adapter/known_failures.py` | the known-failures ledger's format and loader, shared by the set run and the target-stage compile |
| `comparator/templates/WorkspaceTest.lean` | the workspace test template the contract requires the consumer to supply |
| `comparator/problems/*.toml` | the rare source-boundary facts the compiled environment cannot recover: which module when two declare the same name, and an explicit copied proof dependency when opaque theorem-value erasure removes it from the compiled dependency graph |
| `comparator/tools.toml` | the pins, in one machine-readable place: this repository's under `[tools]`, LeanEval's under `[target]`, the generator revision under `[generator]` |

The tests beside each file pin real defects: the importer suite covers
extraction, the interface suite covers the wire shapes, and the command suite
runs the real pinned binary end to end when one is built (CI always does).

Nothing in the importer names a workspace file, a workspace layout, or an
import graph. If a change to it would, the change belongs on the other side.

## Not built, on purpose

**Disproof support.** Blocked upstream: Comparator has no interface for a
plain-statement disproof, and the overhaul plan defers it to the
open-conjectures phase. Nothing here anticipates one.

**Multi-file Challenge support.** The generator carries a statement's whole
closure in `ChallengeDeps`, which is one file. Measured over `FC100OpenSet1`,
no statement needs another FC problem module, so this does not block the
first import.

**A vendored workspace.** A workspace checked into this repository is a copy
of generator output, so it drifts from the generator, and it says nothing
about the importer because a human wrote it. The Lean 4.33 evidence comes
from generating one in CI instead.

**Lifecycle.** Result records, resubmission, and revision tracking are
LeanEval's, per lean-eval#536. This repository regenerates and opens a pull
request; it keeps no state about what happened to one.

## What this side cannot settle alone

1. **Provenance fields in the contract.** Generator schema version 1 has no
   home for the FC source commit and declaration id that §10 requires by
   name, so they travel as a sidecar. A passthrough or provenance field in a
   future generator contract revision would let a generated workspace carry
   its own origin. Related:
   `mathlib-initiative/formalization.yaml` already standardises a source
   repository, revision, declaration and Comparator config —
   `Paul-Lez/hadamard-668-comparator` uses it to describe a wrapper around FC
   at `1721605c` — but its required `project`, `sources`, `automation` and
   `review` sections belong to whoever formalised the statement rather than
   to an import, and it deliberately omits pins. So the question is which
   object is which, not whether to publish a schema.
2. **The `definition_names` config field is undocumented.** Comparator's
   published no-hole config does not carry it, and hole support depends on
   the comparator commit pinned in `tools.toml`. A generated workspace with
   an `answer(sorry)` hole is only checkable against that build.
3. **Answer-slot types are read under this repository's toolchain.** The
   importer asks Formal Conjectures' elaborated environment, at FC's pins,
   for the type of each slot; the workspace is built at LeanEval's. The
   overhaul plan assigns the re-resolution to LeanEval — the consumer
   re-resolves hole metadata under its own target environment — and the
   whole-set audit run is what observes the gap meanwhile: it generates at
   FC's pins and compiles every generated workspace at LeanEval's, with the
   failures recorded by name in `comparator/known_failures.toml` and
   asserted exactly. Which side owns the answer when the two environments
   disagree about a type is lean-eval's call.
4. **Who triggers regeneration is unassigned.** The plan gives the importer
   the duty to regenerate and re-PR when Formal Conjectures fixes a
   misformalisation upstream, and gives lifecycle to LeanEval. Nothing yet
   says which side watches FC commits for a change to an imported
   declaration. The provenance sidecar records what is needed to answer the
   question — commit, path, blob and declaration — but nobody is asking it.
