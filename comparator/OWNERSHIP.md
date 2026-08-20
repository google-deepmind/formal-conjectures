# What this repository owns, and what it hands over

[`lean-eval#536`](https://github.com/leanprover/lean-eval/pull/536) §10 divides
this integration in two. lean-eval's generator core — the part that turns a
marked-up Lean module plus a manifest into a Challenge / Solution / Submission
workspace, with the import and scope fidelity work from
[`lean-eval#531`](https://github.com/leanprover/lean-eval/pull/531) — is being
extracted into `leanprover/lean-eval-generator` and consumed as a pinned
dependency. **The Formal Conjectures importer does not fork the generation
logic.** It maps FC declarations and metadata to LeanEval modules and manifests,
and each manifest records the FC source commit and declaration id.

The code here is arranged along that line so the handover is a deletion rather
than a rewrite. This file says exactly what goes.

## The seam

    scripts/fc_leaneval_importer.py     FC declaration -> (module, manifest)
    scripts/leaneval_interface.py       the two values, and nothing else
    scripts/leaneval_generator.py       (module, manifest) -> workspace files

`scripts/make_comparator_workspace.py` is the command that runs one after the
other. The arrow points one way: the generator imports the interface and never
the importer, and a test asserts that.

### What crosses it

`MarkedUpModule` is one Lean module that requires Mathlib and nothing else,
divided into four labelled regions:

| Region | Contents |
|---|---|
| `dependencies` | the statement's FC-local closure, copied, each declaration carrying the `open`, `variable`, `universe`, `set_option` and `local notation` in force where it was written |
| `scope` | the directives the statement itself needs, and the namespaces it is stated in |
| `holes` | one `noncomputable def <name> : <type> := sorry` for each `answer(sorry)` slot |
| `statement` | the target statement, decorations stripped, proof replaced by `sorry` |

The module is not pre-split into Challenge and ChallengeDeps, because deciding
which generated file imports which, and where the scope has to be restated so
that the same statement text elaborates in all three, is the generator's work.
It is one module rather than four strings because the importer can then
elaborate exactly what it is about to hand over: `--verify` runs the module
through this checkout's Mathlib, so an FC-side defect — a lost `open`, an
unrecognised `local notation`, a namespace nothing declares any more — fails
here and not in lean-eval's CI.

`ProblemManifest` carries what the Lean text does not say: the theorem's name
and its explicit parameters, the hole types Lean reported, the permitted
axioms, a `source` record with the FC repository, commit, blob, module,
declaration id and this repository's Lean and Mathlib pins, and a `target`
record with LeanEval's pins, which are the ones the workspace is built at. lean-eval#536 requires the
commit and the declaration id by name, and they are FC-side by necessity: the
generator sees a Lean module, not a repository. They are also what makes
regeneration possible when Formal Conjectures corrects a misformalisation
upstream. The generator writes the manifest into the workspace unaltered, as
`manifest.json`.

## What is deleted when `lean-eval-generator` lands

| File | Lines | Then |
|---|---|---|
| `scripts/leaneval_generator.py` | 228 | deleted; `generate` becomes a call into the pinned package |
| `scripts/test_leaneval_generator.py` | 163 | deleted, less whatever remains useful as a contract test against the pinned generator |
| `comparator/templates/WorkspaceTest.lean` | 37 | deleted; the generator supplies its own workspace test |
| `scripts/leaneval_interface.py` | 293 | replaced by an import from the pinned package, to the extent its types match |

That is 428 lines deleted outright and 293 more replaced. Nothing in
`scripts/fc_leaneval_importer.py` changes, and `make_comparator_workspace.py`
changes by one import.

## What stays Formal Conjectures' permanently

| File | Lines | Why it cannot move |
|---|---|---|
| `scripts/fc_leaneval_importer.py` | 870 | resolves a declaration against an exact FC commit, reads the elaborated environment, copies the FC-local closure, types each `answer(sorry)` slot, and records the provenance |
| `scripts/comparator_facts.lean` | 205 | the Lean extractor: source ranges, binder explicitness, and answer-slot types, all of which only this repository's elaborated environment knows |
| `scripts/test_fc_leaneval_importer.py` | 400 | every case pins a real extraction defect |
| `scripts/make_comparator_workspace.py` | 157 | the command, and the directory write that belongs to neither side |
| `scripts/test_make_comparator_workspace.py` | 99 | asserts the emitted pair rebuilds the workspace exactly |
| `comparator/problems/*.toml` | — | the choices FC source cannot make for itself: which module, and an answer type Lean reports ambiguously |
| `comparator/tools.toml` | — | the pins, in one machine-readable place: this repository's under `[tools]`, LeanEval's under `[target]` |

Nothing in the importer names a workspace file, a workspace layout, or an
import graph. If a change to it would, the change belongs on the other side.

## Not built, on purpose

**Disproof support.** Blocked upstream: Comparator has no interface for a
plain-statement disproof. Nothing here anticipates one.

**Multi-file Challenge support.** The generator already carries a statement's
whole closure in `ChallengeDeps`, which is one file. Splitting that closure
across several trusted files is a generator-side change: the importer would
hand over the same declarations, and only the `dependencies` region's shape
would have to say how they group. lean-eval#536 asks for this to be scoped
against the actual FC100 statements rather than in the abstract, so it is not
built here.

**A vendored workspace.** A workspace checked into this repository is a copy
of generator output, so it drifts from the generator, and it says nothing about
the importer because a human wrote it. The Lean 4.33 evidence comes from
generating one in CI instead.

**Lifecycle.** Result records, resubmission, and revision tracking are
LeanEval's, per lean-eval#536. This repository regenerates and opens a pull
request; it keeps no state about what happened to one.

## What this side cannot settle alone

Each of these is a place where the interface above is a guess that lean-eval
has to confirm or replace. None of them is blocking the FC work; all of them
would change bytes at the seam.

1. **The markup convention is invented here.** `-- @region <name>` and the four
   region names are local. The generator core is the natural owner of the
   convention, since it is the reader.
2. **The manifest schema is invented here.** `schema_version = 1` and the field
   names are this repository's. lean-eval#536 says the importer emits PRs that
   lean-eval CI validates like any other problem PR, which needs a published
   schema to validate against. The two fields the plan does name — the FC
   source commit and the declaration id — are present under
   `source.commit` and `source.declaration`.
3. **The `definition_names` config field is undocumented.** Comparator's
   published no-hole config does not carry it, and hole support depends on the
   comparator commit pinned in `tools.toml`. A generated workspace with an
   `answer(sorry)` hole is only checkable against that build.
4. **Answer-slot types are read under this repository's toolchain.** The
   importer asks Formal Conjectures' elaborated environment, at FC's Lean and
   Mathlib pins, for the type of each slot; the workspace is built at
   LeanEval's Lean 4.33 and its own Mathlib. A type whose name or elaboration
   differs between the two revisions would be wrong in a way `--verify` cannot
   see, because `--verify` also runs at FC's pins.

   `.github/workflows/comparator-lean-4-33.yml` now does both halves in one
   job: it generates at 4.27 and builds and Comparator-checks at 4.33, on one
   plain theorem and one `Prop`-valued `answer(sorry)` slot. So the gap is
   observed rather than asserted, and every manifest states it —
   `source.lean_toolchain` against `target.lean_toolchain`. What is still open
   is the general case: two declarations passing says nothing about a slot
   whose type name changed between the two Mathlib revisions. A frozen-set
   import needs that job over the whole set, and the decision about which side
   owns the answer when they disagree is lean-eval's.
5. **Who triggers regeneration is unassigned.** The plan gives the importer the
   duty to regenerate and re-PR when Formal Conjectures fixes a
   misformalisation upstream, and gives lifecycle to LeanEval. Nothing yet says
   which side watches FC commits for a change to an imported declaration. The
   manifest records what is needed to answer the question — commit, path, blob
   and declaration — but nobody is asking it.
