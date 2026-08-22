# Formal Conjectures to LeanEval adapter

This directory contains the Formal Conjectures side of the integration with
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval) and
[`leanprover/comparator`](https://github.com/leanprover/comparator), following
the ownership split proposed in
[`lean-eval#536`](https://github.com/leanprover/lean-eval/pull/536), with
coordination tracked in
[`lean-eval#533`](https://github.com/leanprover/lean-eval/issues/533) and
[`formal-conjectures#4930`](https://github.com/google-deepmind/formal-conjectures/issues/4930).

**[`OWNERSHIP.md`](OWNERSHIP.md) is the map**: which code is Formal
Conjectures' permanently, what crosses the seam to the pinned
[`leanprover/lean-eval-generator`](https://github.com/leanprover/lean-eval-generator),
and what the interface still needs from lean-eval. Read it first. This file is
the operator's page: the commands, their inputs, and the pins.

## The generator binary

Workspace generation runs the extracted generator at the revision `tools.toml`
pins under `[generator]`. Build it once — the package depends on nothing, so
this is quick — and point the importer at it:

```bash
git clone https://github.com/leanprover/lean-eval-generator /tmp/lean-eval-generator
git -C /tmp/lean-eval-generator checkout "$(python3 -c '
import tomllib; print(tomllib.load(open("comparator/tools.toml","rb"))["generator"]["rev"])')"
(cd /tmp/lean-eval-generator && lake build)
export LEAN_EVAL_GENERATOR_BIN=/tmp/lean-eval-generator/.lake/build/bin/lean-eval-generator
```

Import and `--verify` are offline as before; only generation needs the binary.

## Two toolchains

Formal Conjectures elaborates its own source under its own pinned toolchain.
LeanEval is the benchmark host: an imported problem is built and checked under
LeanEval's pinned Lean 4.33 and matching Mathlib. Supporting the integration
does not require a repository-wide toolchain upgrade here.

So the importer reads a declaration's source range, binders, dependencies and
`answer(sorry)` slot types from an environment elaborated at *this*
repository's toolchain, and the workspace it produces is pinned to *LeanEval's*
toolchain and Mathlib. The request carries LeanEval's pins; the provenance
sidecar `fc-provenance.json` records the pins the hole types were read at.
`.github/workflows/comparator-lean-4-33.yml` generates a
workspace here and builds and Comparator-checks it there, in one job, which is
what turns the gap between them into something observed rather than assumed.

## Generate one workspace

```bash
python3 comparator/adapter/make_comparator_workspace.py erdos_940.variants.large_integers
```

Use `--out` to choose the parent directory. Generation refuses to overwrite an
existing workspace: it writes into a temporary directory and renames the
complete workspace into place.

The importer stops when the selected source differs from the pinned upstream
revision. This prevents a workspace from combining a working-tree statement
with an older imported context.

`--verify` elaborates the marked-up module before anything is written, so an
FC-side copying defect fails here rather than in LeanEval CI. It runs at this
repository's Lean and Mathlib, so it is not evidence about the 4.33 build.

The workspace contains `ChallengeDeps.lean` with the statement's copied Formal
Conjectures closure, `Challenge.lean` with the trusted statement and its proof
hole, `Submission.lean` and `Submission/` where a solver works, `Solution.lean`
connecting the two, `config.json` with the theorem targets, definition targets
and permitted axioms, `holes.json`, and the `fc-provenance.json` sidecar this
side adds beside the generator's files. `Solution.lean` is fixed: it fails
to build if the submission changes the statement. Comparator rejects `sorryAx`,
because it is not in the permitted axiom list.

### Emit only what this repository owns

```bash
python3 comparator/adapter/make_comparator_workspace.py erdos_1038.parts.i \
  --emit-import .comparator-import
```

This writes the exact bytes that cross the seam — `request.json`, the
`context/` directory the schema-version-1 contract reads, and the provenance sidecar — and
generates no workspace. Running the pinned binary on that request from inside
the emitted directory yields the same file map generation would have written,
which is what makes the seam checkable rather than asserted.

### Import a whole set

```bash
python3 comparator/adapter/make_comparator_workspace.py --set FC100OpenSet1 \
  --verify --report fc100-report.json \
  --known-failures comparator/known_failures.toml
```

One request carries every declaration that imports; failures are recorded per
declaration in the report instead of aborting the run. With
`--known-failures`, the run fails unless the failures are exactly the recorded
ones — an unexpected failure and a silently fixed one both count.

### Supported inputs

- theorem proofs;
- definition answers represented by `answer(sorry)`;
- helper modules under `Submission/`.

Plain-statement disproofs remain out of scope until Comparator provides an
upstream interface for them.

The importer fails closed on ambiguous declarations, source drift, inaccessible
binders, unsupported dependencies, answer-slot types that cannot be matched
safely, and existing output.

## Problem files

`problems/*.toml` is an input, not the LeanEval manifest: it records the
choices this repository's Lean source cannot make for itself, and the importer
reads it. The request the generator receives, and the provenance sidecar, are
derived.

Most declarations need no problem file. Add one TOML file under `problems/`
only when two files declare the same name, which is the one thing the Lean
environment cannot resolve.

| Field | Meaning |
|---|---|
| `id` | Workspace name. It must match the TOML filename. |
| `declaration` | Lean declaration name. |
| `module` | Source file when the declaration name is ambiguous. |

There is deliberately nothing else. The source citation comes from the module
docstring's `*Reference:*` line, because a copy kept here drifts from the one
the repository maintains — the copy this directory used to hold for
`Margulis.lean` had already lost the `v3` the docstring pins. An answer-slot
type Lean reports ambiguously is a `--answer-type` argument rather than a
field, since no problem currently needs one and a field nothing sets is a
format nobody checks.

Run the problem-file check after moving or renaming a declaration:

```bash
python3 comparator/adapter/make_comparator_workspace.py --validate
```

## Tool pins

`tools.toml` is the one machine-readable source. `[tools]` are the revisions a
local run uses under this repository's toolchain. `[target]` are LeanEval's:
the Lean toolchain and Mathlib revision every generated workspace is pinned to,
and the Comparator and `lean4export` commits that check it. `[generator]` is
the extracted generator revision every request is written against; bumping it
is a contract change and has to survive the seam round-trip test. Generation
itself does not run Comparator.

## Conformance before a public import

The adapter should cover these boundary cases before importing a frozen set:

- a plain theorem proof;
- a `Prop`-valued `answer(sorry)` slot;
- a non-`Prop` answer slot;
- explicit declaration parameters versus `∀` binders in the conclusion;
- trusted helper dependencies requiring `ChallengeDeps` or multiple trusted
  files.

The two CI jobs exercise those distinctions: `build-and-docs.yml` generates
five declarations covering each case and checks the importer-to-generator seam,
and `comparator-lean-4-33.yml` builds two of them at LeanEval's pins and runs
Comparator on them. They validate extraction and adapter behaviour, not
mathematical correctness or maintainer acceptance.

The first public open-conjectures import also needs a corrected source set.
`FC100OpenSet1` currently verifies itself as 92 `research open` entries and 8
`research solved` entries, so it must not be imported wholesale as one hundred
open conjectures.
