# Formal Conjectures to LeanEval adapter

This directory contains the Formal Conjectures side of the integration with
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval) and
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## Status and version boundary

The code in this draft is a **conformance prototype**, not a second permanent
workspace generator.

- Formal Conjectures currently elaborates its source under its own pinned
  toolchain.
- LeanEval is the benchmark host and target environment. Imported problems must
  compile under LeanEval's pinned **Lean 4.33** toolchain and matching Mathlib
  revision.
- Formal Conjectures does not need a repository-wide toolchain upgrade merely
  to support the integration.
- LeanEval owns the shared Challenge/Solution/Submission generator and
  Comparator execution path.
- Formal Conjectures owns an importer that resolves declarations, preserves
  provenance, maps `answer(sorry)` semantics, and emits reviewable LeanEval
  source and manifests.

The code is already arranged along that line. `scripts/fc_leaneval_importer.py`
is the FC side and stays; `scripts/leaneval_generator.py` stands in for the
shared generator and is written to be deleted, not rewritten, once
`leanprover/lean-eval-generator` exists. [`OWNERSHIP.md`](OWNERSHIP.md) gives
the interface between them and the line counts either side of that deletion.

This follows the ownership split proposed in
[`lean-eval#536`](https://github.com/leanprover/lean-eval/pull/536), with
coordination tracked in
[`lean-eval#533`](https://github.com/leanprover/lean-eval/issues/533) and
[`formal-conjectures#4930`](https://github.com/google-deepmind/formal-conjectures/issues/4930).

## Final integration flow

1. The FC importer resolves a declaration against an exact Formal Conjectures
   commit and obtains its source range, binders, namespace, dependencies, and
   `answer(sorry)` slot types from Lean.
2. It emits one marked-up LeanEval module and one problem manifest. The
   manifest records at least the FC repository, commit, source path, blob, and
   fully qualified declaration name, so that a workspace can be traced back to
   a revision of this repository and regenerated when that revision is
   corrected.
3. LeanEval builds the vendored source under Lean 4.33 and its matching Mathlib
   pin.
4. The shared LeanEval generator creates `Challenge`, `ChallengeDeps`,
   `Submission`, `Solution`, and Comparator configuration.
5. LeanEval CI builds the generated workspace and runs Comparator with
   `sorryAx` rejected.
6. A deterministic trusted-statement fingerprint links the imported source,
   generated challenge, result record, and later upstream corrections.

The importer must fail closed on ambiguous declarations, source drift,
inaccessible binders, unsupported dependencies, answer-slot types that cannot
be matched safely, and existing output.

## Conformance suite before a public import

The adapter should cover these boundary cases before importing a frozen set:

- a plain theorem proof;
- a `Prop`-valued `answer(sorry)` slot;
- a non-`Prop` answer slot;
- explicit declaration parameters versus `∀` binders in the conclusion;
- trusted helper dependencies requiring `ChallengeDeps` or multiple trusted
  files.

The smoke cases in this draft exercise those distinctions. They validate
extraction and adapter behavior, not mathematical correctness or maintainer
acceptance.

The first public open-conjectures import also needs a corrected source set.
`FC100OpenSet1` currently verifies itself as 92 `research open` entries and 8
`research solved` entries, so it must not be imported wholesale as one hundred
open conjectures.

## Current prototype

`scripts/comparator_facts.lean` asks Lean for the selected declaration's source
range, binders, and `answer(sorry)` slot types.

`scripts/fc_leaneval_importer.py` maps that declaration to the pair the
generator consumes: one marked-up Mathlib-only Lean module, and one manifest.
`scripts/leaneval_generator.py` turns the pair into a pinned standalone
workspace as a conformance harness, and
`scripts/make_comparator_workspace.py` runs the two in order. The generated
workspace uses the Formal Conjectures toolchain and dependency pins. It is
**not** the final LeanEval 4.33 artifact.

The prototype workspace contains:

- `ChallengeDeps.lean`, with the statement's copied Formal Conjectures closure;
- `Challenge.lean`, with the trusted statement and proof hole;
- `Submission.lean` and `Submission/`, where a solver works;
- `Solution.lean`, which connects the submission to the trusted statement;
- `config.json`, with theorem targets, definition targets, and permitted axioms;
- `manifest.json`, the manifest the importer handed the generator: the Formal
  Conjectures source commit and declaration id, the copied closure, the exact
  original declaration text, the hole types, and the pins;
- pinned Lean, Mathlib, Formal Conjectures, Comparator, and helper-tool versions.

`Solution.lean` is fixed. It fails to build if the submission changes the
statement. Comparator also rejects `sorryAx` because it is not in the permitted
axiom list.

### Generate one prototype workspace

```bash
python3 scripts/make_comparator_workspace.py erdos_940.variants.large_integers
```

Use `--out` to choose the parent directory. The generator refuses to overwrite
an existing workspace. It writes into a temporary directory and renames the
complete workspace into place.

The importer stops when the selected source differs from the pinned upstream
revision. This prevents a workspace from combining a working-tree statement
with an older imported context.

`--verify` elaborates the marked-up module against this checkout's Mathlib
before anything is written, so a copying defect fails here rather than in
LeanEval CI.

### Emit only what this repository owns

```bash
python3 scripts/make_comparator_workspace.py erdos_1038.parts.i \
  --emit-import .comparator-import
```

This writes `Problem.lean` and `manifest.json` and generates no workspace. It
is the pair the importer contributes to a LeanEval problem pull request once
the shared generator is a pinned dependency there.

### Supported prototype inputs

- theorem proofs;
- definition answers represented by `answer(sorry)`;
- helper modules under `Submission/`.

Plain-statement disproofs remain out of scope until Comparator provides an
upstream interface for them.

## Problem files

`problems/*.toml` is an input, not the LeanEval manifest: it records the
choices this repository's Lean source cannot make for itself, and the importer
reads it. The manifest the generator receives, and writes into the workspace as
`manifest.json`, is derived.

Most declarations need no problem file. Add one TOML file under `problems/`
only when the source cannot select the declaration by itself.

| Field | Meaning |
|---|---|
| `id` | Workspace name. It must match the TOML filename. |
| `declaration` | Lean declaration name. |
| `module` | Source file when the declaration name is ambiguous. |
| `answer_type` | Explicit override when slot types cannot be matched safely. |
| `source` | Optional source link for the generated README. |
| `notes` | Optional reviewer note for the generated README. |

Run the problem-file check after moving or renaming a declaration:

```bash
python3 scripts/make_comparator_workspace.py --validate
```

## Tool pins

`tools.toml` records the external tool revisions used by the prototype.
Generated prototype workspaces pin Mathlib from `lake-manifest.json` and Formal
Conjectures to the current upstream revision. Workspace generation itself does
not run Comparator.

The final importer instead targets LeanEval's Lean 4.33 toolchain, Mathlib pin,
manifest schema, shared generator revision, and CI policy. Those target pins
belong on the LeanEval side and must be recorded in every generated import or
its provenance record.
