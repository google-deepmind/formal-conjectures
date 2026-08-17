# Comparator workspace adapter

This directory contains a thin adapter from Formal Conjectures to
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval) and
[`leanprover/comparator`](https://github.com/leanprover/comparator). It does not
implement another evaluator.

## How it works

1. `scripts/comparator_facts.lean` asks Lean for the selected declaration's
   source range, binders, and `answer(sorry)` slot types.
2. `scripts/make_comparator_workspace.py` creates one pinned workspace.
3. The generated project builds the challenge and submission.
4. `lake test` runs Comparator against `config.json`.

The workspace contains:

- `Challenge.lean`, with the trusted statement and proof hole;
- `Submission.lean` and `Submission/`, where a solver works;
- `Solution.lean`, which connects the submission to the trusted statement;
- `config.json`, with theorem targets, definition targets, and permitted axioms;
- `holes.json`, with the exact extracted declaration blocks;
- pinned Lean, Mathlib, Formal Conjectures, Comparator, and helper-tool versions.

`Solution.lean` is fixed. It fails to build if the submission changes the
statement. Comparator also rejects `sorryAx` because it is not in the permitted
axiom list.

## Generate one workspace

```bash
python3 scripts/make_comparator_workspace.py erdos_940.variants.large_integers
```

Use `--out` to choose the parent directory. The generator refuses to overwrite
an existing workspace. It writes into a temporary directory and renames the
complete result into place.

The generator also stops when the selected source differs from the pinned
upstream revision. This prevents a workspace from combining a working-tree
statement with an older imported context.

## Supported inputs

- theorem proofs;
- definition answers represented by `answer(sorry)`;
- helper modules under `Submission/`.

Plain-statement disproofs remain out of scope until Comparator provides an
upstream interface for them.

## Problem manifests

Most declarations need no manifest. Add one TOML file under `problems/` only
when the source cannot select the declaration by itself.

| Field | Meaning |
|---|---|
| `id` | Workspace name. It must match the TOML filename. |
| `declaration` | Lean declaration name. |
| `module` | Source file when the declaration name is ambiguous. |
| `answer_type` | Explicit override when slot types cannot be matched safely. |
| `source` | Optional source link for the generated README. |
| `notes` | Optional reviewer note for the generated README. |

Run the manifest check after moving or renaming a declaration:

```bash
python3 scripts/make_comparator_workspace.py --validate
```

## Tool pins

`tools.toml` records the external tool revisions. Generated workspaces pin
Mathlib from `lake-manifest.json` and Formal Conjectures to the current upstream
revision. The workspace build fetches these dependencies; workspace generation
itself does not run Comparator.

Issue #4930 tracks the upstream integration and execution-service decisions.
