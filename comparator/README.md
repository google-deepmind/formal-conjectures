# Package-backed proof workspaces

This prototype exports an FC statement to a LeanEval generator v2 workspace.
The workspace imports a pinned FC package. It does not copy FC definitions,
notation, or source scopes. It is an alternative to the Mathlib-only importer
in [#4951](https://github.com/google-deepmind/formal-conjectures/pull/4951).

## Generate a workspace

Build the generator proposal in
[lean-eval-generator#7](https://github.com/leanprover/lean-eval-generator/pull/7), then run:

```sh
python3 comparator/export_problem.py FormalConjectures/ErdosProblems/940.lean \
  Erdos940.erdos_940 --generator /path/to/lean-eval-generator \
  --out /tmp/erdos-940
```

The output contains `request.json`, the real Lean metadata under `context/`,
`export.json`, and `workspace/`. The request can be replayed from that output
directory using the same generator. Solvers edit `workspace/Submission.lean`
and files under `workspace/Submission/`.

The source snapshot defaults to the local `origin/main` ref. Fetch before
exporting to use current upstream main. Source files, the toolchain, the
resolved dependency manifest, and the relevant Lake settings must match that
snapshot. The exporter executable may be on a separate development branch.
For a fork or local test, pass both `--source-ref` and `--source-repository`.
The repository must contain the selected commit before another machine can
fetch the workspace dependencies. Existing output is never overwritten.

## How the export works

`ExportProblem.lean` uses Lean's frontend to elaborate the source through the
selected declaration with `google.answer = postpone`. This preserves answer
annotations that the normal proposition-answer default would erase. It then:

1. Replaces unfinished answer annotations with typed definition holes, abstracting
   any local parameters needed by their types.
2. Checks that substituting the original answers recovers the source type.
3. Prints closed, explicit signatures and re-elaborates them with no namespace
   or open declarations, checking definitional equality.

The Python command adds the source package import, compiles the exported module
to produce real `.ilean` metadata, and calls the shared generator. The provenance
sidecar records the source commit and file digest, exporter commit and code digests,
generator commit, exact request digest, and generated file digests. The generator checkout is built before use;
an arbitrary binary supplied through `PATH` is not used.

## Checks and limits

```sh
lake --wfail build export_problem FormalConjecturesTest.PackageExport
LEAN_EVAL_GENERATOR_CHECKOUT=/path/to/lean-eval-generator \
  python3 -m unittest discover -s comparator -p test_export.py
```

The tests cover plain theorems, problem-local definitions, proposition and numeric
answers, parameter-dependent answers, multiple answers, and universe parameters.
They generate real metadata and build filled Solution adapters. They use explicit
local package manifests to reuse the checked-out source and existing build cache;
this is not a test of remote package availability.

Set `COMPARATOR_BIN` and install the compatible exporter and sandbox to also run
Comparator verdict checks. These reject an unfinished proof, reject a proof that
uses the imported sorried theorem, accept filled proofs, and reject a changed
statement. Comparator's macOS development shim is suitable only for these trusted
fixtures; it supplies no sandbox security. `WorkspaceTest.lean` runs the configured
Comparator; it does not claim to implement LeanEval's production nanoda policy.

This is a bounded prototype, not an FC100 qualification or a LeanEval catalog
import. Source re-elaboration may expose unsupported files, and private or generated
constants may fail to elaborate through package imports. Failures remain errors.
Expanded signatures prioritize explicit meaning over the original surface notation.
Plain-statement disproofs and assessment of an answer's mathematical usefulness
are outside this tool's scope.

The generated package uses the source snapshot's Lean and Mathlib. It does not
attempt to build a current FC statement at a different LeanEval toolchain.
Adopting these workspaces in LeanEval requires an explicit compatible snapshot.
