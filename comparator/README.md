# Package-backed proof workspaces

Export an FC statement with Lean, then pass closed declaration signatures to
[lean-eval-generator#7](https://github.com/leanprover/lean-eval-generator/pull/7).
Its structured v2 renderer imports a pinned FC package. Neither side copies FC
helper definitions or reconstructs source scopes. Python does not parse Lean.
The generator receives no source ranges, context directory or `.ilean` files.

## Generate a workspace

Fetch upstream main, then run:

```sh
python3 comparator/export_problem.py FormalConjectures/ErdosProblems/940.lean \
  Erdos940.erdos_940 --generator /path/to/lean-eval-generator \
  --out /tmp/erdos-940
```

The output contains `request.json`, `export.json` and `workspace/`. Solvers edit
`workspace/Submission.lean` and files under `workspace/Submission/`. The generator
request is self-contained and can be replayed without the FC checkout.

The source defaults to the local `origin/main` ref. Source files, toolchain,
resolved dependencies and relevant Lake settings must match that snapshot.
For another snapshot, pass `--source-ref` and `--source-repository`. The selected
commit must be available from that repository. Existing output is not overwritten.

## Extraction and checking

The exporter uses Lean's frontend with `google.answer = postpone` to preserve
answer annotations. It replaces unfinished answers with typed definition holes,
abstracting local parameters used by their types. Substituting the original
answers must recover the original statement by definitional equality.

Private constants without writable Lean names are unfolded from their elaborated
definitions; equality with the original statement is still checked.
Signatures include explicit arguments, proof terms and universe parameters.
Lean re-elaborates them under the same universe parameters and checks equality.
Structured results use a dedicated JSON file, so source diagnostics cannot corrupt
the transport. Python passes these signatures and package pins to the generator, validates its
file map and digests, then compiles the actual generated Challenge with Lean.
It records source, exporter, generator, request and output provenance.

`config.json` enables nanoda as well as Lean's kernel. `lake test` invokes the
configured Comparator. Use the Linux sandbox setup in the CI workflow: real
Landrun, an unprivileged process, and systemd's AF_UNIX restriction required by
Comparator. There is no fallback to an unsandboxed verifier.

The verifier's exporter must read FC's `.olean` format. Build it as a normal
pinned Lake dependency with `lake -d comparator/verifier build lean4export/lean4export`.
This tool project declares FC's Lean version and leaves upstream files untouched.
Comparator itself builds with its own declared toolchain.

## Validation

```sh
lake --wfail build export_problem FormalConjecturesTest.PackageExport
lake --wfail test
LEAN_EVAL_GENERATOR_CHECKOUT=/path/to/generator \
  python3 -m unittest discover -s comparator -p test_export.py -v
python3 comparator/check_coverage.py --generator /path/to/generator --out /tmp/fc100
```

The ten fixtures cover local and private definitions, proposition and numeric answers,
dependent and multiple answers, explicit and implicit universes, and proof terms in types. Tests resolve real Git package
pins in a fresh workspace without modifying Lake's dependency manifest. Set
`FC_SOURCE_REPOSITORY` to test a remote fork; the default is the local Git repo.
With the verifier environment used in CI, tests also exercise both kernels and
reject unfinished proofs, imported sorried theorems, changed statements and an
attempted write outside the sandbox. Submissions are first built by Comparator.

The FC100 check evaluates the subset list in Lean, exports every member, compiles
each generated Challenge, and records every failure in `report.json`. It checks
export coverage, not proofs of those problems. Unsupported signatures are errors.

Lean frontend APIs remain version-sensitive; the toolchain pin and these checks
make that dependency explicit. This is an alternative to #4951, not a LeanEval
catalog import. LeanEval adoption requires a compatible environment and policy.
Definition-hole answers still require assessment of their mathematical meaning.
