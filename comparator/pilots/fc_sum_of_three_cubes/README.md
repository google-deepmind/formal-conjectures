# FC Sum of Three Cubes: Lean 4.33 Comparator pilot

This is a vendored, reviewable conformance pilot for the Formal Conjectures to
LeanEval boundary. It does not upgrade the Formal Conjectures repository and it
does not claim to solve the open sum-of-three-cubes conjecture.

## Pins

- Formal Conjectures source commit: `9f5ee773841921f460b4a26a3552f5eca4accaa0`
- LeanEval reference commit: `7699436464052268e6c04b41554bfbc2c6908ec5`
- Lean: `leanprover/lean4:v4.33.0`
- Mathlib: `6f1ef4e5dd604a435bddba4747b13970cd65d2a1`
- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`
- Lean 4.33 exporter: `15f6055e299ad5b89345e533cc2192f4cc00f659`

`provenance.json` records the source declarations, transformation log, target
pins, and a SHA-256 fingerprint over the exact trusted `ChallengeDeps.lean` and
`Challenge.lean` files.

## What the workspace checks

The workspace follows LeanEval's generated structure:

- `ChallengeDeps.lean` contains the trusted predicate copied from Formal
  Conjectures.
- `Challenge.lean` contains a solved smoke theorem and the open conjecture's
  `answer(sorry)` slot, hoisted into a `Prop`-valued definition hole.
- `Submission.lean` supplies an actual proof of the solved smoke theorem.
- `Solution.lean` is fixed and delegates the challenge names to the submission.
- `config.json` asks Comparator to check both theorem names and the definition
  hole under LeanEval's permitted-axiom policy.

The open-conjecture smoke submission intentionally defines the answer hole to
be the proposition itself and proves the bridge by `Iff.rfl`. Comparator should
accept that declaration-level shape. It is not a mathematical resolution and a
human semantic reviewer must reject it. Keeping this case explicit tests the
reason definition answers require a separate review stage.

## Build

```bash
lake exe cache get
lake build
```

## Comparator smoke test

Build the pinned Comparator and Lean 4.33 exporter recorded above, then run:

```bash
COMPARATOR_BIN=/absolute/path/to/comparator \
COMPARATOR_LANDRUN=/absolute/path/to/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/absolute/path/to/lean4export \
lake test
```

The fake landrun is acceptable only for this trusted development smoke test. A
real submission service must use the production sandbox and preserve
Comparator's clean-build assumptions.

## What this does not establish

A passing run establishes that one vendored FC problem shape builds under
LeanEval's Lean 4.33 and Mathlib pins and crosses Comparator's theorem and
definition-hole interfaces. It does not establish that the general importer is
complete, that arbitrary FC dependencies port automatically, that the open
conjecture is solved, or that maintainers should accept the problem into a
frozen release.
