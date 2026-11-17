# Formal Conjectures — Palomar Submission Base (`palomar_prepare`)

[![CI](https://github.com/google-deepmind/formal-conjectures/actions/workflows/ci.yml/badge.svg)](https://github.com/google-deepmind/formal-conjectures/actions/workflows/ci.yml)

This branch (`palomar_prepare`) is a minimal, pre-bumped template derived from
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) for packaging a newly
found formal proof into a [Palomar Registry](https://palomar-registry.org/) submission.

All open-problem directories (`FormalConjectures/`), website assets, and problem-tracking scripts
have been stripped so that you only need to port the single solved problem and its proof.

## What is included

- **`FormalConjecturesForMathlib/`**: Reusable mathematical definitions and proved lemmas from
  Formal Conjectures, already bumped to the current Lean / Mathlib release (`v4.36.0`). Contains
  no `sorry`.
- **`FormalConjecturesUtil/`**: Shared attributes, metadata helpers, and style linters.
- **`FormalConjecturesTest/`**: Tests for `FormalConjecturesUtil`.
- **[`formalization.yaml`](formalization.yaml)**: Placeholder metadata file (`v0.4`) ready to be
  filled in for Palomar.
- **`scripts/check-lean-sources.py` & `scripts/verify-comparator.sh`**: Local preflight checks for
  Palomar's module/line-limit rules, `Challenge.lean` import boundaries, metadata placeholders,
  and `lake comparator` dual-kernel verification (`nanoda_bin` and `con-ron`).

## Quick start

1. **Fetch Mathlib cache and verify the base build:**
   ```bash
   lake exe cache get
   lake --wfail build
   lake --wfail test
   ```
2. **Add the solved problem statement in `Challenge.lean`:**
   - Import **only** `Mathlib` (never `FormalConjecturesUtil` or `FormalConjecturesForMathlib`;
     Palomar requires `Challenge.lean`'s transitive import closure to stay within Lean core and
     Mathlib).
   - Strip `@[category ...]`, `@[AMS ...]`, and `@[question ...]` attributes; inline any minimal
     non-Mathlib definitions needed by the statement with clear docstrings; leave proofs as
     `:= by sorry`.
3. **Add the proof in `Solution.lean` (and optional `Solution/*.lean` submodules):**
   - You may freely import `FormalConjecturesForMathlib` and `FormalConjecturesUtil` here.
   - Prove the exact same fully-qualified declaration names and types declared in `Challenge.lean`
     using only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
4. **Configure Comparator and Lake:**
   - Uncomment the `Challenge` and `Solution` targets in [`lakefile.toml`](lakefile.toml) and add
     them to `defaultTargets`.
   - Create `comparator.json` naming `Challenge`, `Solution`, and your `theorem_names`.
5. **Complete metadata and narrative:**
   - Replace every `TEMPLATE:` entry in [`formalization.yaml`](formalization.yaml).
   - Rewrite this `README.md` to give a clear mathematical overview of your theorem, sources, and
     proof for human readers and Palomar's editorial review.
6. **Verify and submit:**
   ```bash
   python3 scripts/check-lean-sources.py --submission
   lake --wfail build
   ./scripts/verify-comparator.sh
   ```
   Push to a public GitHub repository and submit the full 40-character commit SHA (`git rev-parse HEAD`)
   at <https://submit.palomar-registry.org/>.

## Detailed documentation

- **For humans:** See [`PALOMAR.md`](PALOMAR.md) for full details on dependency boundaries, value
  questions (`answer(...)`), `formalization.yaml` provenance rules, and submission steps.
- **For AI agents:** See [`AGENTS.md`](AGENTS.md) for end-to-end operational instructions,
  statement-fidelity checks, and Palomar agent-protocol safety rules.

## Citing Formal Conjectures

If your formalization builds on a statement from Formal Conjectures, please keep the
`related_formalizations` entry in `formalization.yaml` and consider citing:

```bibtex
@article{FormalConjecturesPaper,
  authors = {Firsching, Moritz and Lezeau, Paul and Mercuri, Salvatore
    and Horv{\'a}th, Mikl{\'o}s Z and Dillies, Ya{\"e}l and S{\"o}nne, Calle and Wieser, Eric and
    Zhang, Fred and Hubert, Thomas and Ag{\"u}era y Arcas, Blaise and Kohli, Pushmeet},
  title = {{F}ormal {C}onjectures: {A}n {O}pen and {E}volving {B}enchmark for {V}erified {D}iscovery in {M}athematics},
  year = {2026},
  url = {https://arxiv.org/abs/2605.13171v1},
}
```

## Licensing

Copyright 2025–2026 The Formal Conjectures Authors. Licensed under the Apache License, Version 2.0
(see [`LICENSE`](LICENSE)). Keep `project.license: "Apache-2.0"` in `formalization.yaml` aligned
with the root `LICENSE` file.
