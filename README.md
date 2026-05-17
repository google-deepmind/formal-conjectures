# Formal Conjectures

[![.github/workflows/push_master.yml](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml/badge.svg)](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/google-deepmind/formal-conjectures)

A collection of formalised statements of conjectures in
[Lean](https://leanprover.github.io/lean4/doc/whatIsLean.html), using
[mathlib](https://github.com/leanprover-community/mathlib4).

Explore the docs: [Formal Conjectures Documentation](https://google-deepmind.github.io/formal-conjectures/)

Join our [channel on the leanprover Zulip](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)

## Goals

While there is a growing corpus of formalised theorems including proofs, there
is a lack of open conjectures where only the statement has been formalised. This
would be useful for a few reasons. It could

*   Become a great benchmark for automated theorem provers and automated
    formalisation tools.
*   Help clarify the precise meaning of conjectures through formalisation.
*   Encourage the expansion of `mathlib` by highlighting needed definitions.

It is our hope that this initiative will form the seed of a much richer dataset of
formalised conjectures.

### Note on Formalisation Accuracy

Formalizing mathematical statements without proofs is inherently challenging.
Subtle inaccuracies can arise where the formal statement might not perfectly
capture the nuances of the original conjecture. To mitigate this issue, we will
rely on careful human review of contributions, and plan to periodically leverage
AlphaProof to help identify potential misformalisations.

## Contributing

Contributions are most welcome — consider adding (or even just opening an issue
describing) your favourite conjecture. See [CONTRIBUTING.md](./CONTRIBUTING.md)
for the full contribution guide, including ways to contribute, the
step-by-step process, file structure conventions, attribute usage, and style
guidelines.

## Usage, Structure & Features

This is a Lean 4 project managed with `lake` and a dependency `mathlib`. You
first need to
[install elan, lake, lean and if you want vscode](https://leanprover-community.github.io/get_started.html)
and then run

```bash
lake exe cache get
lake build
```

### Directory structure

The directory structure is organised by the type of sources of the conjectures.
There are two special directories:

-   `FormalConjectures/Util` contains utilities like the
    [`category` attribute](./FormalConjectures/Util/Attributes/Basic.lean), the
    [`answer( )` elaborator](./FormalConjectures/Util/Answer.lean) and some
    linters.
-   `FormalConjecturesForMathlib` contains code potentially suitable to be upstreamed to
    [mathlib](https://github.com/leanprover-community/mathlib4). Here we follow
    mathlib's directory structure.

For details on the `@[category]`, `@[formal_proof]`, `@[AMS]` attributes and
the `answer( )` elaborator that statements in this repository use, see
[CONTRIBUTING.md](./CONTRIBUTING.md).

## Versioning

This repo will track the monthly tagged releases of mathlib (which correspond to
Lean releases), rather than tracking mathlib master.

To minimize friction when adding problem statements that need definitions that
are not yet in mathlib, such definitions can be added to the `FormalConjecturesForMathlib`
directory. This ensures that the addition of these problems to
formal-conjectures is not locked to the mathlib release cadence.

When `lean-toolchain` is updated on `main`, a GitHub Actions workflow
automatically adds a git tag of the form `v4.{X}.{Y}`, following mathlib's
tagging convention.

Stable benchmark snapshots are tagged using the format
`bench-v{N}-lean4.{X}.{Y}`, where:

-   **`v{N}` (Benchmark version):** Identifies the set of problems included in
    the benchmark. The benchmark version is bumped whenever problems are added,
    removed, or when misformalizations are corrected.
-   **`lean4.{X}.{Y}` (Lean version):** Identifies the Lean 4 toolchain
    version used for that snapshot.

Tags are immutable: fixes to misformalizations are never patched into an existing
benchmark version but instead go into `v{N+1}`.

## Citing formal-conjectures
If your work has used formal-conjectures, please consider citing it via
```
@misc{FormalConjectures,
  author       = {The Formal Conjectures Authors}
  title        = {{T}he {F}ormal {C}onjectures {R}epository},
  year         = {2025},
  url          = {https://github.com/google-deepmind/formal-conjectures},
}

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

Copyright 2025 The Formal Conjectures Authors. All software is licensed under the Apache License,
Version 2.0 (Apache 2.0); you may not use this file except in compliance with
the Apache 2.0 license. You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode.

The content may be based on third party sources and may in some cases include
third party content. The original source for each conjecture is indicated by a
URL within the source file. Third party content may be subject to different
licensing requirements. In particular:

-   Material from Wikipedia articles, MathOverflow and the OEIS is released under the
    Creative Commons Attribution-Share-Alike License 4.0.
-   Material from bbchallenge.org is used under the Creative Commons Attribution
    4.0 International License.
-   Material from the Equational Theories Project is used under Apache-2.0.
-   Material from arXiv is used under the licence applicable to the relevant
    paper, as indicated at the URL within the source file.

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY license are distributed
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.
