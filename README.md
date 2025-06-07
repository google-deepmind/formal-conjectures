# Formal Conjectures

[![.github/workflows/push_master.yml](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml/badge.svg)](https://github.com/google-deepmind/formal-conjectures/actions/workflows/build-and-docs.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/google-deepmind/formal-conjectures)

A collection of formalized statements of conjectures in
[Lean](https://leanprover.github.io/lean4/doc/whatIsLean.html), using
[mathlib](https://github.com/leanprover-community/mathlib4).

<!--TODO(firsching): insert link to autmatically generated documentation once docgen4 works-->

## Goals

While there is a growing corpus of formalized theorems including proofs, there
is a lack of open conjectures where only the statement has been formalized. This
would be useful for a few reasons. It could

*   Become a great benchmark for automated theorem provers and automated
    formalization tools.
*   Help clarify the precise meaning of conjectures through formalization.
*   Encourage the expansion of `mathlib` by highlighting needed definitions.

It is our hope that this initiative will form the seed of a much richer dataset of
formalized conjectures.

### Note on Formalisation Accuracy

Formalizing mathematical statements without proofs is inherently challenging.
Subtle inaccuracies can arise where the formal statement might not perfectly
capture the nuances of the original conjecture. To mitigate this issue, we will
rely on careful human review of contributions, and plan to periodically leverage
AlphaProof to help identify potential misformalisations.

## Contributing

Contributions are most welcome, consider adding (or even just opening an issue
describing) your favorite conjecture.

### I'd like to contribute - what can I do?

There are various ways of contributing to this repository:

1.  **Adding new problem formalisations**

    Unlike other conjecture lists (the Millenium problems, Smale's list, Yau's
    problems, ...) the problems in this repo can come from various places and we
    encourage all sorts of contributions. For example, conjectures can be
    sourced from various places, including:

    *   Mathematical Textbooks
    *   Research Papers (including preprints on the
        [arxiv](https://arxiv.org/archive/math))
    *   [MathOverflow](https://mathoverflow.net/) Questions
    *   Dedicated Problem Lists (e.g.,
        [Erdős Problems](https://www.erdosproblems.com/),
        [Wikipedia's list of unsolved problems](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics),
        [the Scottish Book](https://en.wikipedia.org/wiki/Scottish_Book), ...)
    *   ...

    We are also interested in the formalized statements of solved variants of
    open conjectures and solved statements from dedicated problem lists.
    While the main goal is to collect conjecture statements, we appreciate the
    inclusion of very short proofs for solved items or counterexamples,
    especially if they are illuminating and testing the definitions.
    Lengthy proofs are outside the scope of this repository.

2.  **Opening issues with problems that you would like to see formalised.** Such
    an issue should contain links to suitable references, and ideally a precise
    informal statement of the conjecture.

3.  **Improving the referencing and tagging of problems.** For example, adding
    pointers to references in already existing files, or adding additional
    relevant `AMS` subject attributes to statements.

4.  **Fixing misformalisations.** PRs fixing incorrect formalisations and issues
    flagging problems are encouraged.

### How to Contribute

Please see [CONTRIBUTING](./CONTRIBUTING.md) first.

1.  Open an issue on GitHub specifying what you plan to contribute (and assign
    yourself!)
2.  Fork the repository on GitHub.
3.  Add your formalized conjecture(s) in the appropriate file/directory
    structure to a branch in your fork.
    *   Include comments linking to the source of the conjecture (paper,
        website, book).
    *   Use the `category` attribute to specify what category each of the
        statements falls into (see below for more details on this.)
    *   Use the `AMS` attribute to specify what mathematical areas each of the
        statements are related to.
4.  Ensure the code builds (`lake build`).
5.  Submit a Pull Request to the main repository.

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

The directory structure is organized by the type of sources of the conjectures.
There are two special directories:

-   `Util` contains utilities like the
    [`category` attribute](./FormalConjectures/Util/Attributes.lean), the
    [`answer( )` elaborator](./FormalConjectures/Util/Answer.lean) and some
    linters.
-   `ForMathlib` contains code potentially suitable to be upstreamed to
    [mathlib](https://github.com/leanprover-community/mathlib4). Here we follow
    mathlib's directory structure.

### Some features

#### The `category` attribute

A tag to mark the category of a problem statement. In this repository, we allow
for the following categories:

-   Open research problem: a mathematical problem for which there is no solution
    accepted by the community.
-   Solved research problem: a mathematical problem that has an accepted
    solution (in the sense that it is widely accepted by experts in the field).
    In particular this does *not* mean that the statement has been proven in the
    formal setting.
-   Graduate level problem.
-   Undergraduate level problem.
-   High school level problem.
-   API statement: a statement that constructs basic theory around a new
    definition.
-   Test statement: a statement that serves as a "unit test". These are useful
    to check e.g new definitions or theorem statements.

This repository targets research level problems. As such, graduate/
undergraduate/high school level problems should only be contributed if they
are directly related to a research level problem (e.g. as a special case,
etc.).

The tags should be used as follows:

```lean
@[category research open]
theorem foo : Transcendental ℚ (rexp 1 + π) := by
  sorry

@[category research solved]
theorem bar : FermatLastTheorem := by
  sorry

```

#### The `AMS` attribute

The `AMS` tag is intended to provide some information about the mathematical
subjects a given statement is related to. For simplicity, we use the main
subjects listed in the
[AMS MSC2020](https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf).

The tag can be used as follows:

```lean
@[AMS 11] -- `11` means "Number Theory"
theorem flt : FermatLastTheorem := by
  sorry
```

Within a Lean file, you can use the `#AMS` command to list all the possible
values.

To determine the subject associated to the tag `AMS foo` in VS Code, you can hover
over `foo`.

The attribute allows multiple parameters, e.g. `@[AMS foo bar]` is valid.

#### The `answer( )` elaborator

Some open questions are formulated in a way that require a user provided answer,
for instance the
[Hadwiger–Nelson problem](https://en.wikipedia.org/wiki/Hadwiger%E2%80%93Nelson_problem)
asks for the minimum number of colors needed to color the plane such that no two
points exactly one unit distance apart have the same color. The `answer( )`
elaborator allows us to formulate the problem without deciding for an answer.

```lean
@[category research open]
theorem HadwigerNelsonProblem :
    IsLeast {n : ℕ | ExistsColoring n} answer(sorry) := by
  sorry
```

## Problems that require answers

Note that providing a term inside the `answer( )` elaborator together with a proof that
the statement is true *does not* by itself mean that the problem has been solved. For example, a question
of the form "Which natural numbers satisfy the predicate $P$?" might be formalised as
```lean
theorem myOpenProblem : {n : ℕ | P n} = answer(sorry) := by
  sorry
```
and one can provide trivial answers that aren't mathemetically interesting, e.g. the set
`{n : ℕ | P n}` itself.

In particular, the question of whether the answer provided corresponds to a mathematically
meaningful solution of the problem is outside of the scope of this repository.

## Style Guidelines

1.  Generally speaking, every problem should have its own file, though there is
    some flexibility here (e.g. variants and special cases should go in the same
    file).
2.  Bespoke definitions are allowed, as long as they help clarify problem
    statements. We also encourage contributors to provide some very basic API
    for such definitions as a way to test whether these behave as expected.
3.  Benchmark problems should be stated with the `theorem` keyword, while for
    test statements `example` is usually prefered.
4.  Every statement should have at least one `AMS` subject tag.
5.  Every file should come with a reference to where the problem was sourced
    from, and be put in the corresponding directory of the repository, e.g. a
    problem sourced from wikipedia should live in `FormalConjectures/Wikipedia`.
6.  When a problem is stated as a question in English, the preferred style is to
    use `answer(sorry)` in the following way:
    ```lean
    /-- English version: "Does P hold ?" -/
    theorem myConjecture : P ↔ answer(sorry) := by
      sorry
    ```
    If the problem has been solved, `answer(sorry)` should be replaced by
    `answer(True)` or `answer(False)` accordingly.
    If the problem is not stated as a question, the following style is preferred:
    ```lean
    /-- English version: "P holds" -/
    theorem myConjecture : P := by
      sorry
    ```
    If the problem has been solved to the negative, then `P` should be replaced with
    `¬ P`.
7.  Every file should start with the following copyright header:
    ```lean
    /-
    Copyright 2025 The Formal Conjectures Authors.

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

        https://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
    -/
    ```
    Also consider adding yourself to the list of authors in the AUTHORS file.


## Versioning

This repo will track the monthly tagged releases of mathlib (which correspond to
Lean releases), rather than tracking mathlib master.

To minimize friction when adding problem statements that need definitions that
are not yet in mathlib, such definitions can be added to the `ForMathlib`
directory. This ensures that the addition of these problems to
formal-conjectures is not locked to the mathlib release cadence.

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

-   Material from Wikipedia articles and MathOverflow is released under the
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
