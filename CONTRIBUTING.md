# How to contribute

We'd love to accept your patches and contributions to this project. Contributions
of all kinds are welcome, from adding new formalisations to fixing inaccuracies.

## Before you begin

### Sign our Contributor License Agreement

Contributions to this project must be accompanied by a
[Contributor License Agreement](https://cla.developers.google.com/about) (CLA).
You (or your employer) retain the copyright to your contribution; this simply
gives us permission to use and redistribute your contributions as part of the
project.

If you or your current employer have already signed the Google CLA (even if it
was for a different project), you probably don't need to do it again.

Visit <https://cla.developers.google.com/> to see your current agreements or to
sign a new one.

### Review our community guidelines

This project follows
[Google's Open Source Community Guidelines](https://opensource.google/conduct/).

## Ways to contribute

1. **Formalise a problem.** You can find problem lists ready to be worked on in
   our [list of Milestones](https://github.com/google-deepmind/formal-conjectures/milestones).
   You can also filter by the AMS 2020 Classification (e.g.
   [Group Theory Issues](https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22ams-20%20Group%20theory%20and%20generalizations%22))
   or take a look at
   [good first issues](https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue%20is%3Aopen%20no%3Aassignee%20label%3A%22good%20first%20issue%22)
   if you are new to Lean. Browse
   [unassigned new conjectures](https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue+is%3Aopen+no%3Aassignee+label%3A%22new+conjecture%22)
   and comment on the issue (e.g., "I plan to work on this") to have it
   assigned to you.

   More generally, we encourage adding formalisations of open conjectures from
   all sorts of sources, including:

   - **Literature:** textbooks, problem books and research papers (including
     [arXiv](https://arxiv.org/archive/math)).
   - **Community resources:**
     [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics),
     [MathOverflow](https://mathoverflow.net/) and the
     [OEIS](https://oeis.org/).
   - **Problem lists:** Famous collections
     ([Millennium](https://www.claymath.org/millennium-problems/),
     [Smale](https://en.wikipedia.org/wiki/Smale%27s_problems), Yau),
     [Erdős Problems](https://www.erdosproblems.com/),
     [Ben Green's list](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf),
     [Kourovka notebook](https://arxiv.org/pdf/1401.0300) or
     [The Scottish Book](https://en.wikipedia.org/wiki/Scottish_Book).

   We are also interested in the formalised statements of solved variants of
   open conjectures and solved statements from dedicated problem lists. While
   the main goal is to collect conjecture statements, we appreciate the
   inclusion of very short proofs for solved items or counterexamples,
   especially if they are illuminating and testing the definitions.
   **Longer proofs (i.e. more than 25-50 lines) are not to be included in this
   repository.** Instead, we welcome you to host your proof in your own
   repository and link to it using the `formal_proof` mechanism described
   below. This does not apply to `FormalConjecturesForMathlib`, where we want
   all statements to have proofs.

2. **Open issues** describing problems you'd like to see formalised. Such an
   issue should contain links to suitable references, and ideally a precise
   informal statement of the conjecture.

3. **Improve referencing and tagging** of existing problems — for example,
   adding pointers to references in already existing files, or adding
   additional relevant `AMS` subject attributes to statements.

4. **Mark a problem as solved.** If you become aware that a problem currently
   tagged `@[category research open]` has been solved, update its tag to
   `@[category research solved]` and add a `@[formal_proof using <kind> at
   "<url>"]` attribute pointing to the proof (formal or informal). See
   [The `@[formal_proof]` attribute](#the-formal_proof-attribute) for the
   accepted `<kind>` values.

5. **Fix misformalisations.** PRs fixing incorrect formal statements and issues
   flagging problems are especially appreciated.

## Contribution process

1. **Sign the [Google CLA](https://cla.developers.google.com/)** (required
   once per contributor).
2. Open a GitHub issue describing your planned contribution (if the issue does
   not already exist).
3. Fork the
   [repository](https://github.com/google-deepmind/formal-conjectures) and
   create a branch.
4. Add your formalised conjecture(s) in `FormalConjectures` in the appropriate
   subdirectory.
5. Definitions and results which are needed to formulate the conjecture should
   be added in a separate file in `FormalConjecturesForMathlib` in the
   appropriate subdirectory.
6. Add this file to the index in `FormalConjecturesForMathlib.lean`.
7. Verify that the embedded links are not broken.
8. Ensure the project builds: `lake build`.
9. Submit a Pull Request and link it to the issue you created.

## Getting started with Lean 4

If you're new to Lean 4, install
[elan, lake, and Lean](https://leanprover-community.github.io/get_started.html),
then:

```bash
git clone https://github.com/google-deepmind/formal-conjectures
cd formal-conjectures
lake exe cache get   # download prebuilt Mathlib oleans
lake build
```

Join the
[Formal Conjectures Zulip channel](https://leanprover.zulipchat.com/#narrow/channel/524981-Formal-conjectures)
for help and discussion.

## Choosing a folder and category

### Folder

Each top-level directory under `FormalConjectures/` corresponds to where the
conjecture was sourced from. Place your file in the directory that matches the
source you cite:

- `Arxiv` — arXiv preprints.
- `Books` — books and textbooks.
- `ErdosProblems` — [erdosproblems.com](https://www.erdosproblems.com/).
- `GreensOpenProblems` — [Ben Green's open-problems list](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf).
- `HilbertProblems` — [Hilbert's problems](https://en.wikipedia.org/wiki/Hilbert%27s_problems).
- `Kourovka` — [Kourovka Notebook](https://arxiv.org/pdf/1401.0300) (group
  theory).
- `Mathoverflow` — [MathOverflow](https://mathoverflow.net/).
- `Millenium` — [Millennium Prize Problems](https://www.claymath.org/millennium-problems/).
- `OEIS` — [OEIS](https://oeis.org/).
- `OpenQuantumProblems` — open problems in quantum theory.
- `OptimizationConstants` — open problems about optimization constants.
- `Paper` — research papers not on arXiv.
- `Wikipedia` — [Wikipedia's list of unsolved problems](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics).
- `WrittenOnTheWallII` — the "Written on the Wall II" problem list.
- `Other` — anything that doesn't fit above.

If your source genuinely doesn't fit any of these, use `Other` or open an
issue to discuss adding a new top-level directory before doing so.

### Category

Pick a category tag based on the statement's current status and purpose:

- The conjecture is **open** (no accepted proof) → `@[category research open]`.
- The conjecture has been **solved** (informally accepted, or formally proved
  here or elsewhere) → `@[category research solved]`.
- It's a **textbook-level** problem included as a special case or building
  block of a research problem → `@[category textbook]`.
- The statement defines basic theory around a definition you introduced →
  `@[category API]`.
- The statement is a unit test for a definition or theorem statement →
  `@[category test]`.

See [The `@[category]` attribute](#the-category-attribute) below for the
detailed semantics of each tag.

## File structure conventions

Every `.lean` file should follow this structure:

```lean
/-
Copyright YYYY The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Problem Title
*Reference:* [source](https://…)
-/

namespace MyProblem

@[category research open, AMS 11]
theorem my_conjecture : Statement := by
  sorry

end MyProblem
```

Replace `YYYY` with the current year, and consider adding yourself to the list
of authors in the `AUTHORS` file.

## The `@[category]` attribute

A tag to mark the category of a problem statement. Every statement must have
exactly one category tag. The allowed categories are:

- `@[category research open]` — an unsolved open mathematical problem or
  conjecture for which no solution or proof is currently accepted by the
  mathematical community.
- `@[category research solved]` — a problem with an established solution. This
  includes problems that have a formal proof within this repository, a formal
  proof of an equivalent statement found elsewhere, or an informal solution
  widely accepted by experts in the field.
- `@[category textbook]` — a math problem at the high school, undergraduate,
  or graduate level. This repository targets research level problems; textbook
  problems should only be contributed if they are directly related to a
  research level problem (e.g. as a special case).
- `@[category API]` — a statement that constructs basic theory around a new
  definition.
- `@[category test]` — a "unit test" statement, useful to check e.g. new
  definitions or theorem statements.

Example:

```lean
@[category research open]
theorem foo : Transcendental ℚ (rexp 1 + π) := by
  sorry

@[category research solved]
theorem bar : FermatLastTheorem := by
  sorry
```

## The `@[formal_proof]` attribute

The `formal_proof` attribute records the existence and location of a formal
proof. This is independent of the `category` attribute and can be used with
any category.

Use `@[formal_proof using <kind> at "link"]` where `<kind>` is one of:

- `formal_conjectures` — formally proved in this repository (link to commit).
- `lean4` — formally proved in Lean 4 elsewhere (e.g. Mathlib or another
  repository).
- `other_system` — formally proved in another formal system (Rocq, Isabelle,
  etc.).

```lean
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/example"]
theorem some_problem : ... := by
  sorry
```

## The `@[AMS]` attribute

The `AMS` tag provides information about the mathematical subjects a given
statement is related to. We use the main subjects listed in the
[AMS MSC2020](https://mathscinet.ams.org/mathscinet/msc/pdfs/classifications2020.pdf).
Every statement must have at least one `AMS` subject tag.

```lean
@[AMS 11]      -- Number theory
@[AMS 5 11]    -- Combinatorics + Number theory
```

Within a Lean file, you can use the `#AMS` command to list all the possible
values. To determine the subject associated to a tag in VS Code, you can hover
over the number.

## The `answer( )` elaborator

Some open questions are formulated in a way that requires a user-provided
answer, for instance the
[Hadwiger–Nelson problem](https://en.wikipedia.org/wiki/Hadwiger%E2%80%93Nelson_problem)
asks for the minimum number of colours needed to colour the plane such that
no two points exactly one unit distance apart have the same colour. The
`answer( )` elaborator allows us to formulate the problem without deciding
for an answer.

```lean
@[category research open]
theorem HadwigerNelsonProblem :
    UnitDistancePlaneGraph.chromaticNumber = answer(sorry) := by
  sorry
```

### Problems that require answers

Note that providing a term inside the `answer( )` elaborator together with a
proof that the statement is true *does not* by itself mean that the problem
has been solved. For example, a question of the form "Which natural numbers
satisfy the predicate $P$?" might be formalised as

```lean
theorem myOpenProblem : {n : ℕ | P n} = answer(sorry) := by
  sorry
```

and one can provide trivial answers that aren't mathematically interesting,
e.g. the set `{n : ℕ | P n}` itself. The question of whether the answer
provided corresponds to a mathematically meaningful solution of the problem
is outside of the scope of this repository.

## Style guidelines

- One problem per file (variants and special cases may share a file).
- Include a reference comment linking to the source of the conjecture.
- Use `theorem` or `lemma` for problem statements.
- Bespoke definitions are allowed when they help clarify problem statements;
  add basic API tests for them.
- Every statement should have at least one `AMS` subject tag.
- Every file should be put in the corresponding directory of the repository,
  e.g. a problem sourced from Wikipedia should live in
  `FormalConjectures/Wikipedia`.
- When a problem is stated as a question in English, the preferred style is
  to use `answer(sorry)`:

  ```lean
  /-- English version: "Does P hold?" -/
  theorem myConjecture : answer(sorry) ↔ P := by
    sorry
  ```

  This way the informal "Does ...", "Are there ..." or "Is it true that ..."
  corresponds to the `answer(sorry)` in the formalised statement. If the
  problem has been solved, `answer(sorry)` should be replaced by
  `answer(True)` or `answer(False)` accordingly.

  If the problem is not stated as a question, the following style is preferred:

  ```lean
  /-- English version: "P holds" -/
  theorem myConjecture : P := by
    sorry
  ```

  If the problem has been solved to the negative, then `P` should be replaced
  with `¬ P`.
- Follow the same AI usage conventions as
  [Mathlib](https://leanprover-community.github.io/contribute/index.html).

## Code reviews

All submissions, including submissions by project members, require review. We
use GitHub pull requests for this purpose. Consult
[GitHub Help](https://help.github.com/articles/about-pull-requests/) for more
information on using pull requests.

## Managing labels

Any user can add or remove certain labels on pull requests and issues by
leaving a comment. The supported labels are: `awaiting-author`, `WIP`, `Easy`,
and `documentation`.

- **To add a label**: Leave a comment with the exact label name on a line by
  itself. For example:
  ```text
  awaiting-author
  ```
- **To remove a label**: Leave a comment with `-` followed by the exact label
  name on a line by itself. For example:
  ```text
  -awaiting-author
  ```