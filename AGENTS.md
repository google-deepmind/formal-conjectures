# Agent guidelines

Formal Conjectures states open mathematical problems in Lean 4. It is a statement
repository, not a proof repository: almost every problem is `sorry`.

[CONTRIBUTING.md](CONTRIBUTING.md) is the reference for conventions, folders, and attributes.
Also follow any `README.md` in the directory that you change.

Use these detailed guides when the task needs them:

- [PROOFS.md](PROOFS.md) for proofs and `formal_proof` claims
- [STATEMENTS.md](STATEMENTS.md) for adding and reviewing statements

## Start with existing code

Follow the style of an existing file. Start by copying one from the same directory.

Search Mathlib, `FormalConjecturesForMathlib/`, and nearby problem files before you add a
definition, API, or notation. Search names and documentation with `rg`. Use `#check` to confirm
the type of a candidate declaration.

Put each problem in `FormalConjectures/<Source>/`. Keep closely related variants in the same
file. Put reusable mathematics in `FormalConjecturesForMathlib/`. That directory must not
contain `sorry`.

Problem files normally import only `FormalConjecturesUtil`.
`FormalConjecturesForMathlib/` files import only the required Mathlib modules.

## State the source faithfully

Read the cited source. Make the Lean statement, its docstring, and the source agree. Check the
order and scope of quantifiers, bounds, hypotheses, and all variants. Test empty and smallest
inputs. See [STATEMENTS.md](STATEMENTS.md) for the detailed checks.

Use `answer(sorry)` only for the information that the problem asks to determine. Put all
quantifiers after it. A tautological term inside `answer()` is not a mathematical solution.

## Write clear documentation

Write documentation in simple, concise technical English. Prefer short sentences, common
words, and one instruction or claim per sentence. Remove repetition and details that do not
help a contributor complete the task.

Use the same style for all repository communication. This includes issues, pull requests,
reviews, and comments.

Give each module a docstring with its sources. Give each `research open`, `research solved`,
and `textbook` theorem a concise docstring that states the problem. Explain a non-obvious domain
restriction when it is needed to exclude a degenerate case.

Use LaTeX for mathematics in problem docstrings. Use code formatting for Lean and Mathlib API
names. Do not put review notes or a proposed proof of an open problem in a Lean file.

## Keep the Lean simple

- Follow Mathlib naming conventions.
- Use local notation for notation that is specific to one problem.
- Omit type annotations that Lean can infer.
- Write placeholders as `by sorry`.
- Keep AMS tags in ascending order, such as `AMS 15 51`.
- Do not use a global `open Classical`. Use `open scoped Classical in` or provide a local
  `Decidable` instance.
- Do not add placeholder definitions, incomplete types, unused imports, debug code, or commented
  out code.

## Build the changed scope

Build every module that you change. Do not build the whole project locally for a problem-file
change.

```bash
lake --wfail build 'FormalConjectures.ErdosProblems.«361»'
```

Use the wider target only when the changed scope requires it:

```bash
lake --wfail build FormalConjecturesForMathlib  # shared definitions
lake --wfail test                               # repository utilities
```

`--wfail` turns warnings into failures, as CI does. Fix every warning in the changed scope.

## Write a readable pull request

Keep the pull request description concise and easy to scan. State what changed, why it changed,
and how you checked it. Include only formalisation choices, limitations, or reviewer notes that
affect the change. Remove narration, repetition, and unrelated detail.

Put reviewer notes in the pull request, not in Lean comments. To close several issues, repeat
the keyword: `Fixes #1, fixes #2`.

Before requesting review, check that:

- each changed module builds with `--wfail`
- each problem theorem has one `category` and at least one AMS tag
- module and theorem docstrings follow the source and cite it
- the statement handles its boundary cases
- `FormalConjecturesForMathlib/` contains no `sorry`
- the diff contains only intended files and changes
