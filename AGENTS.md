# Agent guidelines

Formal Conjectures states open mathematical problems in Lean 4. It is a statement
repository, not a proof repository: the value is in the statement saying what the source
says, and almost every problem is `sorry`.

[CONTRIBUTING.md](CONTRIBUTING.md) is the reference for conventions, folders, and the
attributes. This file is what an agent needs on top of it.

## Commands

Build the module you touched, not the project:

```bash
lake --wfail build 'FormalConjectures.ErdosProblems.«361»'
```

Quote it. The guillemets in a numbered file are part of the module name.

```bash
lake --wfail build FormalConjecturesForMathlib   # if you changed a shared definition
lake --wfail test                                # if you changed anything under FormalConjecturesUtil
lake --wfail build                               # over an hour; leave it to CI
```

`--wfail` turns warnings into failures, which is how CI runs. Two that catch people out:

- `open Classical` trips `linter.style.openClassical`. Use `open scoped Classical in` on the
  declaration that needs it, or a `Decidable` instance.
- AMS tags must be ascending: `AMS 15 51`, not `AMS 51 15`.

## Where a statement goes

`FormalConjectures/<Source>/` for problems, one file per problem, named for it. Reusable
mathematics goes in `FormalConjecturesForMathlib/`, which must be `sorry`-free. `sorry` is
expected in `FormalConjectures/` and nowhere else.

Search before you define. Much of what a problem needs is already in Mathlib, in
`FormalConjecturesForMathlib/`, or in a neighbouring problem file, under a name you would not
guess: `trianglesContaining`, `InGeneralPosition`, `NonTrilinear`, `distinctDistances`.

## Check the degenerate cases

The usual way a formalisation is wrong is not a typo. It is a statement that is vacuous,
trivially true, or false on an input nobody pictured, and Lean's junk values hide it because
the file still compiles and still reads well. Try the smallest and emptiest inputs:

| | |
|---|---|
| empty type or set | `∑ i, f i = 0`, and `X → ℝ` is a subsingleton, so contradictory-looking conditions can both hold |
| `ZMod 0` | it is `ℤ`, not a finite modulus |
| `x / 0` | it is `0`, so `∃ m : ℤ, q = m` counts a pole as an integer. Say `a ∣ b` instead |
| `sInf ∅` | it is `0`, so a "least such `n`" is `0` when nothing qualifies |
| `Nat` subtraction | it truncates at zero |

If a hypothesis such as `0 < N`, `[Nonempty X]` or `2 ≤ n` is what keeps the statement
honest, say so in a sentence in the docstring. A reviewer cannot otherwise tell a
load-bearing hypothesis from a decorative one.

## Compiling is not proving

A file containing `sorry` compiles. If you claim something is proved, check:

```lean
#print axioms my_theorem
-- [propext, Classical.choice, Quot.sound]
```

Anything else, `sorryAx` above all, means it is not proved.

The same applies to a proof you cite with `formal_proof`. Read the file for `sorry`, run
`#print axioms` on the theorem you are citing, and check that its statement is the one you
are claiming. A repository saying it proves a conjecture may prove something weaker, and the
statement is often the same theorem under a different name.

## Checking your own work

Each of these has produced a wrong claim in this repository, and each is cheap to avoid.

**Read what matched, not how many.** Searching the site for `coprime` returned four results,
which looked like the search covering statement text. All four matched the theorem *name*.
A count tells you nothing about why something matched.

**`grep sorry` hits prose.** A file whose only two `sorry` matches were inside a comment
describing a plan was nearly written off as incomplete. Use `#print axioms` to decide, and
grep only to find where to look.

**Check the data before describing it.** "The statements are already in `conjectures.json`"
was wrong: `extract_names` is run with `--exclude=statement`, so they are not. Open the file.

**Measure at the right moment.** An environment probe run from a later command says nothing
about what an attribute saw while elaborating, because the declaration is rewound in between.
If a claim is about when something happens, instrument that point.

**A no-op edit looks like a successful one.** A `str.replace` whose pattern no longer matches
changes nothing and reports nothing; so does a `PATCH` that writes back identical content.
Assert that the edit landed, and re-read the file rather than the exit code.

**Shell quoting eats Lean source silently.** An unquoted heredoc expanded `` `A` `` and `$K_n`
in docstrings to nothing. The file still compiled, so only a reader noticed. Quote the
delimiter, and reread any docstring a script wrote.

**Dry-run anything that closes or deletes.** A comparison between an `int` and a set of
strings matched nothing, which would have closed 34 of 35 issues rather than the 6 intended.
Print what a destructive step would do, against real data, before letting it do it.

## Statement fidelity

The docstring quotes the source, and the Lean says exactly that. When they can differ, the
Lean is wrong. Things to reread before submitting:

- quantifier order and scope
- `≤` against `<`, `∀ᶠ` against `∀`, asymptotic equivalence against same order
- a hypothesis the prose states and the Lean drops
- `∃ x, P x → Q`, which is almost always meant as `∃ x, P x ∧ Q` and is trivially true as
  written. There is a linter for it

Prove the `test` and `API` statements you add. They exist to exercise a definition, and one
left `sorry` exercises nothing.

## Before opening a pull request

- [ ] `lake --wfail build <module>` passes for what you touched
- [ ] docstring quotes the source, with a reference in the module docstring
- [ ] every theorem has `category` and at least one `AMS` tag, in ascending order
- [ ] degenerate inputs tried: empty, zero, division
- [ ] `#print axioms` on anything claimed to be proved
- [ ] no `sorry` under `FormalConjecturesForMathlib/`
- [ ] `git status` before `git add`: generated files and `__pycache__` sweep in easily
- [ ] any file a script edited has been reread, not just rebuilt
- [ ] `Fixes #1, fixes #2` in the description, with the keyword repeated. `Fixes #1, #2`
      closes only the first
- [ ] formalisation choices and caveats in the pull request description, not in the Lean file
