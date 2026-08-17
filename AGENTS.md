# Agent guidelines

Formal Conjectures states open mathematical problems in Lean 4. It is a statement
repository, not a proof repository: almost every problem is `sorry`. Each statement must say
what its source says.

[CONTRIBUTING.md](CONTRIBUTING.md) is the reference for conventions, folders, and the
attributes. This file adds only what CONTRIBUTING does not tell you.

Follow the style of an existing file. Start by copying one from the same directory. *File
structure conventions* in CONTRIBUTING gives the skeleton, and a neighbouring file gives the
rest: a definition with its docstring, a statement with its source, and a variant. A template
can become incorrect. A file in the repository cannot, because the build compiles it.

## Commands

Build only the modules that you changed. Do not build the project.

```bash
lake --wfail build 'FormalConjectures.ErdosProblems.«361»'
```

```bash
lake --wfail build FormalConjecturesForMathlib   # if you changed a shared definition
lake --wfail test                                # if you changed FormalConjecturesUtil
lake --wfail build                               # the whole project. Let CI do this.
```

`--wfail` makes each warning into a failure. CI uses the same option. Two warnings cause most
of these failures:

- `open Classical` causes the `linter.style.openClassical` warning. Write
  `open scoped Classical in` before the declaration that needs it. As an alternative, supply
  a `Decidable` instance.
- The AMS tags must be in ascending order. Write `AMS 15 51`. Do not write `AMS 51 15`.

## Where to put a statement

Put a problem in `FormalConjectures/<Source>/`. Use one file for each problem. Give the file
the name of the problem. Put reusable mathematics in `FormalConjecturesForMathlib/`. That
directory must not contain `sorry`. Only `FormalConjectures/` can contain `sorry`.

Search before you write a definition. Mathlib, `FormalConjecturesForMathlib/` and the adjacent
problem files already contain much of what a problem needs. The names are difficult to guess.
Examples: `trianglesContaining`, `InGeneralPosition`, `NonTrilinear`, `distinctDistances`. The
notation is also easy to miss: `ℝ²` for `EuclideanSpace ℝ (Fin 2)`, and `≪` for `IsBigO` at
`atTop`.

## Check the degenerate cases

Most incorrect formalisations are not typographical errors. They are statements that are
vacuous, or trivially true, or false on an input that the author did not think about. Lean
gives a junk value in these cases. Thus the file compiles, and the statement continues to read
correctly. Test the smallest inputs and the empty inputs:

| | |
|---|---|
| empty type or set | `∑ i, f i = 0`. Also, `X → ℝ` is a subsingleton. Thus two conditions that look contradictory can both hold |
| `ZMod 0` | This type is `ℤ`. It is not a finite modulus |
| `x / 0` | The result is `0`. Thus `∃ m : ℤ, q = m` accepts a pole as an integer. Write `a ∣ b` |
| `sInf ∅` | The result is `0`. Thus the least such `n` is `0` when no `n` qualifies |
| `Nat` subtraction | The result truncates to zero |

Some statements are correct only because of a hypothesis such as `0 < N`, `[Nonempty X]` or
`2 ≤ n`. Write one sentence in the docstring for each such hypothesis. A reviewer cannot
otherwise know which hypotheses are necessary.

## Compilation is not proof

A file that contains `sorry` compiles. Run this command before you write that a theorem is
proved:

```lean
#print axioms my_theorem
-- [propext, Classical.choice, Quot.sound]
```

`sorryAx` shows that the theorem is not proved.

The three axioms above are the bar for a `research solved` statement. A `test` statement can
use `decide +native`, which the repository prefers to `native_decide`. It adds at least
`Lean.ofReduceBool` and `Lean.trustCompiler`, and the exact set depends on the proof. These
axioms move the work out of the kernel, so run `#print axioms` and name the result in the pull
request. `decide +kernel` stays within the three axioms above, where it is fast enough.

Do the same for a proof that you cite with `formal_proof`. Read the file and look for `sorry`.
Run `#print axioms` on the theorem that you cite. Then make sure that this theorem states what
you claim. A repository can claim a proof of a conjecture and prove a weaker result. The
correct theorem frequently has a different name.

## Check your own work

Each item below caused an incorrect claim in this repository. Each check is quick.

**Read the matches. Do not count them.** A site search for `coprime` gave four results. This
looked like a search of the statement text. All four results matched the theorem *name*. A
count does not tell you why a search matched.

**`grep sorry` also matches prose.** One file had two matches for `sorry`, both in a comment
that described a plan. The file was almost recorded as incomplete. Use `#print axioms` to
decide. Use grep only to find the location.

**Look at the data before you describe it.** The claim "the statements are already in
`conjectures.json`" was incorrect. `extract_names` uses the `--exclude=statement` option, and
does not write them. Open the file.

**Measure at the correct time.** An environment probe in a later command does not show what an
attribute saw during elaboration. Lean rewinds the declaration between the two points. Add the
instrument at the point that your claim is about.

## Statement fidelity

The docstring quotes the source. The Lean must agree with the docstring. If they disagree, the
Lean is incorrect. Read these again before you submit:

- the order and the scope of the quantifiers
- `≤` against `<`, `∀ᶠ` against `∀`, asymptotic equivalence against the same order
- a hypothesis that the prose gives and the Lean omits
- `∃ x, P x → Q`. The intended statement is almost always `∃ x, P x ∧ Q`. As written, the
  statement is trivially true. A linter finds this

Prove each `test` statement and each `API` statement that you add. These statements must test
a definition. A statement that contains `sorry` tests nothing.

## Completeness

- No placeholder definitions (e.g., `def foo : Type := sorry` or `opaque foo : Type*`)
- No incomplete type annotations or holes
- All referenced definitions must exist
- All imports must be correct
- No new axioms

## Before you open a pull request

- [ ] `lake --wfail build <module>` passes for each module that you changed
- [ ] the docstring quotes the source, and the module docstring gives a reference
- [ ] each theorem has a `category` and at least one `AMS` tag, in ascending order
- [ ] you tested the degenerate inputs: empty, zero, division
- [ ] you ran `#print axioms` on each theorem that you claim is proved
- [ ] `FormalConjecturesForMathlib/` contains no `sorry`
- [ ] you ran `git status` before `git add`. Generated files and `__pycache__` are easy to add
      by mistake
- [ ] you read again each file that a script changed. A build that passes is not sufficient
- [ ] the description contains `Fixes #1, fixes #2`. Repeat the keyword. `Fixes #1, #2` closes
      only the first issue
- [ ] the description gives the formalisation decisions and the limitations. Do not put them
      in the Lean file
