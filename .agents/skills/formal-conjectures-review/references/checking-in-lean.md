# Checking a witness in Lean

Read this when you are about to build a witness or a control. The rubrics under `../rubrics/` say what to
look for. This says how to check it, and it is mostly a list of traps that have cost real time.

## Reviewing a pull request diff

Review the complete PR head in an isolated worktree. Record the repository, head and base
commits from GitHub, and confirm that `origin` is that repository before fetching. Substitute
the PR number for `N` below. Keep the caller's checkout and local edits untouched:

```bash
gh pr view N --json headRefOid,baseRefOid,files
git fetch origin refs/pull/N/head
review_head=$(git rev-parse FETCH_HEAD)
review_parent=$(mktemp -d)
review_tree="$review_parent/checkout"
git worktree add --detach "$review_tree" "$review_head"
git -C "$review_tree" rev-parse HEAD
```

Check that the fetched head equals the head recorded from GitHub. If it changed, refresh the
PR diff and metadata before reviewing. Keep these paths and commits available across tool calls.
Read all changed files and relevant definitions from this worktree. Build there using the
command tool's explicit working-directory setting. Do not transplant individual files into
another revision or use `git checkout --` to discard local changes.

Keep scratch witnesses and evidence outside the worktree. After saving the report and checking
for any work worth preserving, remove only this review worktree, without force:

```bash
git worktree remove "$review_tree"
rmdir "$review_parent"
```

If removal refuses because the worktree has changes, preserve or inspect them; do not force it.
Report final-file line numbers rather than patch offsets. If the PR cannot be resolved, report
that scope as INCOMPLETE rather than silently reviewing a different revision.

## The scratch file

Write it outside the tree and import the module under review.

```bash
lake env lean /absolute/path/to/scratch/Witness.lean
```

Set the command's working directory explicitly to the reviewed worktree for every Lean or Lake
call. Use absolute paths for scratch files. Do not rely on a shell's directory persisting across
tool calls; an incorrect directory can select the wrong project or toolchain.

Two warnings are expected and are not failures. `linter.style.moduleDocstring` fires once for the
file. A file with more than one `/-! ... -/` section trips a second, differently worded variant
once per extra section.

## Axioms, and where a `sorry` came from

Almost every statement in this repository is `sorry`. A witness that uses one inherits it, so a
contradiction derived from two `sorry`s says nothing at all.

Run `#print axioms` on every witness and report what it returns. The useful shape is to split the
proof so the general part is clean:

```lean
theorem helper : ... := by ...          -- [propext, Classical.choice, Quot.sound]
theorem application : False := helper (TheSorriedDeclaration ...)
                                        -- [propext, sorryAx, Classical.choice, Quot.sound]
```

The helper's clean closure establishes the mathematical argument without assuming the target.
The application is a diagnostic use of the admitted target, not a sorry-free contradiction.
`#print axioms` lists dependencies; `sorryAx` alone does not identify which admission supplied it.

## Refute by proving the negation

Better than deriving a contradiction from a `sorry`ed declaration: prove its negation outright,
so nothing in your chain touches the file's `sorry`.

That leaves one gap. A reader has to trust that the statement you negated is the one in the tree.
Close it by elaborating the declaration against your transcription:

```lean
example : <the statement you wrote out> := fun x => TheDeclaration x
```

If that type-checks, it establishes type compatibility for this application. Explicitly account
for every binder and implicit argument before claiming the complete types match. Without a
connection to the target, a `sorry`-free refutation is only about your transcription.

That form does not work on `answer(sorry) ↔ RHS`, which is the commonest shape here: the header
hole resolves before the body, so `example : _ ↔ <RHS> := TheDeclaration` fails. Go through the
implication instead:

```lean
example (h : <RHS>) : True := have := TheDeclaration.mpr h; trivial
```

This checks that `<RHS>` can be passed to that implication. It does not recover the original
answer hole or prove exact correspondence of the complete declaration. For that, use an
available FC exporter that preserves answer annotations and checks the extracted type in Lean.
If exact correspondence cannot be established, report the limitation instead of claiming it.

## What actually reduces

`decide` fails more often than you expect, and the failure is usually a stuck instance rather
than a real obstruction.

| | |
|---|---|
| `Nat.Full` | has a `Decidable` instance that does not reduce; it gets stuck on `List.decidableBAll` over `primeFactorsList`. Use `Full.zero_right`, `Full.one_right` and the `primeFactorsEq` dsimproc in `FormalConjecturesForMathlib/Data/Nat/Full.lean`, or `norm_num [Nat.Full, Nat.primeFactors, Nat.primeFactorsList]` with `set_option maxRecDepth 4000`; the default 512 fails |
| `Equiv.Perm.IsCycle` | no instance. `List.formPerm` on a nodup `List` builds the permutation, but `List.isCycle_formPerm` and `List.support_formPerm_of_nodup` do **not** reduce at realistic sizes: one review lost forty minutes to them timing out at 27 vertices, another got a witness out of them. Treat them as worth one attempt, not as the recipe. What worked at 27 and 125 vertices: give each cycle as an explicit literal `List`, check a hand-rolled walk predicate with a hand-rolled `Decidable`, test `∀ y, y ∈ L` rather than any `Finset` equality, and build the `Equiv.Perm` from the step map with an explicit inverse |
| `Collinear ℝ` | no instance. Three integer points are collinear exactly when the integer cross product vanishes, so a control runs outside Lean and you say so |
| `tsum` / `Filter.limsup` | junk-valued rather than undecidable: `∑' n, f n` is `0` when `f` is not `Summable`, and `limsup` over `ℝ` is `sInf ∅ = 0` on an unbounded sequence. Nothing fails. In a *bound* it weakens the statement. In the admissibility predicate of an `∃ a, Admissible a ∧ P a` it does the opposite and makes the existential easier to satisfy, which can turn a `research open` statement provable. Prefer `HasSum` when you propose a fix, and check the source's own example still satisfies it |
| `Finset.univ` for a pi type | fine as a binder, `∀ v : Fin 3 → ZMod m, P v` enumerates; not fine as a *value* in an equality, because `Fintype.piFinset` does not reduce in the kernel. That distinction decides whether a combinatorial control finishes |
| `Function.iterate` at a literal | pathological. Eight applications of a step map timed out on their own. Phrase a control as a list, not as iterate-`n`-times |
| membership in a `Set` | `decide` cannot see through `x ∈ {m | P m}` and reports `failed to synthesize Decidable`. Peel with `Set.mem_setOf_eq` first. Since `sInf {m | ...}` is the canonical shape here, this is the trap you will hit most |
| a repo-local `def ... : Prop` | instance search will not unfold it, and `∃!` does not resolve either. Both need a two-line `decidable_of_iff _ Iff.rfl` shim before `decide` fires |
| `Nat.choose` | unfolds by Pascal recursion, so `decide` on `C(120, 5)` walks about `10^8` nodes and never returns. Rewrite with `Nat.choose_eq_descFactorial_div_factorial`, which evaluates in `k` multiplications |
| `sInf ∅` emptiness | show the set is `∅` with `ext m; simp`, then `simpa [f] using congrArg sInf h`. Watch for `simp` closing the goal without using your hypothesis; the `unusedSimpArgs` linter is what catches that, and without it you ship a witness that proves nothing about the case you meant |

Before you give up on Lean, look for the constructive encoding. A missing instance is not the end
of the road.

## Finding the lemma

Names in `FormalConjecturesForMathlib` are hard to guess, and the namespace structure is not what
it looks like. `Nat.hasDensity_zero_of_finite` sits inside `namespace Set`, but `end Set.HasDensity`
closes `Set` first, so it is not `Set.Nat.*`. Grep the `namespace` and `end` lines of the file
before guessing a full name.

Two gaps that have each cost a review most of its time:

- **`Set.HasDensity` has no complement and no cofinite lemma.** The natural witness, that a
  cofinite set cannot have density `0`, needs `partialDensity S b + partialDensity Sᶜ b = 1`
  proved from the definition. Budget for it, and consider upstreaming the result.
- **An `sSup` bound does not instantiate for free.** A lemma bounding `sSup S` gives you nothing
  about a particular member until you have `BddAbove S`, because an unbounded `sSup` over `ℕ` is
  `0`. A statement about a degenerate definition can be weaker than it reads.

## Controls that finish

A control that does not terminate is not evidence.

If the paper ships code, inspect and run its program in an isolated execution environment, then
check the output against the Lean predicate. Keep external code away from the trusted verifier
workspace. A search you write yourself may not terminate on the smallest interesting case,
and this is not hypothetical: an annealing search for one even case ran hundreds of thousands of
iterations and found nothing, while the paper's own program produced it immediately.

For a density or coverage sieve, hold the sieve as one big integer and use shifts with
`.bit_count()`. Indexing it bit by bit is quadratic and will time out around `10^7`.
