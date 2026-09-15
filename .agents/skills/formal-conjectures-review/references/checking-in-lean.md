# Checking a witness in Lean

Use this for manual review setup or a targeted witness. For a prepared review, use the workflow's
execution interface and retained inputs instead of recreating its checkout, sources or build.

## Manual review inputs

Record the repository and exact target. For local changes, read `git status --short` and capture
the intended diff, including staged edits and any included new files. Record the base explicitly;
do not assume every review compares with `origin/main`. Preserve the branch, index and files.

For a PR, use the isolated checkout below. Build the affected modules with
`lake --wfail build 'FormalConjectures.<Dir>.«N»'`, or use matching CI evidence that records that
scope and revision. Keep the command and outcome. Do not rerun broad CI or lint sweeps.
A worktree separates Git state; it is not a sandbox. Use trusted execution tooling for candidate
code, and do not let candidate configuration choose the recorded build command or dependencies.
If that execution path is unavailable, report the build as not run.

Retrieve the cited passages with bounded requests. For Erdős pages, use `/latex/<n>` with a
named user agent; for PDFs, use `pdftotext -layout`. Keep the URL, retrieval time and passages
used. If retrieval fails, record the gap and stop; do not crawl unrelated sources to fill it.

## Reviewing a pull request diff

Review the complete PR head in an isolated worktree. Record the repository, head and base
commits from GitHub, and select a remote for that repository before fetching. Substitute the
PR number, repository and remote below. Keep the caller's checkout and local edits untouched:

```bash
gh pr view N --repo OWNER/REPO --json headRefOid,baseRefOid,files
git fetch REMOTE refs/pull/N/head
review_head=$(git rev-parse FETCH_HEAD)
review_parent=$(mktemp -d)
review_tree="$review_parent/checkout"
git worktree add --detach "$review_tree" "$review_head"
git -C "$review_tree" rev-parse HEAD
```

Check that the fetched head equals the head recorded from GitHub. If it changed, refresh the
PR diff and metadata before reviewing. Keep these paths and commits available across tool calls.
Fetch the recorded base commit if needed, then read `git diff BASE_COMMIT...HEAD_COMMIT` and
the complete changed files from this worktree. Retain both tips and their merge base. If the
recorded commits cannot be retrieved, report that gap rather than substitute another base.
Do not transplant individual files into another revision or discard local changes.

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

Use the workflow's isolated scratch tools when supplied. Otherwise, keep the witness outside
the source tree and import the module under review in the trusted execution environment:

```bash
lake env lean /absolute/path/to/scratch/Witness.lean
```

Set the working directory explicitly to the reviewed project and use absolute scratch paths.
Keep witness results separate from the independent candidate build. Identify any scratch-only
linter warnings; do not suppress warnings in the reviewed modules.

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

Reduction and available lemmas depend on the recorded Lean and dependency versions. Search
Mathlib and `FormalConjecturesForMathlib/` with `rg`, then confirm names and types with `#check`.
Do not infer a mathematical obstruction from a missing instance or timeout.

- Prefer existing lemmas to large `decide` computations. For `Nat.Full`, search
  `FormalConjecturesForMathlib/Data/Nat/Full.lean` for the boundary lemmas and simplification API.
- Unfold a local predicate or set membership when it hides a decidable proposition. Confirm
  the resulting predicate still matches the claim being checked.
- For finite combinatorial controls, an explicit list or step map can avoid expensive
  permutation, function-space or iteration reduction. Retain the connection to the Lean predicate.
- For a large binomial coefficient, check whether `Nat.choose_eq_descFactorial_div_factorial`
  avoids recursive expansion in the pinned version.
- Check the boundedness and membership hypotheses of `sSup`/`sInf` lemmas before applying them
  to a particular element. The [soundness rubric](../rubrics/statement-soundness.md#known-definition-traps)
  covers total functions' values outside their intended domain.

## Controls that finish

A control that does not terminate is not evidence.

When a finding depends on a source construction and the paper supplies code, inspect it and
use a bounded isolated run if authorized. Check its output against the Lean predicate and keep
external code away from trusted build and verifier state. Label external computation as such;
it is not a Lean proof. If the control cannot finish within the budget, retain the failure and
report the unresolved claim instead of starting an open-ended search.
