# The verification loop

How a Formal Conjectures statement, a submitted proof and a review verdict
relate, which tool owns each step, and what has already run. This is the
architecture the tooling pull requests converge on; each piece links to where
it lives or to the decision that gates it.

## The ownership rule

One rule decides where code goes:

> FC owns semantics: statements, attributes, `answer()`, and the mapping from
> its concepts to everyone else's. lean-eval owns evaluation plumbing.
> Comparator owns proof verification. Lychee owns link checking. Agent Skills
> owns the procedure format. GitHub Actions owns scheduling.

FC keeps as little generic machinery as possible. When a step here grows
retries, sandboxes or HTTP clients, it is in the wrong place.

## The loop

One pull request flows to one report.

| step | owner | state |
|---|---|---|
| 1. PR opens | GitHub | always |
| 2. metadata identifies the statement | `FormalConjecturesUtil.Metadata` + `scripts/comparator_facts.lean` | in #4894, #4951 |
| 3. status and reference checks | `check_erdos_status.py` (#4828), lychee (#4749) | in review |
| 4. proof fetched at an immutable revision | pinned links (#4895); automation pending | partial |
| 5. workspace generated | `make_comparator_workspace.py` (#4951) | 1209 of 1217 statements |
| 6. comparator verifies proof and axioms | comparator, pins in `comparator/tools.toml` | proven, CI home is [#4930] |
| 7. review skill audits source fidelity | `formal-conjectures-review` (#4899) | measured, awaiting pilot |
| 8. one ReviewReport per PR | schema proposed on [#4394] | first instance emitted |
| 9. GitHub and dashboard render it | views over step 8 | not started, correctly |

The loop has run once, end to end, on a real pull request. #4884 claims the
proof linked from `erdos_427` is conditional on Shiu's theorem. The loop
generated the workspace, fetched the gist at its pinned revision, bridged it
into `Submission/` in two lines, and comparator rejected it:

```
Illegal axiom detected: 'External.shiu_consecutive_primes'
```

That is the PR's thesis, derived by machinery from the artifacts. The
[report](https://github.com/google-deepmind/formal-conjectures/pull/4884#issuecomment-5300370747),
the [run](https://github.com/williamjblair/formal-conjectures/actions/runs/31862100273)
and the [workflow](https://github.com/williamjblair/formal-conjectures/blob/review-loop/.github/workflows/review-loop.yml)
are public. The workflow lives on a fork branch because where such checks
belong in this repository's CI is [#4930]'s open question.

## What each layer knows

**Semantics come from the elaborator, never from parsing.**
`comparator_facts` reports a declaration's source range, its parameters with
real explicitness, and the inferred type of each `answer(sorry)` slot. Every
regex that guessed these had failure modes the environment does not; six were
found by building generated output, and the layer that held them is deleted.
The remaining Python is workspace assembly and source slicing.

**A workspace pins everything.** Mathlib from `lake-manifest.json`, FC at the
merge-base with `origin/main`, external tools in
[`comparator/tools.toml`](../comparator/tools.toml). Reproducing a 2026
verification needs those pins and the submitted bytes, not a continuously
ported proof. Maintained ports are optional and separate; snapshots are not.

**The solver's contract cannot drift.** The solver works in `Submission.lean`
with helper modules under `Submission/`; a fixed `Solution.lean` closes the
trusted statement with the Submission theorem. A submission proving anything
else does not compile. This is lean-eval's shape, taken whole.

**Ingesting an existing external proof needs a bridge.** A proof written into
a generated workspace verifies automatically. A proof written elsewhere
states its own theorem over its own definitions, sometimes on another
toolchain, and connecting it to FC's statement is a per-proof step for a
human or an agent. The 427 gist bridged in two lines because its author
matched this repository's index conventions; KnuthClaudeLean needs real
mathematics. This is the honest cost behind "ingest a GitHub link".

**Judgment stays in the skill.** Machines settle what builds, what a proof
assumes and whether statements match. Whether the Lean says what the cited
source says is the review skill's job, and its findings carry witnesses. The
skill shrinks toward orchestration as the tools grow interfaces.

## The end state

lean-eval's tooling factored into a reusable library that this repository
consumes through a small adapter, so nobody maintains a second evaluation
stack. Disproof submission is comparator's `allow_disproofs`, not an FC
protocol. Live Lean integration and a review dashboard are presentation over
the loop's records, built after the records exist.

[#4394]: https://github.com/google-deepmind/formal-conjectures/issues/4394
[#4930]: https://github.com/google-deepmind/formal-conjectures/issues/4930
