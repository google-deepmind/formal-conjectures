---
name: formal-conjectures-review
description: Use when reviewing a Formal Conjectures pull request, checking whether a Lean statement says what its cited source says, or before submitting a formalisation. Use it for suspected misformalisation, boundary cases, vacuity, answer() polarity, or formal_proof claims. Produce a concise, advisory GitHub-ready review with high-confidence inline suggestions.
license: Apache-2.0
---

# Review a formalisation

This is the semantic second pass. `AGENTS.md` and CI own style and routine mechanical
checks. Answer one question: **does the Lean statement say what its cited source says?**

Use the fast path by default. It should yield either a concise review or a concrete reason to
escalate—not an audit transcript. Do not read `evals/`; it contains answer keys.

## Fast path

1. **Bind the scope.** For a named file, read the complete file and run:

   ```bash
   git status --short
   git diff origin/main -- <path>
   ```

   For a named PR, review its diff, and read the review comments already on it. Do not search
   history or overlapping PRs unless that bears on a candidate finding.

2. **Run the focused build.** From the repository root:

   ```bash
   lake --wfail build 'FormalConjectures.<Dir>.«N»'
   ```

   If it fails, report the failure and stop. Do not rerun repository CI, remote status scripts,
   or broad lint sweeps: they are separate mechanical evidence and do not belong on the semantic
   review's critical path.

3. **Read the source statement.** Read the module docstring and the cited primary source. For an
   Erdős page, fetch `/latex/<n>` with a named user agent and a bounded request. For a paper,
   extract the cited pages with `pdftotext -layout`. Read the statement and directly relevant
   qualifiers or remarks; do not read the whole document by default.

4. **Compare meanings, one angle at a time.** Three angles partition the judgement, and every
   finding names its angle:

   - **source-fidelity** — quantifiers, direction, constants, ranges against the source's words;
     the file against its own docstring.
   - **statement-soundness** — satisfiable hypotheses, junk values at a candidate boundary
     (substitute the smallest relevant value), and `answer()` polarity, self-answer, and scope.
   - **metadata-hygiene** — category against status, unfilled slots under `research solved`,
     and what a `formal_proof` link actually shows.

   Inspect only definitions that control the declaration's meaning. The angle files under
   [`rubrics/`](rubrics/) hold the hunt lists and confirmed exemplars; on the fast path this
   checklist suffices, and a rubric is read when its angle produces a candidate finding.

5. **Report or stop.** If source, Lean, and boundary checks agree, return CLEAN. If they do not,
   give a direct, bounded finding, and check its witness in Lean or by computation before filing
   it — a blocking finding whose witness is only argued is not done
   ([`references/checking-in-lean.md`](references/checking-in-lean.md)). Do not manufacture a
   witness, proof, or secondary concern.

## Escalate only when needed

Escalate when the fast path leaves a material ambiguity: a revised-source/status claim, a
conflicting imported definition, a `formal_proof` claim, an unclear boundary, or a proposed
replacement that needs validation. And escalate always, not optionally, for **any finding that
will set the verdict** — its witness gets built and checked in Lean or by computation before
the report returns. "The repository has no lemma for this" is the signal to build a scratch
witness from Mathlib, not to file the finding argued; a mismatch you can quote and a
contradiction you have checked are different evidence classes, and a verdict rests only on the
second.

Then, and only then:

- read the rubric for the angle in question — [`rubrics/source-fidelity.md`](rubrics/source-fidelity.md),
  [`rubrics/statement-soundness.md`](rubrics/statement-soundness.md), or
  [`rubrics/metadata-hygiene.md`](rubrics/metadata-hygiene.md) — plus
  [`rubrics/_common.md`](rubrics/_common.md) for evidence and verdict rules, and
  [`references/definition-traps.md`](references/definition-traps.md);
- follow source cross-references, read revisions/addenda, or inspect history/overlapping PRs;
- use [`references/checking-in-lean.md`](references/checking-in-lean.md) for a scratch witness,
  `#print axioms`, or a type-checked suggestion;
- run a source construction as a **positive control** whenever a faithfulness claim or a
  status flip rests on the source's construction existing: instantiate it against the Lean
  predicate at a concrete value and report the check. "The source says so" verifies the
  source's claim, not the formalisation's fit — only the control verifies both at once. Run
  a negative control when it resolves the issue.

State exactly which deeper check ran. If it cannot be checked, make it a Question rather than a
Finding.

## PR output contract

Return a review that can be published directly to GitHub:

````markdown
## FC review

**Verdict:** CLEAN | ACCEPT WITH NITS | NEEDS REVISION
**Checks:** source read; Lean `<pass | blocked>`; definitions checked
<One sentence: scope and next action.>
````

After the summary, use `### Findings` and `### Questions` only when needed. Each finding has:

- exact `path:line`, a short title, and its angle in brackets — `[source-fidelity]`,
  `[statement-soundness]`, or `[metadata-hygiene]`;
- direct evidence or witness;
- what that evidence shows and does not show; and
- the smallest proposed change.

Use CLEAN only with no findings; ACCEPT WITH NITS only for non-semantic findings; otherwise use
NEEDS REVISION. Keep uncertainty out of the finding count.

**Cut before you return.** Ask of each finding whether a maintainer would change the file because
of it. If not, it belongs in the checks line or nowhere. A batch that filed fourteen findings
across five files had five worth acting on, and the four that mattered were harder to see for the
nine around them. Three things are not findings on their own: what `AGENTS.md` or
`CONTRIBUTING.md` explicitly permits, a missing docstring sentence, and a point another reviewer
has already made on the PR.

Two rules on evidence. The witness requirement covers the argument, not only the claim: counts,
ratios, and "the only file in the tree that does this" are load-bearing when you use them to argue
a finding matters, so run them or leave them out, because a wrong statistic discredits a correct
finding. And downgrading a discrepancy takes the same evidence as raising one, so quote the
convention that excuses it or report it.

Keep the constraints you were given, including the ones that cost evidence. When a constraint
blocks a check, report it as not established and say why.

For a high-confidence, localized replacement, also emit one GitHub-ready inline comment:

````markdown
<short explanation and witness>

```suggestion
<minimal replacement>
```
````

Emit a suggestion only when the exact original line is known, the replacement is self-contained,
and it type-checks or is plainly documentation-only. Do not suggest a repair that chooses between
unresolved source readings.

End a normal report with one evidence line: reviewer, exact commit, source link, and focused
build result. Keep full hashes, command logs, and external-control transcripts in an existing
artifact only for an escalation.

The review is advisory. Do not approve, request changes, merge, label, or mutate a contributor
branch. A maintainer decides.

## Out of scope

- style, naming, imports, and formatting, which CI and `AGENTS.md` cover;
- a shorter proof for a statement that already builds;
- an equivalent alternative formalisation with no observable difference; and
- whether an open conjecture is true.
