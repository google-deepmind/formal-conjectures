# Common rules for every angle

Each file beside this one is one review angle: a mission, what to hunt for, and what is
not yours. The angles exist so that a finding names the kind of defect it is, so that
coverage is checkable per angle rather than per review, and so that the rubrics could be
judged independently — the shape `TauCetiProject/TauCetiReview` uses — without rewriting
them. `SKILL.md` gives the procedure that runs them.

The angles answer one question between them: does the Lean statement say what its cited
source says? A tool such as `leanprover/comparator` decides whether a submitted proof
establishes a given statement, under a permitted set of axioms. That question is
mechanical, and it is being automated. These angles are about the other question. No
checker settles it, because every checker takes the statement as given. Thus the automated
side gets better, and this side becomes more important.

## Findings carry witnesses

Each finding must carry a **witness**: a concrete case where the Lean and the source
disagree, so a reader can check the finding without redoing the review.

- "This looks too strong" is not a finding.
- "At `c = 2` and `n = 100` the hypothesis needs 20000 edges, and a simple graph has at
  most 4950" is a finding.

A witness that decides a verdict is **checked, not only argued**: run it in Lean or by
computation (`../references/checking-in-lean.md`) before filing the finding. An argument
grounded in a statement the file already proves still needs the connecting step machine-checked
when that step is what makes the finding blocking.

The witness requirement covers the argument, not only the claim: counts, ratios, and "the
only file in the tree that does this" are load-bearing when used to argue a finding
matters, so run them or leave them out. Downgrading a discrepancy takes the same evidence
as raising one: quote the convention that excuses it, or report it.

Examples in the rubrics are marked **confirmed** or **lead**. A confirmed example has a
witness that somebody checked; a lead is a place to look. Do not report a lead as a
finding, do not go hunting for a confirmed example in the current tree and conclude the
entry is wrong when it has been fixed, and do not re-report a defect whose fix is already
open — the pull request is named where there is one.

## Verdict semantics

- **CLEAN**: no findings from any angle.
- **ACCEPT WITH NITS**: findings that do not change the meaning of any statement.
- **NEEDS REVISION**: at least one finding changes a meaning, makes a statement vacuous,
  or shows a `formal_proof` claims more than the linked proof gives.

The verdict is advice about the statement, not a decision about the merge and not a
judgement about the contributor. If you cannot give a witness, write the item as a
question, not a finding — #4896 is the model: it marks its contents as leads.

## Out of scope for every angle

Style, naming and format (the linters and `AGENTS.md` own them); a shorter proof for a
statement that builds; an equivalent alternative formalisation with no observable
difference; whether the conjecture is true; whether to merge.

## Prior art

These angles cite, without copying (no licence; the CLA applies):
[`FABLE_REVIEW.md`](https://github.com/ryantuck/erdos-ai/blob/master/FABLE_REVIEW.md) and
[`ryantuck/formal-conjectures#1`](https://github.com/ryantuck/formal-conjectures/pull/1);
the verdicts suggested in #4876; and the audit in #4896, the source of several leads.
