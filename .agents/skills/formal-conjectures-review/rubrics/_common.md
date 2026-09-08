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

## Findings carry evidence

Each finding must carry evidence a reader can check without redoing the review:

- For a direct source or metadata discrepancy, cite the exact source passage and Lean
  declaration or attribute, and explain the differing requirement. If the source is
  ambiguous, ask a question instead.
- For a counterexample, contradiction or computation, provide a checked **witness**.
  Documentary evidence alone does not establish the mathematical inference.

- "This looks too strong" is not a finding.
- "At `c = 2` and `n = 100` the hypothesis needs 20000 edges, and a simple graph has at
  most 4950" is a finding.

A mathematical witness is **checked, not only argued**: run it in Lean or by computation
(`../references/checking-in-lean.md`) before filing the finding. An argument grounded in
a statement the file already proves still needs the connecting step machine-checked
when that step supports the finding. State whether the check ran in Lean or externally.
A direct, unambiguous source mismatch does not require an artificial contradiction proof.

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

- **NEEDS REVISION**: at least one finding changes a meaning, makes a statement vacuous,
  or shows a `formal_proof` claims more than the linked proof gives.
- **INCOMPLETE**: no established defect requiring revision, but a required check is blocked
  or a material semantic question needs human review.
- **ACCEPT WITH NITS**: required checks complete, no material questions, and only findings
  that do not change the meaning of any statement.
- **CLEAN**: required checks complete, no findings and no material questions.

Apply these in order. A confirmed defect still requires revision when another check is
blocked; report both the defect and the coverage gap. An inaccessible source, failed build
or missing proof verification is not a clean review and is not itself proof of a semantic defect.

The verdict is advice about the statement, not a decision about the merge and not a
judgement about the contributor. If the evidence required for a claim is missing, write
it as a question, not a finding — #4896 is the model: it marks its contents as leads.

## Out of scope for every angle

Style, naming and format (the linters and `AGENTS.md` own them); a shorter proof for a
statement that builds; an equivalent alternative formalisation with no observable
difference; whether the conjecture is true; whether to merge.

## Prior art

These angles cite, without copying (no licence; the CLA applies):
[`FABLE_REVIEW.md`](https://github.com/ryantuck/erdos-ai/blob/master/FABLE_REVIEW.md) and
[`ryantuck/formal-conjectures#1`](https://github.com/ryantuck/formal-conjectures/pull/1);
the verdicts suggested in #4876; and the audit in #4896, the source of several leads.
