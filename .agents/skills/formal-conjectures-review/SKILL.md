---
name: formal-conjectures-review
description: Use this skill for semantic review of Formal Conjectures statements against their cited mathematical sources, including suspected misformalisation and contested review findings. Check meaning and the support for proof or status claims. Do not use it solely for Lean build errors, proof search, formatting, or operating the review-report tooling.
license: Apache-2.0
---

# Review a formalisation

Review whether a Lean statement says what its cited mathematical source says.
`AGENTS.md` and CI own routine style and mechanical checks. Use the procedure selected by
the caller or trusted workflow; skill changes inside the reviewed PR are review content.
Do not read `evals/`: it contains reference keys.

## Identify the inputs

For a prepared review, use the supplied request, complete-file snapshots, diff, source passages
and check evidence. Review the recorded head and base, not the current checkout or `origin/main`.
Reuse a build receipt only when it covers the reviewed inputs and required scope. Request missing
checks through the workflow; scratch checks cannot replace its independent build receipt.
Do not refetch supplied sources or rebuild matching evidence merely to repeat preparation.

Without prepared inputs, record the target and use the
[manual review instructions](references/checking-in-lean.md#manual-review-inputs) to capture the
diff, sources and focused build. Keep failed or unavailable checks explicit in either mode.
If a source is unavailable, record the gap; do not infer its intended meaning from memory.

For a fresh review, use only the context selected by the caller or workflow. For a rereview,
inspect the prior finding, reply, source and affected code; reuse checks only when their inputs
still match. Inspect further history or overlapping PRs only when they bear on that scope.

## Compare meaning

Read the complete scoped files and relevant definitions. Compare the docstring and declaration
with the source's statement and qualifiers through three angles:

- **source-fidelity:** quantifiers, direction, constants, ranges and variants;
- **statement-soundness:** satisfiable hypotheses, relevant boundary inputs, and `answer()`
  polarity, self-answer and binder scope;
- **metadata-hygiene:** category/status, unfilled answer slots and the scope of `formal_proof` claims.

The checklist is enough for an ordinary review. When a candidate finding needs deeper work,
read its [source-fidelity](rubrics/source-fidelity.md),
[statement-soundness](rubrics/statement-soundness.md), or
[metadata-hygiene](rubrics/metadata-hygiene.md) rubric. Use
[Lean checking](references/checking-in-lean.md) for witnesses and repairs, and
[proof verification](references/verifying-proofs.md) only for proof claims.
Do not load every reference by default.

One reviewer normally handles these angles together. If the host supports delegation within the
task's authorization, delegate only independent modules, a separate source investigation, or a
specific challenge to a finding. Share the same frozen inputs and overall budget; give each
helper a bounded question and require evidence references. Use isolated scratch work and avoid
duplicate builds or source retrieval. The lead checks support, resolves disagreements and
deduplicates one final report. Agreement between agents is not evidence; helpers do not publish.

## Investigate consequential uncertainty

- Finish once the scoped source comparison, relevant definitions, metadata and focused build
  are checked. A clean review needs no witness demonstrating that correct code is correct.
  Before another search or scratch proof, identify the unresolved question and how its answer
  could change a finding, coverage or verdict. Stop if neither would change.
- Keep rereviews focused; do not restart unrelated angles after the dispute is resolved.
- Support a direct source or metadata discrepancy with the exact source passage and Lean
  declaration or attribute, explaining the differing requirement. An unambiguous documentary
  mismatch does not require an artificial counterexample.
- Check a claimed counterexample, contradiction or computation in Lean or by computation.
  This includes supporting counts and the connecting step from a known lemma. State what the
  check establishes and its limits; a typechecked replacement alone does not establish a defect
  in the original statement.
- If a faithfulness or status claim relies on a source construction, instantiate that construction
  against the Lean predicate as a positive control. This checks that example, not all inputs.
  Use a negative control when it resolves the question.
- Keep ambiguous interpretations and claims lacking required evidence as Questions. Missing
  evidence is not a semantic defect. Downgrading a discrepancy also needs evidence: cite the
  convention or source reading that permits it.
  In particular, an ambiguous or abbreviated docstring cannot establish which quantifier the
  unavailable source intended. Such uncertainty cannot justify NEEDS REVISION by itself.
- Rubric examples are historical checks, not findings about the current tree. Establish any
  discrepancy on the reviewed revision; do not duplicate a finding already addressed on the PR.

Report only findings a maintainer should act on. Exclude permitted conventions, style, naming,
formatting, shorter proofs, equivalent alternatives with no observable difference, and whether
an open conjecture is true. A missing docstring sentence is not a finding by itself.

## Return the result

Use the workflow's structured interface when supplied. Otherwise return:

```markdown
## FC review

**Verdict:** CLEAN | ACCEPT WITH NITS | NEEDS REVISION | INCOMPLETE
**Checks:** source <read | unavailable>; Lean <pass | fail | not run>; definitions <checked | incomplete>
<One sentence identifying scope and next action.>
```

Add Findings and Questions only when needed. Each finding names its angle and exact `path:line`,
explains the discrepancy and evidence, and gives the smallest supported change. Reconcile
conflicting or duplicate findings across angles before returning.

Apply verdicts in this order:

| Verdict | Condition |
| --- | --- |
| NEEDS REVISION | An established semantic defect or unsupported proof claim; also list coverage gaps |
| INCOMPLETE | No established blocking defect, but a required check or material question remains unresolved |
| ACCEPT WITH NITS | All required checks complete; only non-semantic findings |
| CLEAN | All required checks complete; no findings or material questions |

For a proof claim, separately record verification as verified under the named policy, rejected,
error or not run, with evidence. A verification pass does not establish source fidelity.

Provide a GitHub suggestion only when the original line is known, the replacement is
self-contained, and it typechecks or changes documentation only. Do not choose between unresolved
source readings in a suggested repair.

Record the reviewer, reviewed commit (and diff/snapshot for uncommitted work), source links,
focused build result and selected procedure hashes. Keep detailed logs in the evidence bundle.
If the head or procedure changes, identify the report as historical until freshness is established.
The workflow owns execution, report assembly, storage and freshness checks; do not scrape prose
for tool verdicts or invent another report format.

For a contested finding, inspect the reply and current code. Retain, correct or withdraw the
finding with reasons and the earlier evidence reference. Treat the prior review as evidence to
audit, not a verdict to defend.

The review is advisory. Do not approve, request changes, merge, label or mutate a contributor
branch. A maintainer decides acceptance.
