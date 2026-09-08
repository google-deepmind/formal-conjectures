# Sol review pilot — 8 September 2026

All 24 reviews in the final structured-output batches passed the report assembler. Reassembling the retained inputs
reproduced all 24 JSON reports, freshness observations and Markdown summaries byte-for-byte.
The reviewer and separate, label-blinded grader both used `gpt-5.6-sol`, high reasoning,
through Codex CLI 0.149.0. No review comments or approvals were published.

| Batch | Skill reports / graded | Baseline reports / graded | Result |
| --- | --- | --- | --- |
| Original ten scenarios | 10 / 10 | 10 / 10 | Provisional labels disputed; no accuracy claim. |
| Supplemental Goldbach pair | 2 / 2 | 2 / 2 | Both arms returned CLEAN on the unchanged statement and one correct finding on the altered bound. |

The main batch produced 9 findings with the skill and 14 without it. The model grader marked
one finding unsupported/nonactionable in each arm. It marked all case criteria met in 5/10
runs in each arm, while disputing gold labels in three skill runs and four baseline runs.
These counts do not establish that either reviewer is more accurate: they include unresolved
source interpretations, one observation per case/arm, correlated scenarios and a same-family
model judge. The Erdős 940 boundary example is referenced in the skill, so this is calibration,
not a held-out generalization result. No cases or failed attempts were silently discarded.

The original “clean” Erdős 940 label needs adjudication. Both arms identify the difference
between infinitely many nonrepresentable integers and eventual representability. Whether
FC intends a related variant of the cited question is a maintainer judgement. A separate
post-run Lean audit verifies only the general logical distinction, not a counterexample
involving powerful numbers; it was not supplied to either arm or the graders.

There is also a grading limitation: a baseline Erdős 14 report files a uniformity concern
as a semantic finding while admitting the packet cannot resolve it. One model grader accepts
that as actionable without addressing whether it belongs only in Questions. Human assessment
must check that distinction rather than treating a model grade as authority.

The Goldbach pair was added after these disputes, frozen before its own model calls, and
reported separately. Its unchanged statement matches the scoped source. The altered version
includes 2; a retained Lean proof shows that two primes cannot sum to 2. That witness says
nothing about the conjecture for integers greater than 2.

## Outputs and reproduction

- [Canonical model reviews and individual grades](reviews.jsonl)
- [Counts, model metadata and exact reassembly hashes](summary.json)
- [Actual clean report](clean-report.md)
- [Actual boundary report](boundary-report.md)
- [Harness and run protocol](../../../../../../scripts/review-eval/README.md)

The sample Markdown files are display copies with repository-relative evidence links. The
original report bytes, raw CLI events, prompts, usage and input snapshots are retained in the
local run archive. Dollar cost and human review time are unavailable, not zero.

Earlier attempts remain separate: the installed CLI rejected Astra before inference; a 5.5
batch was interrupted when the user selected Sol; an initial Sol output used the packet file
name instead of the repository path and was rejected. The harness now supplies a native output
schema with the permitted repository paths and validates the result through the report assembler
(originally #5341, now included with the skill). No rejected
output was repaired or counted as a success.

Before routine publication: have a maintainer assess the anonymized reports, settle the
source/label disputes and the treatment of uncertain findings, then freeze a broader suite and
run paired repeats. The human label forms are pending. Source acquisition, new witness
construction and tool execution still require the separate tool-using integration pilot.
