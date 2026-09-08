# Review evaluation

Measure whether the skill improves mathematical review. Valid JSON is a tooling check,
not an accuracy score. This suite follows the [Agent Skills evaluation guide](https://agentskills.io/skill-creation/evaluating-skills),
[best practices](https://agentskills.io/skill-creation/best-practices),
[description testing](https://agentskills.io/skill-creation/optimizing-descriptions) and
[specification](https://agentskills.io/specification).

## Three separate questions

| Track | What it measures |
| --- | --- |
| Offline tests | Report shape, evidence integrity, scope and freshness; no model calls |
| Tool-using review | Supported defects, missed defects, false alarms, repairs and appropriate uncertainty |
| Description routing | Whether a relevant task causes the skill to be loaded; not review correctness |

## Cases and reference judgements

The skill's `evals/benchmark.json` contains 24 cases across 12 problem families:

- Eight actual FC corrections, each with its historical file and corrected counterpart (16 cases).
- Four additional candidate clean controls in algebra, combinatorics and number theory.
- Two source-unavailable workflow cases and two authored rereview scenarios.

Historical corrections cover domains, repeated summands, an unused parameter, a geometric
construction, Fourier coefficients/tails, difference cardinality and OEIS definitions/indexing.
Each case retains exact source-file provenance and source-document hashes. Historical files
are replayed in the pinned current environment; this is not a claim that their original
checkouts used that toolchain. Rereview conversations are explicitly authored scenarios.

**All reference keys are provisional.** A merged correction supports a defect label but does
not prove that the corrected file is otherwise clean. The initial development cases are R01
(integer domain), R17 (modern Jacobson statement) and R22 (source unavailable).
Keep before/after and workflow variants in the same family and split. Qualification cases
cannot run until their keys have a named human reviewer and supporting evidence. Do not mark
an author/model judgement as human adjudication. Public historical cases may be known from
model training; “qualification” means withheld from this iteration, not guaranteed novel.

Keep easy clean controls and ties. Do not select cases because the skill wins. Inspect three
initial development cases, improve the protocol using their transcripts, then expand. If a
case changes, freeze a new iteration and retain the earlier inputs/results. Do not tune the
skill using qualification outcomes and continue calling those cases held out.

## Reviewer environment

`review_eval.py` runs fresh Codex processes with only an explicitly configured workspace MCP
server. The server uses the official Python MCP SDK; it does not implement its own protocol.
The model can read/search sources and definitions, write scratch witnesses, and invoke Lean.
It cannot see suite keys, subsequent corrections, other runs or caller credentials.

Each run gets a separate Docker container with networking disabled, a non-root user,
resource limits and dropped capabilities. Only the original candidate, source documents,
optional prior context and an output directory are mounted. Only the skill arm receives
`SKILL.md` and its supporting files; those files are read on demand, never concatenated into
the initial prompt. The baseline receives the same ordinary FC contribution guidance and
JSON interface, without the skill's review strategy. The report records an explicit baseline
procedure receipt; that receipt is not supplied to the baseline model. Installed host skills are disabled for
the invocation, plugin discovery is disabled and client state is isolated. The operator's global
configuration is not edited. Built-in resource discovery is accepted only when its catalog is empty.

The image retains Lean/Mathlib and FC shared definitions, but removes FC problem sources,
problem build artifacts, FC history and its skills. Each candidate has a deterministic local
Git snapshot, explicitly distinct from its upstream source commit. `build()` runs the focused
`lake --wfail build`; its exit status is a build result. Arbitrary shell/witness output remains
raw evidence and is never parsed into a proof verdict. The original candidate is read-only.

This is an **offline tool-using benchmark**: source documents are available on demand, but
live web discovery and external proof execution are not measured. Model authentication stays
on the host. Only the isolated workspace tools are approved for unattended evaluation.
The Docker image and MCP server are trusted tooling, not contributor-supplied code.

## Run

Requires Docker, the Codex CLI and Python 3.11+. Install optional runtime dependencies into a
virtual environment with `pip install -r scripts/review-eval/requirements.txt`. Ordinary CI
script tests do not require Docker, the SDK, credentials or model usage.

```sh
docker build -t fc-review-eval:lean4.33.1 -f scripts/review-eval/Dockerfile .

python scripts/review_eval.py freeze \
  --suite .agents/skills/formal-conjectures-review/evals/benchmark.json \
  --skill .agents/skills/formal-conjectures-review \
  --image fc-review-eval:lean4.33.1 --cases R01 R17 R22 \
  --repeats 1 --timeout 420 --max-calls 30 --out ../review-eval/iteration-1

python ../review-eval/iteration-1/tooling/review_eval.py run \
  --root ../review-eval/iteration-1 --model gpt-5.6-sol --workers 2
python ../review-eval/iteration-1/tooling/review_eval.py assess \
  --root ../review-eval/iteration-1 --model gpt-5.6-sol
python ../review-eval/iteration-1/tooling/review_eval.py summarize --root ../review-eval/iteration-1
python ../review-eval/iteration-1/tooling/review_eval.py human-packet \
  --root ../review-eval/iteration-1 --out ../review-eval/iteration-1-human
```

`freeze` records the image identity, suite, selected cases, budgets, procedure and exact tooling.
Use the copied tooling to resume/reproduce a frozen run after editing the repository. Existing
attempts are never overwritten or silently retried. Failed and unstarted jobs remain visible.
For repeated comparisons, use the same model/settings and three runs per case and condition.
Repetitions do not increase the number of independent mathematical problems.

Each run retains the prompt, raw response, model events, tool commands/results, scratch outputs,
usage, wall time and assembled JSON/Markdown bundle. Preserve the entire iteration outside the
source checkout; do not commit authentication state. For temporary output inside the checkout,
use the ignored `review-artifacts/` directory. Generated `evals/results/` is also ignored.
Benchmark inputs and reference keys remain tracked. Publication is a separate workflow.

## Assessment

A separate model call receives the anonymous review, source dossier and execution transcript.
It matches reference defects, assesses every finding for support/actionability, and marks
repairs valid, invalid, untested or absent. Alternative valid findings and repairs are allowed.
Tool traces can reveal the procedure, so this is label blinding, not guaranteed arm blinding.

`summary.json` reports raw per-condition counts and per-run assessments. Disputed or insufficient
keys are counted separately; they are not reviewer failures. It reports defect detection,
unsupported/unresolved findings, clean-case false alarms, duplicates, repair validity, uncertainty,
time and tokens. There is no blended “all assertions passed” accuracy number. Model grades
remain provisional, including when a different model family is used as assessor.

Have a mathematician assess the anonymous packets, record missed defects, false alarms and
minutes spent, and adjudicate the reference key before qualification. Human forms start blank;
no human score or time is inferred. Inspect evidence and transcripts alongside aggregate counts.
Mechanical checks never substitute for source fidelity or mathematical correctness.

To adjudicate all 24 reference cases before running qualification, export their candidates and
sources without the provisional labels or later fix provenance:

```sh
python scripts/review_eval.py key-packet \
  --suite .agents/skills/formal-conjectures-review/evals/benchmark.json \
  --out ../review-eval/key-adjudication
```

The mathematician fills `adjudication.json`. Reconcile disagreements with the catalog, then
record the named reviewer and supporting evidence in each key. This step is manual; neither
packet export nor a model assessment promotes a key to `human_adjudicated`.

## Description routing

`evals/triggers.json` has 20 realistic queries: ten positives and ten nearby negatives, split
12 development / 8 validation with both classes represented. The separate command tests a
controlled catalog containing the description and observes an actual MCP `load_skill` call:

```sh
python scripts/review-eval/trigger_eval.py run \
  --queries .agents/skills/formal-conjectures-review/evals/triggers.json \
  --skill .agents/skills/formal-conjectures-review/SKILL.md \
  --split development --repeats 3 --out ../review-eval/description-1
```

The runner retains exact tooling copies, query bytes, the skill and raw invocations.
Run validation after freezing the description; do not use its failures for tuning and keep
calling it held out. Report per-query loading rates and failed invocations, separately from
review scores. This controlled selector tests description routing, not native desktop skill
discovery. A native-client trigger check remains a distinct integration test.

## Historical records

The superseded packet-only cases, selected outputs and their exact tooling remain in
[Git history](https://github.com/williamjblair/formal-conjectures/tree/ba5930b643b2ab1f85036ec2c3c6ff5a82f75aeb/.agents/skills/formal-conjectures-review/evals)
and the operator's run archive. They are excluded from the current source tree. Their 24 valid
reports establish format/replay behavior only and are not pooled with this benchmark.
Do not run old manifests with the v2 CLI.
