# Review evaluation

This is a small, paired **evidence-packet pilot**, not an autonomous review bot or a
claim of independently established review quality. It tests interpretation of supplied
evidence and generation of reports through the assembler in FC #5341.

The current suite is `.agents/skills/formal-conjectures-review/evals/evals.json`.
It contains ten scenarios clustered on two real FC declarations at main
`d33e35a5f45386a173b31159ae6598b1968bc463`, using Lean 4.33.1. It includes candidate
clean controls, seeded source mismatches, unavailable evidence, a disproven proof claim,
stale proof status, and contested or contradictory prior findings. Conversation and stale
status records are explicitly simulated; Lean compilation and axiom inspection records
are actual local executions. A successful statement build is not a proof.

The Erdős 940 boundary example is also referenced by #4933 in the procedure. These are
regression/calibration scenarios, not held-out evidence of mathematical generalization.
`evals/supplemental.json` adds a separate Goldbach clean/boundary pair, with an actual
Lean proof that two primes cannot sum to 2. It was selected after the initial pilot
challenged the original clean labels, then frozen before its own model calls. Keep its
results separate; it does not replace the original cases or repair their scores.

The original eval file is preserved byte-for-byte under `evals/historical/`.
Its scores, selection rules and toolchain policy are historical. Do not use them as current
validation or follow their recommendation to retain only cases that separate the arms.

## Protocol

1. Freeze the suite, source bytes, candidate files, procedure, assembler and harness before
   running either arm. All scenarios stay in the denominator, including failed model calls,
   malformed reports, ties and disputed gold. Do not edit a frozen run to improve scores.
2. Give both arms identical packets, model, reasoning effort, output contract and tool access.
   Inject the procedure only into the skill arm. Never supply expected answers or prior
   evaluation outputs. Rereview context is supplied only in designated rereview scenarios.
3. Run fresh Codex processes in empty directories. Disable shell tools, web and subagents;
   ignore user configuration. Retain raw events and reject unexpected tool use. This harness
   is not a general isolation service for untrusted code. Installed global skill metadata
   may still be included by the CLI; record its version and compare arms in the same host.
4. Supply a native structured-output schema that constrains finding paths to the repository
   scope and evidence references to the retained packet. Then validate each model's exact
   JSON through the supplied report assembler. Do not extract
   verdicts or findings with regex, repair malformed outputs, or count CLI success as a pass.
5. Grade reports in a separate, fresh model invocation with randomized opaque run IDs.
   Withhold arm labels, reviewer identity, selected procedure, telemetry and other reports.
   Style can still reveal the arm; this is label blinding, not guaranteed perfect blinding.
6. Judge each finding for support, usefulness and duplication, and check for contradictory
   fixes. Extra findings are not automatically false positives. If evidence challenges the
   provisional gold key, record the dispute without changing the frozen score.

Gold criteria are author-written and provisional. A model judge is a separate assessment,
not independent human validation. Use the same model for both reviewer arms. A judge from
another model family and a maintainer reading anonymized reports are useful follow-ups.

## Run locally

The commands make no GitHub writes. `freeze` and `summarize` make no model calls.
`run` and `judge` use the authenticated Codex CLI and consume account usage. No model runs
are scheduled in CI. The assembler path must be a trusted checkout of #5341 or its successor;
this PR does not copy that implementation or require it for ordinary script tests.

```sh
python3 scripts/review_eval.py freeze \
  --suite .agents/skills/formal-conjectures-review/evals/evals.json \
  --skill .agents/skills/formal-conjectures-review \
  --assembler /path/to/report-checkout/scripts/review_report.py \
  --repeats 1 --out /tmp/fc-review-eval-run

python3 scripts/review_eval.py run --root /tmp/fc-review-eval-run \
  --assembler /path/to/report-checkout/scripts/review_report.py --model MODEL_ID
python3 scripts/review_eval.py judge --root /tmp/fc-review-eval-run --model JUDGE_MODEL_ID
python3 scripts/review_eval.py summarize --root /tmp/fc-review-eval-run
python3 scripts/review_eval.py human-packet --root /tmp/fc-review-eval-run \
  --out /tmp/fc-review-human-packet
```

The first run is one observation per scenario and arm, not an accuracy estimate. Use paired
repeats on a frozen suite before claiming a reliable skill/baseline difference. Broaden the
mathematical domains before generalizing beyond these two declarations.
Use `--suite .agents/skills/formal-conjectures-review/evals/supplemental.json` and a new
output directory to run the supplemental controls with the same protocol.

Runs retain the packet, procedure files, input hashes, original model output, CLI events,
usage when available, wall time, validated JSON/Markdown reports, and individual grading
rationales. Dollar cost is `null` when the provider does not report it. The harness never
estimates a dollar cost from tokens. Freeze a new directory for an intentional repeat;
resuming skips completed attempts, including failures, rather than retrying selected cases.

`summary.json` exposes per-arm counts and every case result. Missing/invalid judgements are
ungraded, never automatically successful. Do not call “all criteria met” mathematical accuracy.
The initial local artifact directory is not a durable public archive.

## Human assessment and remaining scope

Before routine publication, a maintainer should inspect anonymized reports with the source
and evidence, record which findings they would act on, missed defects, corrections to the
gold key, and minutes spent assessing/repairing each report. Keep those labels separate from
model grades. No human time or acceptance is inferred from successful report generation.
The `human-packet` command exports anonymous packets and a label form with decisions and
minutes left unset. It withholds model grades and arm labels. Sending it to a maintainer
is a separate action; the harness does not contact anyone.

This pilot does not measure source retrieval, construction of new Lean witnesses, execution
sandboxing, Comparator integration, GitHub publication or report persistence. Test those in
the later tool-using integration pilot; supplied evidence cannot validate tool-use behaviour.

Offline integrity checks run with the existing script CI:

```sh
python3 -m unittest discover -s scripts -p 'test_review_eval.py' -v
```
