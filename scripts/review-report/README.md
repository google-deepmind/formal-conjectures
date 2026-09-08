# Local review-report pilot

Prepare pinned inputs, collect an advisory review and existing check evidence, and render
one local report. The tool runs Git reads only. It does not run Lean, a model, external
proof code, a network request or a GitHub write.

This is an experimental operational format, not an accepted FC interface or a replacement
for the older `formal-conjectures.pr-audit.v1` evidence prototype. That prototype's stricter
validation and independent-review claims are not implemented here. Its records may be retained
as evidence files, but this tool does not validate their internal schema or import their authority.

## Prepare a review

Use a checkout of the exact PR head and a trusted copy of the review skill, such as #4899.
Put the cited source excerpts and their URLs/retrieval notes in a dedicated source directory.
An empty directory is allowed when the source is unavailable; source review must then remain
incomplete. The tool records the committed head, actual merge base, changed paths, procedure
files and source bytes. Local uncommitted changes are not the review target. Skill `evals/`
directories are excluded from reviewer inputs.

```sh
python3 scripts/review_report.py prepare \
  --checkout /path/to/pr-checkout --repository google-deepmind/formal-conjectures \
  --base origin/main --skill /path/to/formal-conjectures-review \
  --sources /path/to/source-excerpts --require build --out /tmp/review-inputs
```

Add `--require proof` when a proof claim needs verification. Build is always required.
The repository locator is supplied by the operator; the tool does not authenticate GitHub
or establish that the local Git commits belong to that remote.

The output contains `request.json`, copied `procedure/` and `sources/` files, and a
`review-template.json`. Give the reviewer these inputs and the corresponding source checkout.
Store the completed template separately as `review.json`; do not edit the pinned request.

## Review input contract

The template has exactly these fields:

- `request_id`: copied from `request.json`; the reviewer cannot supply a verdict for another request.
- `reviewer`: human identity or actual model/version used. This is recorded, not authenticated.
- `context_policy`: `fresh` or `rereview`. A rereview must retain its prior review context.
- `prior_reviews`: evidence paths for prior reports and replies; empty for a fresh review.
- `coverage`: `source-fidelity`, `statement-soundness`, `metadata-hygiene`, each `complete` or `incomplete`.
- `findings`: objects with exactly `angle`, `file`, `line`, `severity`, `message`, `suggestion`, `evidence`.
- `questions`: unresolved material questions as strings. Optional non-material notes do not belong here.

The template also includes `reconciliations`, an optional additive v1 field for rereviews.
Each entry has exactly `prior_evidence`, `status` (`retained`, `corrected` or `withdrawn`),
`reason`, and nonempty supporting `evidence` paths. The prior reference must occur in
`prior_reviews`; use a separate retained record per prior finding. Each prior reference can
be reconciled once. A withdrawn finding is preserved in the report without becoming a current
finding or unresolved question. An unresolved dispute belongs in `questions`. Producers that
omit this field remain valid; the assembler does not infer a disposition for them.

A finding's angle is one of the three coverage keys. Its file must be in the recorded diff;
line is a nonnegative integer (`0` means file-wide). For deletions, cite the old file's line.
The tool validates scope membership but does not validate line numbers against source bytes.
Severity is `semantic` or `nit`. Message and suggestion must be nonempty. Evidence is a
nonempty list of retained paths, for example `sources/problem.txt` or `evidence/witness.txt`.
Documentary evidence and checked counterexamples remain different kinds of support; the reviewer
must explain which supports the finding. The assembler cannot judge that relationship.

## Supplied checks

Create an evidence directory containing `checks.json` and files under `evidence/`:

```json
{
  "request_id": "COPY_THE_REQUEST_ID",
  "artifacts": [
    {"path": "evidence/build.json", "sha256": "SHA256_OF_THE_EXACT_FILE_BYTES"}
  ],
  "checks": [
    {
      "kind": "build",
      "status": "pass",
      "producer": "the workflow/run or operator that produced this evidence",
      "policy": "lake --wfail build on the affected modules",
      "detail": "What ran and the scope it establishes",
      "evidence": ["evidence/build.json"]
    }
  ]
}
```

This is a shape example, not a build result. `kind` is `build` or `proof`; each occurs at most
once. `status` is `pass`, `fail`, `error` or `not_run`. Pass/fail requires retained evidence.
Missing required checks become `not_run`. An empty `artifacts` and `checks` array records that
no checks were supplied. The manifest can also retain witness outputs or earlier audit records
for findings to reference, without inventing a build or proof verdict for them.

For proof evidence, retain the exact statement/proof/bridge pins, dependency and verifier
versions, configured axiom policy, and the actual result in the referenced artifact. Name the
policy in the check. **Do not turn an arbitrary log into a passing receipt.** Producers must
establish the result through their documented verification path. This tool checks supplied
record shape, identity and file digests, not producer authenticity or proof correctness.
A nonzero Comparator exit without a documented classification is an error, not a parsed
mathematical rejection. No policy is inferred from log text or filenames.

## Assemble and check freshness

Run `prepare` again with the current checkout, trusted skill and source excerpts, writing
another directory. This captures changes since the original review. `--current` is required;
supplying an old snapshot again cannot establish current freshness.

```sh
python3 scripts/review_report.py assemble \
  --request /tmp/review-inputs --current /tmp/current-review-inputs \
  --review /tmp/review.json --evidence /tmp/review-evidence --out /tmp/review-result
```

The output directory must not exist. It contains:

- `report.json`: deterministic advisory result with the original request, supplied findings,
  normalized checks, artifact digests and assembler code hash.
- `observation.json`: original report digest, current request identity and freshness/completeness.
  Different current inputs change this observation, not the original result.
- `summary.md`: escaped human-readable view of both records, with local evidence links.
- Copied input records, original procedure/source files, and check evidence.

Confirmed semantic findings yield `NEEDS REVISION`, with any incomplete checks still listed.
Otherwise a missing/failed check, incomplete coverage or material question yields `INCOMPLETE`.
Only a complete review can yield `CLEAN` or `ACCEPT WITH NITS`. Staleness is a separate prominent
state: an old clean result does not become current merely because its original checks passed.
A failed build or rejected proof remains a check outcome, not an invented semantic finding.

Exit `0` means the report was assembled, including when incomplete or stale. Exit `2` means
invalid input or an I/O/Git failure. Neither exit code approves a PR. Strict readers should use
the versioned JSON fields, never scrape `summary.md` or treat CLI success as a review pass.

## Evaluation and next integration

Compare review variants only on matching head, merge base, source snapshots, tool access and
context policy. A fresh run and a rereview with prior findings are different evaluation inputs.
Keep historical runs separately. Count actual findings, unsupported claims, false positives,
contradictory suggestions and human effort; a report that parses is not a successful review.

The design adapts Tau Ceti's [case-file approach](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/casefile.py)
and [separation of operational state from archived runs](https://github.com/TauCetiProject/TauCetiData#design).
It handles procedure freshness explicitly, the missing behavior tracked in
[TauCetiReview #95](https://github.com/TauCetiProject/TauCetiReview/issues/95).
No upstream implementation is vendored. Isolated evidence execution, authenticated producer
adapters, model invocation, persistent PR state and publication remain follow-ups under FC #4394.

Run the offline checks with:

```sh
python3 -m unittest discover -s scripts -p 'test_review_report.py' -v
```
