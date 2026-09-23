# CLI agent audit — 10 September 2026

Development audit on macOS arm64, starting at integration commit `cf5098ef0`.
The installed editable CLI identified itself as `0.2.0rc3`. This is a local
qualification record, not a release acceptance or model-accuracy evaluation.

The [11 September RC3 qualification](rc3-final.md) records subsequent live proof,
publication, installation and website checks. This audit retains its original
scope and results.

## Findings and fixes

| Reproduction | Before | Fix |
| --- | --- | --- |
| `eval summarize DIR --json`, with an array or missing task in `fc-result.json` | Unhandled traceback, empty JSON stdout, exit 1 | Validate consumed fields; return structured `invalid_result`, exit 3 |
| Evaluation result with an invalid task or suite digest | Counted as a verified attempt | Reject malformed identities before counting; preserve legitimate pre-task infrastructure errors with a null digest |
| `verify` with a missing directory or a file | Misleading `untrusted_target`, exit 4 | Check the directory first; actionable `directory_missing`, exit 2 |

Regression tests cover these cases. No verification policy, target identity,
review/report schema, or public catalog shape changed.

## Exercised paths

| Path | Evidence |
| --- | --- |
| Help, version, doctor, find/show, variants, exact names, empty results, invalid arguments, family help, status, selectors, skill path and completion | 31 subprocess cases; machine output checked for valid JSON and matching exit status |
| Real contribution preparation | PR #4941, head `fadba095d4ad43b234d5ddb3c89a11da25eebbb9`, base `5a13d480c38611f1381ba345f5933e9c29544c08`; independent Docker build passed in approximately 37 seconds |
| Existing-agent handoff | Read frozen procedure, complete scoped file, diff and source passages; finished a local report with explicit prior topic exposure |
| Invalid and completed drafts | Unfinished draft rejected while pending; corrected report accepted; completed report could not be overwritten |
| Historical inspection | Already-merged PR correctly marked historical; finishing returns 4 for applicability, while reading the saved run/logs returns 0 |
| Public export | Dry-run succeeded and retained the public projection locally; no upload or PR comment |
| Distribution | Built wheel from sdist; installed into a fresh Python 3.11 environment; help, version, doctor, fork browsing and bundled skill installation worked from `/tmp`; uninstall removed the executable |
| Packaged resources | Both skills and native exporter resources included; evaluation answer-key directories excluded |
| Shell output | Redirected command tests used `NO_COLOR`; Bash and Zsh completion scripts passed syntax checks |
| Deterministic suite | 119 toolkit tests passed after fixes, including remote-control, publication and execution-boundary fixtures |

The mathematical smoke case was already discussed in development and was merged
before this audit. No actionable semantic finding was established in its changed
content. It cannot measure review accuracy or replace human pilot adjudication.

## Remaining qualification

This audit did not dispatch live Linux proof verification, run a solver through
Harbor, post through the designated publisher, or perform a Linux clean install.
Their deterministic tests passed; their live acceptance gates remain separate.
The poisoned-build regression was not rerun in this audit; execution code did not
change. No paid model calls, publication, or upstream activation occurred.

Default public browsing still depends on #5375 deploying upstream. This audit
selected the fork endpoint explicitly. Its native catalog had 5,264 declarations
at source revision `947d543c20efc871fd1b28f76c29e72ebca432c8`, not the latest
integration revision. `moduleDocstrings` appearing first reflects sorted JSON keys,
not another schema or missing statements.

Detailed operator artifacts remain in the checkout's gitignored
`.conjectures/qualification/cli-agent-audit-20260910/`. The local review run is
`20260910T164848Z-cc90c8599ea6`; its retained bundle includes the assessment notes.
Original failing probe outputs remain alongside the post-fix retest outputs.
