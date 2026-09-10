# Reusing merge-queue validation

A push to `main` first looks for a successful merge-queue run from the same
repository and workflow at the exact same commit. If its receipt and Pages
archive match, the build job uploads those same tar bytes into the current run.
The existing deployment job consumes the current run's artifact as usual.

```text
merge queue: script tests + full Lean/site build → Pages archive + receipt
                                                    ↓ exact match
main:        script tests + validate receipt → upload archive → deploy
                              ↓ no match
                         ordinary full build → deploy
```

The receipt binds the artifact ID and tar digest to the repository, source
commit, workflow, run attempt, runner image/version, base path, and full build
mode. The source commit binds the checked-in build recipes and dependency pins.
The entire source workflow must succeed, including its parallel script tests.
A receipt from an earlier rerun attempt cannot validate a later one.

Only `merge_group` runs targeting `main` can supply artifacts. PR artifacts,
website-only builds, other repositories, other workflows, different commits,
and failed or unfinished runs cannot qualify. Downloads copy only the named
archive member; they do not execute or extract the site contents. The tar digest
is checked before upload. Deployment also waits for the current script tests.

No new repository setting, secret, or required check is needed. The build job
uses `actions: read` on its existing `GITHUB_TOKEN`. Artifacts expire after one
day. Missing, expired, ambiguous, mismatched, or unavailable artifacts result in
an ordinary build. A manual full run on `main` always rebuilds, which also permits
refreshing external contributor metadata used by the site.

Reused builds preserve the validated snapshot, including external metadata;
they do not refresh that data or write a new Lean cache. Cache separation in
#5435 remains independent. If configurable site feeds or other environment
inputs are added, include them in the receipt comparison before allowing reuse.

## Qualification before adoption

Local tests cover promotion, wrong source runs, changed inputs, expired/missing
artifacts, old attempts, download failures, digest mismatches, and a source rerun
during download. Run `python3 -m unittest discover -s scripts -p 'test_*.py'`.

Live acceptance still requires a successful queue run followed by a `main` push
at the same SHA: confirm compilation is skipped, the archive is unchanged, the
source run is linked in the summary, and Pages deploys it. Also confirm a push
without a qualifying receipt builds normally. Do not infer this acceptance from
mocked API tests or from a successful PR check, which cannot take the reuse path.
