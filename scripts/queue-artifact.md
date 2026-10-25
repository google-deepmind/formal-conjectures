# Reusing the merge-queue website

A push to `main` always validates Lean and refreshes its shared build cache.
It also looks for a successful merge-queue run from the same repository and
workflow at the exact same commit. If its receipt and Pages archive match,
it uploads those same tar bytes instead of rebuilding the website.

```text
merge queue: script tests + full Lean/site build → Pages archive + receipt
                                                    ↓ exact match
main:        script tests + Lean validation + Lean cache refresh
               → reuse website OR render/build website → deploy
```

Reuse skips Verso rendering, HTML processing, plotting, fragment extraction,
and website assembly. Lean library/problem builds, utility tests, metadata
extraction, category checks, and Lean cache saves still run. A failed current
check blocks deployment even when the website artifact is valid.

The receipt binds the artifact ID and tar digest to the repository, source
commit, workflow, run attempt, runner image/version, base path, and full build
mode. The source commit binds the checked-in build recipes and dependency pins.
The entire source workflow must succeed, including its parallel script tests.
A receipt from an earlier rerun attempt cannot validate a later one.

Only `merge_group` runs targeting `main` can supply artifacts. PR artifacts,
website-only builds, other repositories, other workflows, different commits,
and failed or unfinished runs cannot qualify. Downloads copy only the named
archive member; they do not execute or extract the site contents. The tar digest
is checked before upload. Deployment waits for the current build and script tests.

No new repository setting, secret, or required check is needed. The build job
uses `actions: read` on its existing `GITHUB_TOKEN`. Artifacts expire after one
day. Missing, expired, ambiguous, mismatched, or unavailable artifacts result in
an ordinary website build. A manual full run on `main` always rebuilds the site,
which also permits refreshing its external contributor metadata.

## Dependency and qualification

Merge #5435 first. Its cache separation saves the Lean build before documentation
can change its traces. This PR keeps that save enabled on reuse hits and uses
the existing `site` switch to skip documentation cache restores and saves.
It does not copy #5435's implementation into this branch.

The documentation cache is not refreshed on reuse hits. Later queue builds may
therefore spend longer rebuilding documentation even though the shared Lean
cache stays current. Measure consecutive queue/main cycles after #5435, including
cache restores, rendering, artifact transfer, and total runtime, before adoption.
A single faster deployment is insufficient evidence of an overall improvement.

Run `python3 -m unittest discover -s scripts -p 'test_*.py'`. Tests cover artifact
provenance/integrity, old attempts, unavailable downloads, source reruns, and the
workflow conditions that preserve Lean work while skipping website work. Set
`FC_BUILD_WORKFLOW` to a combined workflow file to run the same condition tests
with #5435 applied.

Live acceptance still requires a successful queue run followed by a `main` push
at the same SHA. Confirm Lean validation and cache refresh run, site construction
is skipped, the archive is unchanged, and Pages deploys it. Check that a failed
current Lean build blocks deployment and that a push without a qualifying receipt
builds the site normally. A successful PR check cannot exercise the reuse path.

Reused sites preserve the queue's external metadata snapshot. If configurable
feeds or other environment inputs are added, include them in the receipt
comparison before allowing reuse.
