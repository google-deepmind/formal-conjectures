# Agent workflow implementation and qualification

Recorded 10 September 2026. This is development work, not a new published release
or upstream acceptance. No model was launched and no paid API call was made.

For later release checks and current acceptance gates, see the
[11 September RC3 qualification](rc3-final.md). The results below retain their
original revisions and limitations.

| Scope | Delivery |
| --- | --- |
| Skill discovery and explicit installation | `codex/fc-toolkit-cli`, existing deferred #5386 |
| Standalone workspaces and local Linux controller | `codex/fc-toolkit-proof-cli`, existing deferred #5387 |
| Frozen suites and Harbor export/grading | `codex/fc-toolkit-evals`, follow-up to the proof branch |
| Combined testing | `codex/fc-toolkit-integration` |

## Recorded checks

- Integration: 100 deterministic toolkit tests passed, including atomic evaluation
  export, external target binding, symlink rejection, configuration preservation,
  missing verifier results and non-scored infrastructure failures.
- Focused branches: 51 core tests, 75 proof tests, and 79 evaluation-branch tests passed.
- Clean wheel/source-distribution packaging passed on macOS and Linux at
  `74299491840e73ba9f070a11384cefeb9425ec08`:
  [package qualification](https://github.com/williamjblair/formal-conjectures/actions/runs/34487976713).
  The installed wheel exposed skill discovery/installation outside a checkout,
  without AI credentials or an installed model adapter.
- Harbor's actual `TaskConfig` accepted the generated task at upstream revision
  `191d1b989bbba1d77c2db23e17aec308d7c08046` (version 0.22.0). This validates the task
  contract, not an end-to-end agent trial or a verifier image.
- The added AF_UNIX filter denied Unix sockets and socket pairs in a native ARM
  Linux container, also denying a child's socket creation while retaining AF_INET.
  This was a functional probe with an installed distribution libseccomp, not a
  pinned production-image qualification. An x86-emulated container could not load
  the filter and correctly returned an execution error.

- A real Harbor no-op trial transferred the submission and retained an infrastructure
  error with no reward when trusted toolkit/tools were deliberately absent. See
  [the receipt](harbor-missing-tools.json). This checks actual artifact/error handling
  through the harness without invoking a model; it is not successful proof grading.

- Native Linux also passed all seven agent-workspace tests, including a concurrent
  symlink swap during capture. In a container without Git, Lean, network access or
  AI credentials, `doctor` and `show` passed against an explicit statement fixture.
  This does not substitute for production catalog deployment.
- Subsequent implementation adds bounded descriptor-relative submission reads and
  keeps pending definition assessment visible in workspace status. These changes
  have deterministic coverage; the real proof run below retains its own exact pin.

## Linux proof qualification

[34488055221](https://github.com/williamjblair/formal-conjectures/actions/runs/34488055221)
at `0881caf46` exposed a missing source-cache acquisition step: fresh export timed out
before Comparator. The result correctly remained an infrastructure error with policy
unevaluated. The original failed result is preserved.

The controller now populates the exact source's pinned dependencies before export and
retains acquisition logs. A regression checks that acquisition failure cannot reach
export or import submitted code. The corrected controls passed in 36m 55s at
[`74628f9febe204e87f5387338b240124e8b7fd4e`](https://github.com/williamjblair/formal-conjectures/actions/runs/34490305986).
It covers standalone initialization, unfinished proofs, imported assumptions, a valid
proof and a changed executor. Both negative proof cases reached Comparator's
`axiom_policy` stage and returned `disallowed_axiom`; the valid proof passed with
both kernels enabled. The changed executor remained an unevaluated infrastructure
error. The AF_UNIX probe also passed. The [retained receipt](agent-linux-74628f9.json)
contains the exact results, source/controller commits and tool hashes.

| Operation | Recorded duration |
| --- | ---: |
| Initialize exact workspace | 4m 28s |
| Reject unfinished proof | 9m 53s |
| Reject imported assumption | 9m 38s |
| Accept valid proof | 8m 51s |
| Reject changed executor | Under 1s |

Later changes add bounded submission capture, explicit per-case progress and removal
of rebuildable dependency directories while retaining inputs/results/logs. These have
deterministic coverage; the real controls above qualify their recorded revision.
The latest clean macOS/Linux package check passed at `6a21960b2` in
[34492315569](https://github.com/williamjblair/formal-conjectures/actions/runs/34492315569).

## Harbor end-to-end qualification

Recorded 16 September 2026. [35156959562](https://github.com/williamjblair/formal-conjectures/actions/runs/35156959562)
at `8c3f82545f51a58d4fa9241e0cc72af61e93eed0` built the shipped solver and verifier
recipes, pushed them to a registry inside the job and used their digests in a frozen
suite. Harbor `191d1b98` ran four trials with separate verifier environments. Harbor's
`nop` and `oracle` agents supplied the submissions; no model was called.

The unfinished and imported-assumption trials were rejected at `axiom_policy` with
reward 0. The valid proof was verified with reward 1. The filled answer hole passed
formal checks and was retained as `assessment_required` with no reward. The
[receipt](harbor-e2e-8c3f825.json) records image digests, the export manifest digest
and every trial.

Three earlier runs failed and were corrected. The first surfaced a toolchain lookup in
the verifier recipe and the second a missing fixture path in the workflow. The third
reached real grading, where the added filter also blocked `socketpair()`. Git's HTTPS resolver needs that call, so all four attempts were
retained as unscored infrastructure errors. The filter now matches the systemd
executor and blocks `socket()` only.

## Remaining acceptance

The Harbor adapter's recorded acceptance check has passed. A model-backed evaluation
still needs its own retained trial manifest and registry-published images. Retain
failures and missing rewards in any reported result.

Current delivery: #5386 and #5387 are active drafts. #5386 includes Actions
preparation and depends on #4899/#5375; #5387 also requires #5337 and Comparator #87.
After prerequisites merge, replay only the child changes onto upstream main before
requesting review. The evaluation follow-up does not block the core CLI. See #4394.
