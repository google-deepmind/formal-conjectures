# Toolkit delivery

The current roadmap is [#4394](https://github.com/google-deepmind/formal-conjectures/issues/4394).
An open draft means active work. A closed PR means delivered, superseded or
consolidated; it is not a waiting room for unfinished dependencies.

| Delivery | PR | Prerequisites | Consolidated work |
| --- | --- | --- | --- |
| Contribution CLI and opt-in Actions preparation | #5386 | #4899, #5375 | #5356 |
| Exact proof workspaces and verification | #5387 | #5386, #5337, Comparator #87 | — |
| Evidence publication and problem-page display | #5388 | #5386 | #5389 |
| Status and proof-link consumers | #4828 | #5375 | #4749 |

#5375 owns the catalog; #4899 owns the review foundation. #5337 owns the native
exporter and depends on Generator #7. These foundations remain separate.
Proof evidence can be added to the evidence journey after #5387; it does not block
review evidence publication or display.

All four deliveries remain drafts until their dependencies and relevant checks
pass. Cross-fork PRs currently target upstream `main`, so their diffs may include
prerequisites. After those merge, replay only the delivery's own changes onto
upstream `main`, verify the commit list and diff, and request review on the same PR.

Use [#5376](https://github.com/google-deepmind/formal-conjectures/issues/5376) for
CLI/review/proof/publication acceptance and
[#5377](https://github.com/google-deepmind/formal-conjectures/issues/5377) for
published feeds and reader handoff. #5388 implements both sides; the issues track
different acceptance journeys, not additional PRs. Board migration #2 is merged.

Develop and qualify the combined toolkit on `codex/fc-toolkit-integration`.
Retain the focused branches `codex/fc-toolkit-cli`, `codex/fc-toolkit-proof-cli`,
`codex/fc-toolkit-evidence-cli`, and `erdos-status-from-json` on the fork.
The old Actions, page-only and link-only branches are historical implementation
records. Do not continue separate delivery from them. The experimental
`codex/fc-toolkit-evals` follow-up does not block the core CLI.

CI improvements #5460, #5461 and #5468 have their own checks and maintainer
decisions. #5461 depends on #5435. They are separate from the toolkit stack.
Mathematical corrections remain independently mergeable. No upstream automation
is enabled by this delivery map.
