# Delivery consolidation — 10 September 2026

Seven deferred deliveries were combined into four active draft PRs. The roadmap is
[#4394](https://github.com/google-deepmind/formal-conjectures/issues/4394); toolkit
acceptance is #5376 and website handoff is #5377.

| Retained PR | Absorbed PR | Scope |
| --- | --- | --- |
| #5386 | #5356 | Contribution CLI and opt-in Actions preparation |
| #5387 | — | Exact proof workspaces and verification |
| #5388 | #5389 | Evidence publication and problem-page display |
| #4828 | #4749 | Status and proof-link metadata consumers |

The absorbed PRs remain closed as consolidated work. Active drafts remain open
while dependencies are pending. Upstream review still requires replaying only each
layer's changes after prerequisites merge; cumulative draft diffs are not ready
for review. #5375's branch was not changed by this consolidation.

## Checks

| Branch | Tested revision | Passed checks |
| --- | --- | --- |
| CLI + Actions | `60bebefc35df212f824f0841e1c3ce1a740ebb4e` | 67 toolkit; 88 script tests |
| Proof | `3f2016c72a00a9ea2b7f5762c17aaad694f47262` | 92 toolkit tests |
| Evidence + pages | `cb0b40843bf55a3dcb08cdd94b09f8a17cdabda6` | 89 toolkit tests; Node website suite |
| Metadata consumers | `a2f0b3a39c5d069f22a8f59567926f1c3ec18244` | 69 script tests |
| Experimental evaluation | `dae33440c6bb11830264da3a2e3aa8fdc31df565` | 97 toolkit tests |
| Integration | `63521c98588d576891389a0ed094c37fcbdb4a1e` | 119 toolkit; 121 script tests |

Branch consolidation exposed obsolete `catalog.json` URLs and `conjectures[]`
fixtures in the two metadata consumers. Both now use the native `conjectures.json`
and `problems[]` contract. The initial failures are retained in the local logs.
The first multi-check invocation also resolved the virtualenv Python symlink to
its base interpreter, omitting test dependencies; the corrected invocations use
the virtualenv executable. Successful reruns above are the qualification evidence.

Actions preparation has no model/publication job and remains opt-in. The old API
adapter was not imported into the core delivery; historical evaluation code remains
outside the installed runtime. The proof/evaluation fixes from the agent audit are
retained on integration and their owning branches.

These are deterministic/local checks, not new semantic accuracy measurements,
remote verifier qualification or publisher acceptance. The final live proof,
publisher, production catalog and reader-handoff gates remain open. No upstream
merge or automation activation occurred. All pushes preserved branch history.

Detailed logs remain in the operator checkout at
`.conjectures/qualification/consolidation-20260910/`. Original issue and PR bodies
were retained locally before editing; GitHub edit history also preserves them.
