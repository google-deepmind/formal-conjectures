# Toolkit 0.2.0rc2 qualification

This is a fork release candidate. It is not a complete release or an upstream
acceptance claim. The reproducible tests run under the Toolkit package qualification
workflow on Linux and macOS. Release assets are built from the tagged source
archive and include checksums.

RC2 adds persistent cancellation-request status, exact workspace handoff commands,
and the installation/qualification documentation corrections. The configured
Linux executor remains independently pinned; a client update does not change it.

## Exercised locally

- Human output and JSON, help, run selectors, actual logs, setup validation, bounded
  waiting, interruption, and historical-record exit semantics.
- Wheel built from the source distribution, installed outside a checkout without
  model dependencies; bundled skill and trusted resources present.
- Live catalog browsing and PR #4941 preparation with retained source passages and
  an independent passing Docker/Lean build.
- PR #4941 source comparison in the implementation session. No actionable findings;
  this is a provisional operator review, not a blinded accuracy evaluation.
- Selected review archived and advisory summary posted on
  [PR #4941](https://github.com/google-deepmind/formal-conjectures/pull/4941#issuecomment-5604286224); full sources and local execution files remain local.
- macOS initialization produced an exact public fixture workspace. The valid proof
  passed both configured kernels on [Linux run 34371044609](https://github.com/williamjblair/formal-conjectures/actions/runs/34371044609),
  using executor `e1c3e16c31ee5bc8f60c744e4b675a67c7fd20bd`. The CLI retrieved and
  checked its exact request and executor bindings.
- The unfinished fixture was [rejected for `disallowed_axiom`](https://github.com/williamjblair/formal-conjectures/actions/runs/34371466968).
  `run wait` returned 1 from the structured result; it did not infer rejection from log text.
- Fresh production-image setup passed after correcting cache ownership. Its digest is
  `sha256:d026928de86fbcf96af257e38d818d8ee613a810af847317aa8605ae2b180dfc`.
- Published RC wheel commands passed: isolated trial, install, live browsing, upgrade,
  and uninstall. [Linux/macOS package CI](https://github.com/williamjblair/formal-conjectures/actions/runs/34372604154) passed.
- Real poisoned-build isolation: invalid candidate rejected after scratch Lake
  tampering; valid candidate builds twice.
- Disposable Git archive tests for idempotency, failed upload, stale target, and
  older advisory requests. Completed local reports survive publication failure.

## Release gates still tracked

- Complete the macOS-to-Linux proof journey on the final executor revision,
  including valid/invalid proofs, infrastructure errors, and sandbox controls.
- Exercise concurrent advisory posting across separate controllers; GitHub comment
  updates do not provide a transaction covering freshness reads and writes.
- Finish the five-case semantic pilot with human adjudication. Operational success
  is not mathematical review accuracy.
- Finish published-index/site ingestion and the independent reader handoff.

The CLI labels proof/publication experimental while these gates remain. The
canonical delivery and acceptance tracker is FC #4394, with #5376 and #5377.

## Catalog delivery dependency

Default `find`/`show` browsing requires #5375 to merge and its full site build to
publish `data/conjectures.json` and `data/catalog-manifest.json`. There is no pilot
mirror or legacy projection fallback. Prior RC browsing checks established name
lookup only; they did not establish statement availability. The release gate now
requires actual statement text, source revision, and matching descriptor digest.
Local fixture tests are separate from deployment acceptance.
