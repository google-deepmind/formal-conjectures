# Toolkit 0.2.0rc1 qualification

This is a fork release candidate. It is not a complete release or an upstream
acceptance claim. The reproducible tests run under the Toolkit package qualification
workflow on Linux and macOS. Release assets are built from the tagged source
archive and include checksums.

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
- Real poisoned-build isolation: invalid candidate rejected after scratch Lake
  tampering; valid candidate builds twice.
- Disposable Git archive tests for idempotency, failed upload, stale target, and
  older advisory requests. Completed local reports survive publication failure.

## Release gates still tracked

- Complete the macOS-to-Linux proof journey on the final executor revision,
  including valid/invalid proofs, infrastructure errors, and sandbox controls.
- Record fresh-image setup qualification and published-asset installation results.
- Exercise concurrent advisory posting across separate controllers; GitHub comment
  updates do not provide a transaction covering freshness reads and writes.
- Finish the five-case semantic pilot with human adjudication. Operational success
  is not mathematical review accuracy.
- Finish published-index/site ingestion and the independent reader handoff.

The CLI labels proof/publication experimental while these gates remain. The
canonical delivery and acceptance tracker is FC #4394, with #5376 and #5377.
