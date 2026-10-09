# AEGIS Ω — RH proof-spine main-root intake V1

This is an **independent main-based composite**, not another PR-on-PR branch.

- Protected upstream / fork base: `tarikskalic33/formal-conjectures@02da1ad1288b4881ea1f8e575fbe84af7db04364` (`main`).
- Exact copied source heads: PR #13 `a6a74532e46fbe38fbe5737928dbbfd340b0127e`, PR #16 `110eec990577be4ec602e93c76293bce077a3cdd`, PR #62 `78cf37e2f837dcaac1fface0ea1b7c04804f70a1`.
- `228` changed source blobs (`79+3+146`), zero overlapping changed paths, exact original Git blob SHAs for each file.
- The initial assembly commit is parented **directly to main**. No source-branch commit ancestry is imported.
- `source_manifest.json` lists every imported path, originating PR and exact Git blob SHA, plus original main blob when present.
- Workflow and Lean validation is **not implied** by this tree copy. Current-head checks and theorem axiom audits must run independently.
- In particular, the original official `RiemannHypothesis.riemannHypothesis` still fails with the unsolved `UniversalZeroQuadraticNonnegativeV10` residual until an actual Lean proof exists; no `sorry`, axiom or assumption is supplied by assembly.

`AUTHORITY_EFFECT=NONE` · `RH_PROVEN_UNCONDITIONALLY=false` · `NO_MAIN_MUTATION`.
