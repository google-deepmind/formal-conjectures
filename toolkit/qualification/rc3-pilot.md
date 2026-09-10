# RC3 pilot: adjudication packet

Human assessment is pending. This is one development-exposed existing-agent attempt per case, not a blinded accuracy benchmark. No paid model calls were made. Model identity, token usage and per-case effort were unavailable. All five independent builds passed.

The frozen manifest SHA-256 is `63272348d7e43ea80d7e5755243859b6a1daefec69b65a678c98d1a9ec8ce834`. Original records remain in `.conjectures/qualification/rc3/` and `.conjectures/runs/`. #5391 was excluded before attempts because its shared-utility changes exceeded supported scope; #5344 replaced it. No case was replaced after an attempt.

| Case | Provisional result | Coverage gap | Human assessment |
|---|---|---|---|
| [#5402](https://github.com/google-deepmind/formal-conjectures/pull/5402) | pass | None identified | Pending |
| [#5397](https://github.com/google-deepmind/formal-conjectures/pull/5397) | incomplete | Fox–Kleitman primary source absent | Pending |
| [#4862](https://github.com/google-deepmind/formal-conjectures/pull/4862) | pass | None identified | Pending |
| [#5091](https://github.com/google-deepmind/formal-conjectures/pull/5091) | incomplete | Exact registry receipt and predicate bridge unverified | Pending |
| [#5344](https://github.com/google-deepmind/formal-conjectures/pull/5344) | pass | None identified | Pending |

No actionable findings or counterexamples were established. That does not establish an absence of missed issues. Assess each case for missed issues, usefulness and review effort; assess the two coverage questions for whether they are useful and appropriately scoped.

## #5402

Run: `20260910T085059Z-49ed306611d4`. Head: `4c21df9f12a7480460fcb74117d184109cab4d17`. Base: `b82b08faa9006484021c12005ab41287fb2ffb69`.

The changed Hilbert fifth statement matches the locally Euclidean formulation in retained Tao source-05. LieGroupPresentation supplies a continuous group isomorphism to an analytic Lie group in the same dimension and deliberately does not assume second countability. Checked the shared definition and the discrete zero-dimensional boundary. The retained Pardon abstract supports the 3-manifold variant. No actionable discrepancy established; this is statement review, not independent proof verification.

Frozen sources:
- [https://arxiv.org/abs/1112.2324](https://arxiv.org/abs/1112.2324); retained record SHA-256 `c2f6acff7bbfcfc1ab972772b4c9b2e6c75e1abb26e5a86ce764208775619597`.
- [https://doi.org/10.1090/S0894-0347-2013-00766-3](https://doi.org/10.1090/S0894-0347-2013-00766-3); retained record SHA-256 `81b772b5e085e922dfd6dae8fcca44e7359edb1a3bcbe97572b02b77cb8a49f4`.
- [https://doi.org/10.2307/1968928](https://doi.org/10.2307/1968928); retained record SHA-256 `14efec1d3bd0ae383a72728e83391f20a72decc2ef8a56bf0f7d330aa05ac619`.
- [https://doi.org/10.4171/LEM/61-1/2-2](https://doi.org/10.4171/LEM/61-1/2-2); retained record SHA-256 `bf82ce9c2274ac15ef3be882c582629f931d76959f93e61fcaae23ceb432af8a`.
- [https://en.wikipedia.org/wiki/Hilbert%E2%80%93Smith_conjecture](https://en.wikipedia.org/wiki/Hilbert%E2%80%93Smith_conjecture); retained record SHA-256 `c96ae3e2a5145fdc259b2560556d6c3a45457f89ecfa539d0578754827bfa02d`.
- [https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/](https://terrytao.wordpress.com/2011/08/13/the-hilbert-smith-conjecture/); retained record SHA-256 `6991173178b74b385d64d42855c666fa2d012934fdcb591f12f4a3a771103fad`.
- [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0); retained record SHA-256 `585e251ab92ddf7e487f84f9b87ddcf8a2cfaea289f9290598ee6e61c747e827`.

Human assessment: **pending**. Supported findings: —. Unsupported findings: —. Missed issues: —. Useful: —. Effort: —.

## #5397

Run: `20260910T085236Z-1ee12e170830`. Head: `9424d82628b3dcf4102b10fd6e7c4563fd8b178b`. Base: `71d1b446c02a001c3055e59bbe7fd968ac6c97dc`.

The new positive-arity guard excludes the empty tuple while retaining uniform dependence on k rather than p. Read the complete module and Green Problem 21. Existing built tests cover the empty infimum and the one-colour positive example. The frozen source collection includes Green’s secondary account, but not Fox–Kleitman Conjecture 5 itself; the exact primary-source arity convention remains unconfirmed.

Frozen sources:
- [https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.21](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.21); retained record SHA-256 `853c825a4794bb7f1f669567bfdc04a2546de5681010bfe820b336a2fb7e46b1`.
- [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0); retained record SHA-256 `eb364781cbe9125ea858145f5cbe92f45ad6ff539bf43803f833b1b1dbac9bde`.

Human assessment: **pending**. Supported findings: —. Unsupported findings: —. Missed issues: —. Useful: —. Effort: —.

## #4862

Run: `20260910T085313Z-ef10511ac766`. Head: `722a53b212b9e101493499cc4834ec22b0275015`. Base: `5a13d480c38611f1381ba345f5933e9c29544c08`.

The retained Luo–Yang–Zhu abstract states the same quantifier order: every fixed positive lambda, all sufficiently large n, all complex tuples of modulus at least one, a power between 2 and n+1 exceeding exp(-lambda*n). The answer(False) correction agrees with that source; choose lambda=log C for the claimed contradiction. Finite indexing and the original z1 normalization are represented consistently. The remaining variants match the retained Erdős problem-page summary. No proof verification was performed.

Frozen sources:
- [https://arxiv.org/abs/2607.22017](https://arxiv.org/abs/2607.22017); retained record SHA-256 `1f5158362968c26688462fa190a7b6f74221a115b746dc4ebc5e6bd0ee0e3765`.
- [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0); retained record SHA-256 `dafe52bd0b800f4962c36e0e31101e18f145e02f5b45b0daede0558a7cd52901`.
- [https://www.erdosproblems.com/latex/973](https://www.erdosproblems.com/latex/973); retained record SHA-256 `d5357c8a33506838a08bcf8a6d3c4460d7edf9839d4cd33e295ca12b0664327e`.

Human assessment: **pending**. Supported findings: —. Unsupported findings: —. Missed issues: —. Useful: —. Effort: —.

## #5091

Run: `20260910T085332Z-46a2906db330`. Head: `d4e7385685fdd403563b597dc50eca87663d6cc4`. Base: `5a13d480c38611f1381ba345f5933e9c29544c08`.

The retained Erdős source now reports the infinitude result, consistent with research solved and answer(True). The explicit-pair proofs build. The linked source contains pairSet_infinite, but the retained registry page is only a JavaScript shell and does not expose the pinned registration/Comparator receipt. Its FullDensityCore.PairSet is not independently matched to the FC S predicate in this run. Keep the proof-verification claim unconfirmed rather than infer rejection or acceptance.

Frozen sources:
- [https://github.com/williamjblair/lean-proofs/blob/03729c9cbb0b602f5a828bb850c85e84c5a6d460/ErdosProblems/Erdos730/FullDensityTheorem.lean#L40](https://github.com/williamjblair/lean-proofs/blob/03729c9cbb0b602f5a828bb850c85e84c5a6d460/ErdosProblems/Erdos730/FullDensityTheorem.lean#L40); retained record SHA-256 `4bf0900a0a4c3c0641a1441a416aa58577de57cf754c37ec6cf33f38f1a3d4df`.
- [https://oeis.org/A129515](https://oeis.org/A129515); retained record SHA-256 `b1fc942254657cc7a9db9645536f686bd942991f6879080b45bae5a568b6f051`.
- [https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-22-000001&version=1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-22-000001&version=1); retained record SHA-256 `3cb6aa3685636f35dc6801d38ffabe78dd5497b4889884e93163d966afa61362`.
- [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0); retained record SHA-256 `b77e62aee047d40c8a4e4d15d95e9145bc3badcb854bec8852a91b8232217515`.
- [https://www.erdosproblems.com/latex/730](https://www.erdosproblems.com/latex/730); retained record SHA-256 `177a708c7174239551d2578d1a4e81bc32262230ccbe51b4a6c958e55974d1d7`.

Human assessment: **pending**. Supported findings: —. Unsupported findings: —. Missed issues: —. Useful: —. Effort: —.

## #5344

Run: `20260910T085507Z-f58591bc0c8f`. Head: `ffce175fe3e33e1b9b2f9ba453ba2d7dd9b20c7f`. Base: `d33e35a5f45386a173b31159ae6598b1968bc463`.

The definition now counts exactly k denominators through Fin k. StrictMono supplies increasing distinct denominators and the lower bound supplies positivity for N>=1. Nat.find selects the least cardinality; finite N=0 behavior does not affect either atTop statement. The main limit and the eventual Ioc bound match retained Erdős source-01. No actionable discrepancy established.

Frozen sources:
- [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0); retained record SHA-256 `faa83ca08ee352427199bbc5559c76125fb29d38d8a2233e1cda1a969a1f72e2`.
- [https://www.erdosproblems.com/latex/295](https://www.erdosproblems.com/latex/295); retained record SHA-256 `81539914c3ae23a091ab4afacb0ae7e9bd84e01c8b56245e2a65f8ee8e11667d`.

Human assessment: **pending**. Supported findings: —. Unsupported findings: —. Missed issues: —. Useful: —. Effort: —.
