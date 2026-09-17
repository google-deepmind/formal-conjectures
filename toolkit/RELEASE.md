# Toolkit 0.2.0rc3 qualification

RC3 is a fork release candidate. Upstream acceptance, production deployment and
mathematical review accuracy are separate from a successful fork qualification.
The [qualification record](qualification/rc3-final.md) contains exact runs,
revisions, retained failures and remaining gates.

| Area | RC3 coverage |
| --- | --- |
| Existing agents | No model launcher or AI authentication. Bundled procedure, writable review draft, portable skill discovery and explicit completion. |
| Review | Independent scoped build, bounded sources, retained findings, current/historical inspection and useful next actions. |
| Publication | Explicit immutable archival, one serialized Actions publisher, cancellation/retry receipts, revision checks and one bot-owned comment. |
| Proof | Native exact-target workspaces; pinned Linux executor, Comparator, Landrun, compatible exporter and both kernels. Typed success, rejection and unevaluated infrastructure error remain distinct. |
| Distribution | Wheel built from its source distribution; clean macOS/Linux installation without a checkout or AI credentials. uv owns installation, upgrade and uninstall. |
| Pilot | Five development-exposed attempts, qualitatively approved by William. Two coverage gaps remain; no broad accuracy claim. |

Proof and publication remain labelled experimental until all applicable acceptance
journeys pass. The configured executor and publisher are independently pinned;
installing a newer client does not change them. Rerun affected qualification before
adopting accepted upstream dependency revisions.

Default `find` and `show` require upstream #5375 to merge and deploy its full
`data/conjectures.json` and `data/catalog-manifest.json`. An explicitly configured
fork can be tested now; there is no automatic fork or statement-free fallback.
The website and board must retain exact repository joins. The upstream queue cannot
establish applicability for a disposable fork PR.

[#4394](https://github.com/google-deepmind/formal-conjectures/issues/4394) owns the
merge order. [#5376](https://github.com/google-deepmind/formal-conjectures/issues/5376)
and [#5377](https://github.com/google-deepmind/formal-conjectures/issues/5377) track
contribution and public reader acceptance. Do not close them solely because a fork
release exists. RC2's records and earlier operator comments remain historical;
local comment writes are no longer the supported publication path.
