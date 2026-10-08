# AEGIS Ω → Formal Conjectures: pinned RH source transfer (2026-10-08)

**Status:** EVIDENCE_ONLY / NOT_ADMITTED.  This file records a content-addressed research archive, not a proof of the Riemann Hypothesis. The official target remains open at `AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10`.

## Source comparison

- AEGIS #679 at `4d7578ef3df6ae4d1bcd6e2eaefeb2f7f5309afe`: 191 byte-exact formal Lean source files archived as `*.lean.src`, plus 4 nonidentical research artifacts from its source revision. Archive: `research/rh/aegis_source_4d7578e/`.
- AEGIS #699 at `0c1477fb032bb979a1bc61efd23caa4cacfe376c`: 80 byte-exact UTF-8 `research/rh` files, including Krein primal, certificates and Feshbach receipts. Archive: `research/rh/aegis_source_0c1477f/`.
- AEGIS #693 at `4f93fffcea401e8ede433cc27d525ff7ad1579e3`: 16 additional/alternate byte-exact Epstein and critical-line source files not identical to the two snapshots above. Archive: `research/rh/aegis_source_4f93fff/`.

**Verified file total:** 291/291 staged paths matched their pinned Git blob SHA during assembly. Full per-file source/path/hash/size evidence is in `AEGIS_RH_SOURCE_PORT_MANIFEST_20261008.json`.

### Explicit exclusions

- Binary `research/rh/feshbach_arb_v2/L1.2/blocks_N100_NP10000.json.gz` (3272172 bytes), Git blob `11b7f66ce9245b825f01b249212a9ec52bd2360b`; read at https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/0c1477fb032bb979a1bc61efd23caa4cacfe376c/research/rh/feshbach_arb_v2/L1.2/blocks_N100_NP10000.json.gz
- Binary `research/rh/feshbach_arb_v2/L1.3/blocks_N100_NP42000.json.gz` (3275497 bytes), Git blob `610da292e15b7fd72a754fa72ed50a98f7a73587`; read at https://github.com/Aegis-Omega/AEGIS-OMEGA/blob/0c1477fb032bb979a1bc61efd23caa4cacfe376c/research/rh/feshbach_arb_v2/L1.3/blocks_N100_NP42000.json.gz

Those 2 compressed upstream blobs could not be copied by the connected GitHub text-only API; their immutable links and original blob SHA are preserved. No claim of a complete binary mirror is made.

## Distinctions that must not be collapsed

- Existing fork PR #63 holds the **active, main-rooted** integration of fork PR #13, PR #16 and PR #62 source files and the exact official RH proof target. The archived sources here **do not automatically participate in the Lean import graph** and do not replace these adapted proof modules.
- The original AEGIS sources do not generally have matching byte hashes to the fork's adapted theorem files, even when names match. They are preserved separately to prevent overwriting valid work.
- Passing a module compile, `#print axioms`, or a CI check proves only the particular checked statement, not that RH's remaining positivity theorem has been discharged.
- Neither the upstream branch ancestry nor the two large compressed certificate blobs have been merged into the fork. No branch deletions, force pushes, authority expansion, protected-main mutations, or unconditional RH claims.

## Source and verification contract

Use `source_pin`, `source_path` and `blob_sha` in the JSON manifest to reconstruct or check byte-identity. Rename a `*.lean.src` copy to `*.lean` only in a pinned isolated Lean workspace with all dependencies resolved, then replay the exact theorem statements and inspect axioms. Numerical receipts remain empirical inputs; their existence is not a formal proof.
