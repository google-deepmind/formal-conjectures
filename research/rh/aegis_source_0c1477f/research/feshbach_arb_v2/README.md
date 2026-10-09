# Feshbach certificates beyond log 3 (Arb), general L

Same method as `../feshbach_arb_v1/` (L = 1.05), generalised to every prime power q < e^L in the symbol
S(ξ) = Re ψ(1/4 + iξ/2) − log π − Σ_q 2Λ(q) q^{−1/2} cos(ξ log q), in the Krein LP and in the Arb verifier.

| L | prime powers | low block | Krein + slack | c_∞ | Ritz λ₁ | certified μ |
|---|---|---|---|---|---|---|
| 1.2 | 2, 3 | N = 100 (199 dims), rows ≤ 10000 | m = 1.98, slack on [0.05, 450], step 1 | ≥ 1.9206 | 6.639e-5 | **5e-5** (fails 6e-5) |
| 1.3 | 2, 3 | N = 100, rows ≤ 42000 | m = 1.95, same slack layout | ≥ 1.8881 | 2.320e-6 | **2.1e-6** |
| 1.4 | 2, 3, 4 | N = 160 (319 dims), rows ≤ 16000, second-order tail (`TAIL_ORDER=2`) | m = 1.45, slack on [0.05, 560] | ≥ 1.4212 | 5.534e-8 | **5e-8** |
| 1.6 | 2, 3, 4 | N = 200 (399 dims), rows ≤ 16000, order-4 tail (`TAIL_ORDER=4`) | m = 1.35, slack on [0.05, 560] | ≥ 1.3232 | 5.353e-12 | **4.5e-12** |
| 1.8 | 2, 3, 4, 5 | N = 400 (799 dims), rows ≤ 16000, order-8 tail, weighted Cauchy–Schwarz (`TAIL_WEIGHTS=mixed`) | m = 1.05, slack on [0.01, 2000] | ≥ 0.9799 | 4.534e-17 | **4e-17** (fails 4.2e-17) |

Claim (T1, interval arithmetic, not Lean): Q(G) ≥ μ‖G‖² for every moment-zero G in L²[0, L].
Fixed widths, not RH. Each `L*/RECEIPT.json` lists inputs, SHA-256 of every output and the unformalised steps.

Reproduce: `./run_all.sh 1.2 100 10000 2.0 450 1.0 1.98 5e-5`, `./run_all.sh 1.3 100 42000 2.0 450 1.0 1.95 2.1e-6`,
`TAIL_ORDER=2 ./run_all.sh 1.4 160 16000 1.5 560 1.0 1.45 5e-8` `TAIL_ORDER=4 ./run_all.sh 1.6 200 16000 1.5 560 1.0 1.35 4.5e-12`,
`TAIL_ORDER=8 TAIL_WEIGHTS=mixed ./run_all.sh 1.8 400 16000 1.2 2000 1.0 1.05 4e-17 0.01` (block matrices for L ≥ 1.4 are not committed; hashes are in the receipts).

At L = 1.6 the comparable published bound is Zhu's 8.9e-18 (arXiv:2608.24827), for the full form with the pole term;
the numbers here are for the moment-zero (pole-free) restriction and are not directly comparable.
`blocks_*.json` is stored gzipped; `gunzip -k` it before running `schur_arb.py` by hand.

At L = 1.8 two changes were needed. The Krein zero cell [0, 0.05] fails (Taylor remainder from the large hat
coefficients), so the optional 9th argument narrows it to [0, 0.01]. The uniform Cauchy–Schwarz factor 2K + 3 = 19
dominated C_B, so `TAIL_WEIGHTS=mixed` uses weights p_i (sum 1, half uniform, half sqrt-optimal for the bottom Ritz
vector; any fixed p is a valid bound). The default `uniform` reproduces the earlier receipts exactly.
