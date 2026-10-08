# Full-space Feshbach certificate at L = 1.05 (Arb)

Claim (T1, interval arithmetic, not Lean): for every moment-zero G in L²[0, 1.05],

    Q(G) = (1/2π) ∫ |Ĝ(ξ)|² S(ξ) dξ  ≥  0.0025 ‖G‖²,
    S(ξ) = Re ψ(1/4 + iξ/2) − log π − √2 log 2 cos(ξ log 2),

which is the restricted Weil form at log-support width 1.05 (no pole term on the moment-zero subspace).
The previous certified margin at this width was 0.00025 (`KREIN_ARB_CERTIFICATE_L1.05.json`).
This is a fixed-width statement, not RH.

## Structure

H = moment-zero subspace of L²[0, L], A the operator of Q on H. V = moment-zero part of
span{e^{2πimx/L}, |m| ≤ 16} (dimension 31). Write H = V ⊕ (H ⊖ V). Then A ≥ μ on H if

    A11 − μ G11 − C_B / (c_∞ − μ) ≻ 0,   c_∞ ≤ inf_{H ⊖ V} A,   C_B ≥ ‖P_{H⊖V} A v‖² (as a form on V).

| step | file | what is enclosed |
|---|---|---|
| A11, G11 | `feshbach_blocks_arb.py` | cutoff-free CvS/CCM entries (`cvs_entries.py`, vendored from `guinand_weil_arb.py`) compressed to V |
| C_B | `feshbach_blocks_arb.py` | Σ_n \|(Qv)_n\|² over \|n\| ≤ 10000 in Arb, explicit 1/n tail for \|n\| > 10000, minus A11 G11⁻¹ A11 |
| Krein + slack | `verify_krein_slack_arb.py` | W(S − 0.99) + Ĥ + W s̄ ≥ 0 for all real ξ; Ĥ = hats on [L, L+4] (genuine functions); s̄ a step function on [0.05, 40] |
| c_∞ | `complement_trace_arb.py` | A − 0.99 ≥ −T on H with T = P_L M_s̄ P_L, so c_∞ ≥ 0.99 − tr(P T P); tr(P T P) = tr T − tr(Π T), Π onto V ⊕ span(e^{±x/2}); Gauss–Legendre with Bernstein-ellipse error balls |
| Schur | `schur_arb.py` | interval Cholesky of the 31×31 Schur matrix |

`run_all.sh` reproduces everything from scratch.

## Not machine-checked

- Identification of the CvS cutoff-free matrix with Q on the trigonometric basis (Groskin, arXiv:2607.02828, Lemma 2.1 / Thm 2.5);
  numerically the compressed spectrum agrees with an independent Fourier quadrature (0.1137, 0.7502, 0.8578).
- The Krein pairing ∫ |Ĝ₁|² Ĥ = 0 for hats supported in |u| ≥ L (Lean: `RHKreinGenuineCertificateV1`, not linked here).
- The Feshbach inequality and the tail bound for rows |n| > 10000 (derivation in `feshbach_blocks_arb.py` comments).

## Krein step with the Lean digamma minorant (`lean_digamma/`)

`../feshbach_arb_v2/verify_krein_slack_lemma.py` re-verifies the Krein + slack inequality without evaluating
Re ψ: on each cell [a, b] it uses the constant
LB(a) = −5792/10000 + Σ_{n<1024} quarterTerm(a, n) − (3/4)(1/(1024+1/4) + 1/(1024+1/4)²),
which is ≤ Re ψ(1/4 + it/2) for all t² ≥ a² by `AEGISOverlay/RHKreinDigammaMonotonicityV1.digamma_quarter_certificate_lower_of_sq_le`
(fork `tarikskalic33/formal-conjectures`; standard axioms). With the same LP, slack and m = 0.99 it certifies
F ≥ 0 on 12523 cells (exact rational endpoints, `lean_digamma/krein_cells.json`), zero cell [0, 1/20], and the tail
t ≥ 3000 (F/W ≥ 3.62, via LB(3000)). c_∞, C_B and the Schur step are unchanged, so μ = 0.0025 stands with the
archimedean weight now taken from a kernel-checked bound. Still not machine-checked: the per-cell Taylor models
(cosines of the prime and hat frequencies, Arb), the hat pairing, the CvS identification and the Feshbach step.
