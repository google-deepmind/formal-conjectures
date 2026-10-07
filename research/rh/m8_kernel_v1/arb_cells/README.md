# All 2,198 finite cells of the L = 4/5 Krein certificate: Arb enclosure

`arb_cells.py` checks, in rigorous ball arithmetic (Arb through python-flint
0.8.0, 256-bit), the per-cell inequality consumed by `CellAnalyticSoundV1`:

```
correctionSymbol t + W t · (S t − 1/16) − W t · lv  ≥  0     for t ∈ [lo, hi],
W t = (t² + 1/4)²
```

for every serialized cell `1 … 2198` of
`research/rh/krein_order19_v1/certificate.json` (SHA-256
`790fb6ee2e8cf6c07cf2d829e8d1046dee214d41dea19ee1009f19afb03323a6`).
Cell `0` contains `t = 0`, where the script's `sinc` series is undefined; it is
already closed in the kernel (`RHKreinFirstCellV1`).

Each cell is enclosed by a degree-8 Taylor model about its centre (eighth
coefficient enclosed over the whole cell) and the sign-independent floor
`a₀ − Σ |a_k| r^k`, the same shape as `term_lower` in the Lean cell modules;
undecided cells are bisected.

| mode | `S` | result | pieces | smallest floor |
|---|---|---|---|---|
| `exact` | `symbol t` itself | 2198 / 2198 positive | 2693 | 3.9·10⁻⁴ (cell 8) |
| `lean` | lower bound built only from facts already proved in the tree | 2198 / 2198 positive | 2318 | 2.2·10⁻⁴ (cell 2), else ≥ 7.6·10⁻⁴ |

The `lean` bound is

```
−5773/10000 + Σ_{n<128} quarterTerm lo n − (3/4)(1/(128+1/4) + 1/(128+1/4)²)
  − 1144729886/10⁹ − A₀ cos(t L₀) − A₀ t·10⁻¹⁰ − 2·10⁻⁹,
A₀ = 1414213562/10⁹ · 6931471806/10¹⁰,   L₀ = 287209/414355,
```

i.e. `digamma_sharp_lower_of_sq_le` at the left endpoint (monotonicity of
`Re ψ(1/4 + it/2)` in `t²`), `γ < 0.5773`, the rational `log π` upper bound,
and `|log 2 − 287209/414355| ≤ 10⁻¹⁰` (Mathlib `Real.log_two_near_10`), with the
prime cosine kept exact instead of replaced by `1`.

## What this changes

The earlier per-cell route froze the whole symbol at the left endpoint
(`cos(t log 2) ≤ 1`). That loses `√2 log 2 (1 − cos(t log 2)) · W t`, which is
already `≈ 0.26` at `t ≈ 0.96` and is why the fifteenth-cell floor stopped
working from cell 15 on. Keeping the prime cosine as a polynomial in the cell
variable (the same addition-formula expansion used for the edge term) removes
the loss. With that, every cell closes with bounds the kernel already has, and
no further analytic input is needed for this window.

## Status

This is a machine-checked *numerical* enclosure, not a Lean proof. The kernel
closure of cells 15–2198 still has to be generated (per-cell or per-block
Taylor-model modules) and replayed. It concerns one window only. It does not
cover the tail `t ≥ 300`, the other windows, or the Riemann hypothesis.
AUTHORITY_EFFECT = NONE.

## Reproduce

```
pip install python-flint==0.8.0
KREIN_CERT=research/rh/krein_order19_v1/certificate.json \
EXPLICIT_CORRECTION=AEGISOverlay/RHKreinExplicitCorrectionV1.lean \
  python3 arb_cells.py lean > arb_lean.txt     # ≈ 10 s
```

The two output listings are not committed; they regenerate byte-for-byte in a few
seconds and are pinned by the hashes below.

Negative control: adding `1/50` to every `lv` makes 29 of cells 1–40 fail in
`lean` mode (6 in `exact` mode), so the check rejects violated cells rather than
passing everything.

| file | SHA-256 |
|---|---|
| `arb_cells.py` | `b5c8a90c02dbcd3774de7361e90502e64635357226a99b30bb2309c37e3bf95a` |
| `arb_exact.txt` | `0c5e66ea3f7f0df9e0e7ef3f5e07b427e36feb3916d837d35c6e1300666fd91e` |
| `arb_lean.txt` | `1d205fcc59c9029aca1eedf6c34a83f12ae1aafb7f786075963eacf81742304a` |
