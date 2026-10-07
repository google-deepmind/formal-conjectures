# The L = 21/20 Krein window

Target: nonnegativity of the zeta zero quadratic on every moment-zero packet of logarithmic
half-width `r` with `2r < 21/20`. It goes through `RHKreinZetaBridgeV1.certificate_zero_quadratic_nonneg`
with `m = 0`.

The certificate is the SVD-regularized LP solution `krein_lp_L1.05_svd.json`: 399 hats at
`u_k = 21/20 + (k+1)/50` and five `δ` terms. Its coefficients are taken as the exact dyadic values
of the stored binary64 numbers.

## Structure

- **`RHKreinL105CheckerV1.checkWide`** builds one Taylor model per wide cell and checks each piece
  by re-centring that polynomial (`shiftPoly`). The model has:
  - the hat sum, as 399 columns advanced by one rotation each. The column error uses
    `Complex.exp_bound'`, so cells of radius 1/2 work with frequencies up to 9.05;
  - a crude ball `|hats| ≤ (2/50)(100/t)²Σ|c|` on cells where the hats are negligible;
  - the δ terms, the prime cosine and the weight;
  - the digamma head `Σ_{n<K₀}` as a complex geometric series.

  The remaining digamma terms enter as a monotone constant per piece, with the sharp telescoping
  tail of `RHKreinDigammaSharpTailV1`.
- **`checkWide_sound`** proves `0 ≤ Fcert t` on the cell. Its axioms are the standard three.
- **`RHKreinL105TailV1`** has three parts:
  - `tail_nonneg`: for `t ≥ 3000`, `Fcert ≥ t⁴(κ − B)`, with κ and B checked by `decide`;
  - `Fcert_even`;
  - `glue`.
- **`RHKreinL105BridgeV1.zero_quadratic_nonneg_L105`** turns `Fcert ≥ 0` on `[0, 3000]` plus the
  tail check into the zero-quadratic statement. Compiled, standard axioms.
- **`RHKreinHatAtV1`** is a triangular hat column at any centre: Fourier transform, support and
  integrability.
- **`RHKreinDigammaSharpTailV1`** proves
  `Re ψ(1/4+it/2) ≥ −γ + Σ_{n<N} q_n(t) − (3/4)(1/a_N + 1/a_N²) + T/(2a_N²+T)`.

## Design

`tools/design105F.json` is produced by the exact mirror `tools/m105.py` (`sweep.py`, `minN.py`,
`deg16.py`). It has 1744 wide cells: 170 with full hat models and 1574 with the hat ball. There
are 4517 pieces, and every piece passes in the mirror. Each cell carries its own Taylor degree
(36 or 16), its number of digamma terms N (16–256), and K₀.

`tools/gen105.py` writes 116 batch modules with one `decide +kernel` per wide cell.
`tools/genall105.py` writes `RHKreinL105AllV1`.

## Build

The bridge requires the PR #693 versions of `WeilFixedLineGammaXSpaceV10`,
`WeilFixedLineCompletedGammaV10`, `WeilFixedLineGammaFubiniV10` and
`WeilFixedLineGammaAssemblyV10`. The `0 < c` hypothesis there replaces `1 < c`.

## Window chain

- **`RHWindowConnectedL105V1`** plugs the certificate into the repository window chain
  (`WeilWindowExhaustionV1`, `final_sign_implies_rh_v13`,
  `autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10`):
  - `window_lt_21_40`: every log window `[−L, L]` with `L < 21/40` has the arithmetic sign;
  - `rh_of_windows_from_21_40`: RH follows from the sign on the windows `L ≥ 21/40` alone.

  Both take the certificate's finite range (`hfin`) and tail check (`htail`) as hypotheses and
  depend on `[propext, Classical.choice, Quot.sound]`. They were compiled against a tree in which
  the 17 bridge-chain modules were rebuilt on the PR #693 closure.
- **`RHWindowL105FinalV1`** discharges `hfin` and `htail` with `RHKreinL105AllV1`:
  - `window_lt_21_40 : 0 ≤ L → L < 21/40 → WindowArithmeticNonpositiveV1 L`, with no hypotheses;
  - `rh_of_windows_from_21_40 : (∀ L ≥ 21/40, WindowArithmeticNonpositiveV1 L) → RiemannHypothesis`.

## Status at this commit (2026-10-05)

- Kernel run complete: all 133 batch modules (116 batches; cells 12 and 13 split into 17
  sub-files by `tools/resplit.py`, every sub-cell re-checked in the exact mirror `tools/split.py`
  and glued back with `glue`) pass `decide +kernel`, one at a time.
- `RHKreinL105AllV1.zero_quadratic_nonneg_width_21_20`, `RHWindowConnectedL105V1` and
  `RHWindowL105FinalV1.{window_lt_21_40, rh_of_windows_from_21_40}` depend on
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- The batch modules are not committed. Regenerate them with `tools/gen105.py` and
  `tools/resplit.py` from `tools/design105F.json` (see Design).

The windows `L ≥ 21/40` are not proved. Not RH. AUTHORITY_EFFECT = NONE.
