import WeilFixedLineFubiniSwapV4

open Complex MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false

noncomputable section

example (f : WeilCompactSmoothGV1) (σ : ℝ) :
    HasVerticalNormMomentsTwoV3
      (fun γ : ℝ => mellin f.1 ((σ : ℂ) + (γ : ℂ) * I)) :=
  weil_compact_smooth_mellin_has_vertical_norm_moments_two_v3 f σ

example (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    (∑' ρ : LiCriterion.NontrivialZero,
      ∫ t : ℝ,
        ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          WeilPairedZeroKernelV3 c t ρ) * H t) =
      ∫ t : ℝ,
        ∑' ρ : LiCriterion.NontrivialZero,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t :=
  riemannXi_paired_kernel_integral_tsum_v4 H c hc hH

example (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    (∫ t : ℝ,
      (2 * _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I)) * H t) =
      ∑' ρ : LiCriterion.NontrivialZero,
        ∫ t : ℝ,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t :=
  riemannXi_paired_logDeriv_fixed_line_integral_v4 H c hc hH
