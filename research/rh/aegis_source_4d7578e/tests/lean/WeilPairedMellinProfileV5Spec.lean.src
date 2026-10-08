import WeilPairedMellinProfileV5

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

example (f : WeilCompactSmoothGV1) (c : ℝ) :
    HasVerticalNormMomentsTwoV3 (WeilPairedMellinProfileV5 f c) :=
  weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c

example (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
      (2 * _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t) =
      ∑' ρ : LiCriterion.NontrivialZero,
        ∫ t : ℝ,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) *
              WeilPairedMellinProfileV5 f c t :=
  riemannXi_paired_mellin_logDeriv_fixed_line_integral_v5 f c hc
