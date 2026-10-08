import WeilFixedLineFubiniCoreV3

open Complex MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- Freeze the paired zero kernel in the actual nontrivial-zero carrier. -/
example (c t : ℝ) (ρ : LiCriterion.NontrivialZero) :
    WeilPairedZeroKernelV3 c t ρ =
      1 / (((c : ℂ) + (t : ℂ) * I) - ρ.val) +
      1 / (((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val)) := rfl

/-- Freeze the exact rational cancellation used for the central-height O(h^-2) bound. -/
example (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    WeilPairedZeroKernelV3 c t ρ =
      (2 * ((c : ℂ) + (t : ℂ) * I) - 1) /
        ((((c : ℂ) + (t : ℂ) * I) - ρ.val) *
          (((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val))) :=
  weil_paired_zero_kernel_eq_quotient_v3 c t ρ hc

/-- Freeze the FZ core: second weighted L1 moment of H is enough for the
multiplicity-weighted paired-kernel product integrals to be summable. -/
example (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
        ∫ t : ℝ, ‖WeilPairedZeroKernelV3 c t ρ * H t‖) :=
  riemannXi_paired_kernel_product_integral_summable_v3 H c hc hH
