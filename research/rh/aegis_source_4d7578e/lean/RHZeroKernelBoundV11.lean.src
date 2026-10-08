import WeilZeroKernelHermitianV11
import RHFinalClosureSpineV1
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — four-phase bounds for the canonical zero translation kernel V11.

Assume the exact repository final-sign residual.  Through the whole explicit
formula this is equivalent to nonnegativity of the canonical zero quadratic
for every moment-zero compact-smooth packet.

Apply that nonnegativity to the four exact translated packets

  g + T_t g,
  g - T_t g,
  g + I T_t g,
  g - I T_t g.

Using the V11 Hermitian two-point expansion gives the sharp component box

  |Re K_g(t)| <= Q_g,
  |Im K_g(t)| <= Q_g,

where Q_g is real and nonnegative.  This is the formal version of the
four-phase step in the restricted Weil criterion.

AUTHORITY_EFFECT = NONE.
-/

open Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHZeroKernelBoundV11

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1

/-- Final sign gives nonnegativity of the real canonical zero quadratic. -/
theorem final_sign_zero_quadratic_nonnegative_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    0 ≤ (WeilAutocorrelationZeroQuadraticV11 g).re := by
  have hz :=
    (final_sign_residual_iff_zero_quadratic_nonnegative_v10.mp h)
      g hm
  simpa [WeilAutocorrelationZeroQuadraticV11] using hz

private theorem phase_one_lower_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    -(WeilAutocorrelationZeroQuadraticV11 g).re ≤
      (WeilZeroTranslationKernelV11 g d).re := by
  let p := WeilTwoPointTranslateV11 g d 1
  have hpMom := twoPointTranslate_preserves_moments_v11 g d 1 hm
  have hpNonneg :=
    final_sign_zero_quadratic_nonnegative_v11 h p hpMom
  have hexp :=
    congrArg Complex.re
      (twoPoint_zero_quadratic_hermitian_v11 g d 1 hm)
  change
    (WeilAutocorrelationZeroQuadraticV11 p).re =
      ((1 + (1 : ℂ) * conj (1 : ℂ)) *
          WeilAutocorrelationZeroQuadraticV11 g +
        (1 : ℂ) * WeilZeroTranslationKernelV11 g d +
        conj (1 : ℂ) *
          conj (WeilZeroTranslationKernelV11 g d)).re at hexp
  simp at hexp
  linarith

private theorem phase_neg_one_upper_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    (WeilZeroTranslationKernelV11 g d).re ≤
      (WeilAutocorrelationZeroQuadraticV11 g).re := by
  let p := WeilTwoPointTranslateV11 g d (-1)
  have hpMom := twoPointTranslate_preserves_moments_v11 g d (-1) hm
  have hpNonneg :=
    final_sign_zero_quadratic_nonnegative_v11 h p hpMom
  have hexp :=
    congrArg Complex.re
      (twoPoint_zero_quadratic_hermitian_v11 g d (-1) hm)
  change
    (WeilAutocorrelationZeroQuadraticV11 p).re =
      ((1 + (-1 : ℂ) * conj (-1 : ℂ)) *
          WeilAutocorrelationZeroQuadraticV11 g +
        (-1 : ℂ) * WeilZeroTranslationKernelV11 g d +
        conj (-1 : ℂ) *
          conj (WeilZeroTranslationKernelV11 g d)).re at hexp
  simp at hexp
  linarith

private theorem phase_i_upper_im_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    (WeilZeroTranslationKernelV11 g d).im ≤
      (WeilAutocorrelationZeroQuadraticV11 g).re := by
  let p := WeilTwoPointTranslateV11 g d I
  have hpMom := twoPointTranslate_preserves_moments_v11 g d I hm
  have hpNonneg :=
    final_sign_zero_quadratic_nonnegative_v11 h p hpMom
  have hexp :=
    congrArg Complex.re
      (twoPoint_zero_quadratic_hermitian_v11 g d I hm)
  change
    (WeilAutocorrelationZeroQuadraticV11 p).re =
      ((1 + I * conj I) *
          WeilAutocorrelationZeroQuadraticV11 g +
        I * WeilZeroTranslationKernelV11 g d +
        conj I * conj (WeilZeroTranslationKernelV11 g d)).re at hexp
  have hQreal :=
    autocorrelation_zero_quadratic_real_v11 g hm
  simp [Complex.mul_re, Complex.mul_im, hQreal] at hexp
  linarith

private theorem phase_neg_i_lower_im_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    -(WeilAutocorrelationZeroQuadraticV11 g).re ≤
      (WeilZeroTranslationKernelV11 g d).im := by
  let p := WeilTwoPointTranslateV11 g d (-I)
  have hpMom := twoPointTranslate_preserves_moments_v11 g d (-I) hm
  have hpNonneg :=
    final_sign_zero_quadratic_nonnegative_v11 h p hpMom
  have hexp :=
    congrArg Complex.re
      (twoPoint_zero_quadratic_hermitian_v11 g d (-I) hm)
  change
    (WeilAutocorrelationZeroQuadraticV11 p).re =
      ((1 + (-I) * conj (-I)) *
          WeilAutocorrelationZeroQuadraticV11 g +
        (-I) * WeilZeroTranslationKernelV11 g d +
        conj (-I) * conj (WeilZeroTranslationKernelV11 g d)).re at hexp
  have hQreal :=
    autocorrelation_zero_quadratic_real_v11 g hm
  simp [Complex.mul_re, Complex.mul_im, hQreal] at hexp
  linarith

/-- Exact four-phase component box for the canonical zero translation kernel. -/
theorem final_sign_zero_kernel_component_bounds_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    |(WeilZeroTranslationKernelV11 g d).re| ≤
        (WeilAutocorrelationZeroQuadraticV11 g).re ∧
      |(WeilZeroTranslationKernelV11 g d).im| ≤
        (WeilAutocorrelationZeroQuadraticV11 g).re := by
  constructor
  · rw [abs_le]
    exact ⟨
      phase_one_lower_v11 h g d hm,
      phase_neg_one_upper_v11 h g d hm⟩
  · rw [abs_le]
    exact ⟨
      phase_neg_i_lower_im_v11 h g d hm,
      phase_i_upper_im_v11 h g d hm⟩

/-- A convenient uniform norm bound, deliberately using constant 2 so no
square-root arithmetic is needed. -/
theorem final_sign_zero_kernel_norm_bound_v11
    (h : FinalSignResidualV1)
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hm : WeilMomentConditionsV1 g) :
    ‖WeilZeroTranslationKernelV11 g d‖ ≤
      2 * (WeilAutocorrelationZeroQuadraticV11 g).re := by
  obtain ⟨hre, him⟩ :=
    final_sign_zero_kernel_component_bounds_v11 h g d hm
  calc
    ‖WeilZeroTranslationKernelV11 g d‖
      ≤ |(WeilZeroTranslationKernelV11 g d).re| +
        |(WeilZeroTranslationKernelV11 g d).im| :=
          Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * (WeilAutocorrelationZeroQuadraticV11 g).re := by
          linarith

end AEGIS.RHZeroKernelBoundV11

#print axioms AEGIS.RHZeroKernelBoundV11.final_sign_zero_quadratic_nonnegative_v11
#print axioms AEGIS.RHZeroKernelBoundV11.final_sign_zero_kernel_component_bounds_v11
#print axioms AEGIS.RHZeroKernelBoundV11.final_sign_zero_kernel_norm_bound_v11
