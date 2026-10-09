import WeilWidthArchCorrelationV25
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
AEGIS Ω — width-1/32 actual Archimedean budget V2.6.

This lane converts the V2.5 logarithmic autocorrelation estimates into the
actual repository Archimedean diagonal integrand.

For x = exp u and A = WeilAutocorrelationV1 g,

  exp(u) * Re(WeilArchimedeanIntegrandV1 A (exp u))
    = (exp(u) * Re A(exp u) - energy(g)) / sinh(u).

The V2.5 bound
  ||A(exp u)|| <= exp(-u/2) * energy(g)
then gives the exact small-window majorant consumed by the V2.4 frontier,
while width support makes the outer tail exact.

No off-diagonal estimate, global Weil sign, or RH conclusion is asserted here.
-/

open Set Function MeasureTheory Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilWidthArchBudgetV26

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilWidthDiagonalArchFrontierV24

def widthArchLogIntegrandV26
    (g : WeilCompactSmoothGV1) (u : ℝ) : ℝ :=
  (Real.exp u *
      (WeilAutocorrelationV1 g (Real.exp u)).re -
    energy g.1) / Real.sinh u

/-- V2.5 immediately gives the multiplicative autocorrelation decay on a
positive logarithmic displacement. -/
theorem autocorrelation_exp_norm_le_v26
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
      Real.exp (-u / 2) * energy g.1 := by
  have h :=
    norm_logCorrelation_le_energy_v25 g u
  rw [logCorrelation_eq_autocorrelation_v25] at h
  have hepos : 0 < Real.exp (u / 2) := Real.exp_pos _
  have hmul :
      Real.exp (u / 2) *
          ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
        energy g.1 := by
    simpa [norm_mul, Complex.norm_exp] using h
  have hdiv :
      ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
        energy g.1 / Real.exp (u / 2) := by
    rw [le_div_iff₀ hepos]
    simpa [mul_comm] using hmul
  calc
    ‖WeilAutocorrelationV1 g (Real.exp u)‖
        ≤ energy g.1 / Real.exp (u / 2) := hdiv
    _ = Real.exp (-u / 2) * energy g.1 := by
      rw [show -u / 2 = -(u / 2) by ring, Real.exp_neg]
      simp [div_eq_mul_inv, mul_comm]

/-- Real-part form used by the Archimedean numerator. -/
theorem autocorrelation_exp_re_le_v26
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    Real.exp u *
        (WeilAutocorrelationV1 g (Real.exp u)).re ≤
      Real.exp (u / 2) * energy g.1 := by
  have hre :
      (WeilAutocorrelationV1 g (Real.exp u)).re ≤
        ‖WeilAutocorrelationV1 g (Real.exp u)‖ :=
    Complex.re_le_norm _
  have hnorm := autocorrelation_exp_norm_le_v26 g u
  have hexp : 0 ≤ Real.exp u := (Real.exp_pos u).le
  have h1 := mul_le_mul_of_nonneg_left (hre.trans hnorm) hexp
  calc
    Real.exp u *
        (WeilAutocorrelationV1 g (Real.exp u)).re
        ≤ Real.exp u *
          (Real.exp (-u / 2) * energy g.1) := h1
    _ = Real.exp (u / 2) * energy g.1 := by
      calc
        Real.exp u * (Real.exp (-u / 2) * energy g.1)
            = (Real.exp u * Real.exp (-u / 2)) * energy g.1 := by ring
        _ = Real.exp (u + (-u / 2)) * energy g.1 := by
          rw [Real.exp_add]
        _ = Real.exp (u / 2) * energy g.1 := by
          congr 2
          ring

/-- Exact pointwise logarithmic form of the repository Archimedean diagonal
integrand. -/
theorem exp_mul_archimedean_re_eq_log_v26
    (g : WeilCompactSmoothGV1) {u : ℝ} (hu : 0 < u) :
    Real.exp u *
        (WeilArchimedeanIntegrandV1
          (WeilAutocorrelationV1 g) (Real.exp u)).re =
      widthArchLogIntegrandV26 g u := by
  let x : ℝ := Real.exp u
  let A : ℝ → ℂ := WeilAutocorrelationV1 g
  let E : ℝ := energy g.1
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.exp_pos u
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
  have hrec : A x⁻¹ = (x : ℂ) * conj (A x) := by
    dsimp [A]
    exact weil_autocorrelation_reciprocal_v1 g hxpos
  have hcenter_re : (A 1).re = E := by
    dsimp [A, E]
    exact AEGIS.WeilDiagonalKernelReductionV21.autocorrelation_one_re_eq_energy g
  have hcenter_im : (A 1).im = 0 := by
    dsimp [A]
    exact weil_autocorrelation_one_real_v1 g
  have hcenter : A 1 = (E : ℂ) := by
    apply Complex.ext
    · simpa using hcenter_re
    · simpa using hcenter_im
  have hnum :
      A x + (1 / (x : ℂ)) * A x⁻¹ -
          (2 / (x : ℂ)) * A 1 =
        ((2 * (A x).re - 2 * E / x : ℝ) : ℂ) := by
    rw [hrec, hcenter]
    apply Complex.ext
    · simp [hxC]
      field_simp [hxpos.ne']
      ring
    · simp [hxC]
  have hden :
      (x : ℂ) - ((x⁻¹ : ℝ) : ℂ) =
        ((x - x⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hsinh : 0 < Real.sinh u := by
    exact AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos hu
  have hdenR : x - x⁻¹ = 2 * Real.sinh u := by
    dsimp [x]
    rw [Real.sinh_eq, Real.exp_neg]
    ring
  unfold WeilArchimedeanIntegrandV1
  change x *
      ((A x + (1 / (x : ℂ)) * A x⁻¹ -
          (2 / (x : ℂ)) * A 1) /
        ((x : ℂ) - ((x⁻¹ : ℝ) : ℂ))).re =
    widthArchLogIntegrandV26 g u
  rw [hnum, hden, Complex.div_ofReal_re]
  unfold widthArchLogIntegrandV26
  dsimp [x, A, E]
  rw [hdenR]
  field_simp [hsinh.ne']

private theorem exp_sub_one_le_self_mul_exp_v26
    {v : ℝ} (hv : 0 ≤ v) :
    Real.exp v - 1 ≤ v * Real.exp v := by
  have h := Real.add_one_le_exp (-v)
  have hm :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos v).le
  have hexp : Real.exp v * Real.exp (-v) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hexp] at hm
  nlinarith

/-- On the retained inner log-window, the transformed real Archimedean
integrand is bounded by the exact constant that integrates to
diagonalSmallV21 times energy. -/
theorem width_arch_log_inner_pointwise_v26
    (g : WeilCompactSmoothGV1) {u : ℝ}
    (hu0 : 0 < u) (huw : u ≤ (1 / 32 : ℝ)) :
    widthArchLogIntegrandV26 g u ≤
      energy g.1 * (Real.exp (1 / 64 : ℝ) / 2) := by
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hsinh : 0 < Real.sinh u :=
    AEGIS.WeilArchimedeanCothTailV1.sinh_pos_of_pos hu0
  have hnum :=
    autocorrelation_exp_re_le_v26 g u
  have hnum' :
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re -
          energy g.1 ≤
        energy g.1 * (Real.exp (u / 2) - 1) := by
    nlinarith
  have huv : 0 ≤ u / 2 := by linarith
  have hexp :=
    exp_sub_one_le_self_mul_exp_v26 huv
  have hsinh_ge : u ≤ Real.sinh u :=
    Real.self_le_sinh_iff.mpr hu0.le
  have hexpmono :
      Real.exp (u / 2) ≤ Real.exp (1 / 64 : ℝ) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hkernel :
      (Real.exp (u / 2) - 1) / Real.sinh u ≤
        Real.exp (1 / 64 : ℝ) / 2 := by
    rw [div_le_iff₀ hsinh]
    have h1 :
        Real.exp (u / 2) - 1 ≤
          (u / 2) * Real.exp (u / 2) := hexp
    have h2 :
        (u / 2) * Real.exp (u / 2) ≤
          (Real.sinh u / 2) * Real.exp (1 / 64 : ℝ) := by
      exact mul_le_mul
        (by linarith [hsinh_ge])
        hexpmono
        (Real.exp_pos _).le
        (by linarith [hu0])
    calc
      Real.exp (u / 2) - 1
          ≤ (u / 2) * Real.exp (u / 2) := h1
      _ ≤ (Real.sinh u / 2) * Real.exp (1 / 64 : ℝ) := h2
      _ = (Real.exp (1 / 64 : ℝ) / 2) * Real.sinh u := by ring
  unfold widthArchLogIntegrandV26
  have hdiv :
      (Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re -
          energy g.1) / Real.sinh u ≤
        (energy g.1 * (Real.exp (u / 2) - 1)) / Real.sinh u := by
    exact div_le_div_of_nonneg_right hnum' hsinh.le
  calc
    (Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re -
        energy g.1) / Real.sinh u
        ≤ energy g.1 *
            ((Real.exp (u / 2) - 1) / Real.sinh u) := by
          simpa [mul_div_assoc] using hdiv
    _ ≤ energy g.1 * (Real.exp (1 / 64 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hkernel hE

/-- Outside the width difference-support, the transformed integrand is exactly
the negative 1/sinh tail. -/
theorem width_arch_log_tail_eq_v26
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a)
    {u : ℝ} (hu : (1 / 32 : ℝ) < u) :
    widthArchLogIntegrandV26 g u =
      -energy g.1 / Real.sinh u := by
  have hC := logCorrelation_zero_of_width_v25 g a u hw hu
  rw [logCorrelation_eq_autocorrelation_v25] at hC
  have he :
      (Real.exp (u / 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hA :
      WeilAutocorrelationV1 g (Real.exp u) = 0 := by
    exact (mul_eq_zero.mp hC).resolve_left he
  unfold widthArchLogIntegrandV26
  rw [hA]
  simp

end AEGIS.WeilWidthArchBudgetV26

#print axioms AEGIS.WeilWidthArchBudgetV26.autocorrelation_exp_norm_le_v26
#print axioms AEGIS.WeilWidthArchBudgetV26.exp_mul_archimedean_re_eq_log_v26
#print axioms AEGIS.WeilWidthArchBudgetV26.width_arch_log_inner_pointwise_v26
#print axioms AEGIS.WeilWidthArchBudgetV26.width_arch_log_tail_eq_v26
