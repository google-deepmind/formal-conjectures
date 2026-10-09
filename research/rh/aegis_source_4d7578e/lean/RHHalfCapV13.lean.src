import RHDyadicDiagonalV13
import WeilWidthArchBudgetV26
import Mathlib.Tactic

/-!
AEGIS Ω — the Cauchy–Schwarz half-cap for narrow autocorrelations, V13.

If the logarithmic lift of `g` is supported in `[a − r, a + r]` and the shift `u`
exceeds the half-width `r`, then the two overlapping pieces of the support lie on
opposite sides of the centre `a`: the factor `f v` needs `v < a`, the factor
`f (v + u)` needs `v + u > a`.  Pointwise AM–GM with these indicators and the
disjointness of `(−∞, a]` and `(a, ∞)` give

  ‖logCorrelation g u‖ ≤ energy g / 2,   hence   e^u·Re A(e^u) ≥ −e^{u/2}·energy g / 2,

half the cap `‖logCorrelation g u‖ ≤ energy g` used by the V26 route.  This is the
first positive-definiteness-type input beyond the pointwise cap.  Not RH.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHalfCapV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilWidthArchCorrelationV25
open AEGIS.RHDyadicDiagonalV13

/-- **Half-cap.**  For a shift beyond the half-width the correlation is at most half
the energy. -/
theorem half_cap_logCorrelation (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : r < u) :
    ‖logCorrelationV25 g u‖ ≤ energy g.1 / 2 := by
  set f : ℝ → ℂ := logLift g.1 with hf
  set F : ℝ → ℝ := fun w => ‖f w‖ ^ 2 with hF
  have hFi : Integrable F := logLift_sq_integrable_v25 g
  let q : ℝ → ℂ := fun v => f (v + u) * conj (f v)
  let M : ℝ → ℝ := fun v =>
    (1 / 2 : ℝ) * ((Ioi a).indicator F (v + u) + (Iic a).indicator F v)
  have hq : Integrable q := by simpa [q, f] using logCorrelation_integrable_v25 g u
  have hI1 : Integrable (fun v => (Ioi a).indicator F (v + u)) :=
    (hFi.indicator measurableSet_Ioi).comp_add_right u
  have hI2 : Integrable (fun v => (Iic a).indicator F v) :=
    hFi.indicator measurableSet_Iic
  have hM : Integrable M := (hI1.add hI2).const_mul (1 / 2 : ℝ)
  have hpoint : ∀ v : ℝ, ‖q v‖ ≤ M v := by
    intro v
    by_cases h0 : f v = 0
    · have : ‖q v‖ = 0 := by simp [q, h0]
      rw [this]
      unfold M
      apply mul_nonneg (by norm_num)
      apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    by_cases h1 : f (v + u) = 0
    · have : ‖q v‖ = 0 := by simp [q, h1]
      rw [this]
      unfold M
      apply mul_nonneg (by norm_num)
      apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    have hm0 : v ∈ tsupport f := subset_tsupport _ h0
    have hm1 : v + u ∈ tsupport f := subset_tsupport _ h1
    have hv := hw hm0
    have hvu := hw hm1
    have hA : v + u ∈ Ioi a := by
      show a < v + u
      linarith [hv.1]
    have hB : v ∈ Iic a := by
      show v ≤ a
      linarith [hvu.2]
    unfold M
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
    simp only [q, F, norm_mul, norm_conj]
    nlinarith [sq_nonneg (‖f (v + u)‖ - ‖f v‖)]
  have hshift : (∫ v : ℝ, (Ioi a).indicator F (v + u)) = ∫ w : ℝ, (Ioi a).indicator F w :=
    integral_add_right_eq_self (fun w => (Ioi a).indicator F w) u
  have hsplit : (∫ w : ℝ, (Ioi a).indicator F w) + (∫ w : ℝ, (Iic a).indicator F w) =
      ∫ w : ℝ, F w := by
    rw [integral_indicator measurableSet_Ioi, integral_indicator measurableSet_Iic, add_comm]
    have := integral_add_compl (measurableSet_Iic (a := a)) hFi
    rwa [compl_Iic] at this
  have hE : (∫ w : ℝ, F w) = energy g.1 := by
    simpa [F, f] using logLift_energy_eq_packet_energy g
  calc
    ‖logCorrelationV25 g u‖ = ‖∫ v : ℝ, q v‖ := by rfl
    _ ≤ ∫ v : ℝ, ‖q v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, M v := integral_mono hq.norm hM hpoint
    _ = (1 / 2 : ℝ) * ((∫ v : ℝ, (Ioi a).indicator F (v + u)) +
          ∫ v : ℝ, (Iic a).indicator F v) := by
      unfold M
      rw [integral_const_mul, integral_add hI1 hI2]
    _ = energy g.1 / 2 := by
      rw [hshift, hsplit, hE]
      ring

/-- The half-cap in the form consumed by the Archimedean majorant:
`e^u · Re A(e^u) ≥ −e^{u/2} · energy g / 2` for `u > r`. -/
theorem half_cap_exp_re_lower (g : WeilCompactSmoothGV1) (r a u : ℝ)
    (hw : HalfWidthAt g r a) (hu : r < u) :
    -(Real.exp (u / 2) * (energy g.1 / 2)) ≤
      Real.exp u * (WeilAutocorrelationV1 g (Real.exp u)).re := by
  have h := half_cap_logCorrelation g r a u hw hu
  rw [logCorrelation_eq_autocorrelation_v25] at h
  have hnorm : Real.exp (u / 2) * ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤ energy g.1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h
  have hre : -‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤ (WeilAutocorrelationV1 g (Real.exp u)).re :=
    le_trans (neg_le_neg (Complex.abs_re_le_norm _)) (neg_abs_le _)
  have hsplit : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he := Real.exp_pos (u / 2)
  have h1 := mul_le_mul_of_nonneg_left hre (Real.exp_pos u).le
  have h2 : Real.exp u * ‖WeilAutocorrelationV1 g (Real.exp u)‖ ≤
      Real.exp (u / 2) * (energy g.1 / 2) := by
    set N := ‖WeilAutocorrelationV1 g (Real.exp u)‖ with hN
    have hmul := mul_le_mul_of_nonneg_left hnorm he.le
    have heq : Real.exp u * N = Real.exp (u / 2) * (Real.exp (u / 2) * N) := by
      rw [← mul_assoc, ← hsplit]
    rw [heq]
    exact hmul
  linarith

end AEGIS.RHHalfCapV13

#print axioms AEGIS.RHHalfCapV13.half_cap_logCorrelation
#print axioms AEGIS.RHHalfCapV13.half_cap_exp_re_lower
