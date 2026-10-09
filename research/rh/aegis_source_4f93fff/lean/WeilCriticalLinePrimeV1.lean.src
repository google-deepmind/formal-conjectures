import WeilMellinInversionV1
import WeilAutocorrelationMellinV11
import Mathlib.Tactic

/-!
AEGIS Ω — autocorrelation values on the critical line (prime half of the bridge).

Mellin inversion on the line σ = 1/2 together with the V11 factorization gives,
for every x > 0,

  A_g(x) = (1/2π) ∫ x^{-(1/2+it)} |Mg(1/2+it)|² dt.

Evaluated at x = m and x = 1/m this is the critical-line form of the repository
prime term Λ(m)·(A_g(m) + A_g(1/m)/m), the arithmetic half of the bridge to the
Krein t-form.  No sign, positivity, or RH claim is made.  AUTHORITY_EFFECT = NONE.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilCriticalLinePrimeV1

open AEGIS.WeilAutocorrelationMellinV11

theorem one_sub_conj_critical_v1 (t : ℝ) :
    (1 : ℂ) - conj (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
  apply Complex.ext <;> norm_num

/-- Autocorrelation Mellin transform on the critical line is a squared modulus. -/
theorem autocorrelation_mellin_critical_v1 (g : WeilCompactSmoothGV1) (t : ℝ) :
    mellin (WeilAutocorrelationV1 g) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) : ℂ) := by
  rw [weil_autocorrelation_mellin_factorization_v11, one_sub_conj_critical_v1,
    Complex.mul_conj]

/-- Critical-line inversion formula for an autocorrelation packet. -/
theorem autocorrelation_critical_line_inversion_v1
    (g : WeilCompactSmoothGV1) {x : ℝ} (hx : 0 < x) :
    WeilAutocorrelationV1 g x =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
          (Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) : ℂ) := by
  have h := weil_compact_smooth_mellin_inversion_v1
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) hx
  change mellinInv (1 / 2) (mellin (WeilAutocorrelationV1 g)) x =
    WeilAutocorrelationV1 g x at h
  rw [← h]
  unfold mellinInv
  simp only [autocorrelation_mellin_critical_v1, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast
  ring

theorem cpow_pair_cos_v1 {m : ℝ} (hm : 0 < m) (t : ℝ) :
    (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) +
        (1 / (m : ℂ)) * ((m⁻¹ : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((2 * Real.exp (-(Real.log m) / 2) * Real.cos (t * Real.log m) : ℝ) : ℂ) := by
  set L := Real.log m with hL
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmi0 : ((m⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_pos.mpr hm).ne'
  have hlog1 : Complex.log (m : ℂ) = (L : ℂ) := by
    rw [hL, Complex.ofReal_log hm.le]
  have hlog2 : Complex.log ((m⁻¹ : ℝ) : ℂ) = ((-L : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (inv_pos.mpr hm).le, Real.log_inv, hL]
  have hinv : (1 / (m : ℂ)) = Complex.exp (((-L : ℝ) : ℂ)) := by
    rw [Complex.ofReal_neg, Complex.exp_neg, ← Complex.ofReal_exp, hL, Real.exp_log hm]
    simp
  rw [Complex.cpow_def_of_ne_zero hm0, Complex.cpow_def_of_ne_zero hmi0, hlog1, hlog2, hinv,
    ← Complex.exp_add]
  push_cast
  rw [Complex.cos]
  have e1 : (L : ℂ) * -((1 / 2 : ℂ) + (t : ℂ) * I) = (-L / 2 : ℂ) + (-((t : ℂ) * L * I)) := by ring
  have e2 : -(L : ℂ) + -(L : ℂ) * -((1 / 2 : ℂ) + (t : ℂ) * I) = (-L / 2 : ℂ) + (t : ℂ) * L * I := by ring
  have e3 : -((t : ℂ) * L * I) = -((t : ℂ) * L) * I := by ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add, e3]
  ring

/-- Critical-line density of an autocorrelation packet. -/
def criticalDensityV1 (g : WeilCompactSmoothGV1) (t : ℝ) : ℂ :=
  (Complex.normSq (mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) : ℂ)

theorem criticalDensity_integrable_v1 (g : WeilCompactSmoothGV1) :
    Integrable (criticalDensityV1 g) := by
  have h := weil_compact_smooth_mellin_vertical_integrable_all_v1
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2)
  have h' : Integrable (fun y : ℝ =>
      mellin (WeilAutocorrelationV1 g) (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) := h
  refine h'.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [autocorrelation_mellin_critical_v1]
  rfl

theorem cpow_mul_density_integrable_v1 (g : WeilCompactSmoothGV1) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * criticalDensityV1 g t) := by
  refine (criticalDensity_integrable_v1 g).bdd_mul (c := x ^ (-(1 / 2 : ℝ))) ?_ ?_
  · have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact (Continuous.const_cpow (by fun_prop) (Or.inl hx0)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp

/-- The repository prime pair `A(m) + A(1/m)/m` on the critical line. -/
theorem prime_pair_critical_cos_v1 (g : WeilCompactSmoothGV1) {m : ℝ} (hm : 0 < m) :
    WeilAutocorrelationV1 g m + (1 / (m : ℂ)) * WeilAutocorrelationV1 g (m⁻¹) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, ((2 * Real.exp (-(Real.log m) / 2) * Real.cos (t * Real.log m) : ℝ) : ℂ) *
          criticalDensityV1 g t := by
  have hmi : 0 < m⁻¹ := inv_pos.mpr hm
  rw [autocorrelation_critical_line_inversion_v1 g hm,
    autocorrelation_critical_line_inversion_v1 g hmi]
  have ha := cpow_mul_density_integrable_v1 g hm
  have hb := (cpow_mul_density_integrable_v1 g hmi).const_mul (1 / (m : ℂ))
  have hsplit : (∫ t : ℝ, ((m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        criticalDensityV1 g t + (1 / (m : ℂ)) *
          (((m⁻¹ : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * criticalDensityV1 g t))) =
      (∫ t : ℝ, (m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * criticalDensityV1 g t) +
        (1 / (m : ℂ)) * ∫ t : ℝ,
          ((m⁻¹ : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * criticalDensityV1 g t := by
    rw [integral_add ha hb, integral_const_mul]
  have hcongr : (∫ t : ℝ, ((2 * Real.exp (-(Real.log m) / 2) * Real.cos (t * Real.log m) : ℝ) : ℂ) *
        criticalDensityV1 g t) =
      ∫ t : ℝ, ((m : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) *
        criticalDensityV1 g t + (1 / (m : ℂ)) *
          (((m⁻¹ : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) * criticalDensityV1 g t)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← cpow_pair_cos_v1 hm t]
    ring
  rw [hcongr, hsplit]
  unfold criticalDensityV1
  ring

end AEGIS.WeilCriticalLinePrimeV1

#print axioms AEGIS.WeilCriticalLinePrimeV1.autocorrelation_mellin_critical_v1
#print axioms AEGIS.WeilCriticalLinePrimeV1.autocorrelation_critical_line_inversion_v1
#print axioms AEGIS.WeilCriticalLinePrimeV1.cpow_pair_cos_v1
#print axioms AEGIS.WeilCriticalLinePrimeV1.prime_pair_critical_cos_v1
