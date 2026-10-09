import WeilCriterionCompactSmoothV1
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

/-!
AEGIS Ω — autocorrelation involution and reality of the arithmetic expression.

The change of variables uses the positive-half-line Lebesgue measure, including
its scaling factor. Reality does not supply the remaining sign inequality.
The generic reality theorem also holds for Lean's totalized sums/integrals;
it must not be used as evidence that those expressions converge.

EXPLICIT_FORMULA_OPEN
ARITHMETIC_NEGATIVITY_OPEN
RH_EQUIVALENCE_OPEN
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

/-- The reciprocal identity includes the Jacobian `x` for the repository's
Lebesgue-measure autocorrelation (which does not use `dy / y`). -/
theorem weil_autocorrelation_reciprocal_v1 (g : WeilCompactSmoothGV1)
    {x : ℝ} (hx : 0 < x) :
    WeilAutocorrelationV1 g x⁻¹ =
      (x : ℂ) * conj (WeilAutocorrelationV1 g x) := by
  have hchange := integral_comp_mul_left_Ioi'
    (fun y : ℝ => g.1 (x⁻¹ * y) * conj (g.1 y)) 0 hx
  simp only [mul_zero, inv_mul_cancel_left₀ hx.ne'] at hchange
  have hconj :
      (∫ y in Ioi (0 : ℝ), g.1 y * conj (g.1 (x * y))) =
        conj (∫ y in Ioi (0 : ℝ), g.1 (x * y) * conj (g.1 y)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [mul_comm]
  simpa only [WeilAutocorrelationV1, Complex.star_def, hconj,
    Complex.real_smul] using hchange.symm

/-- At the identity, the autocorrelation is real. -/
theorem weil_autocorrelation_one_real_v1 (g : WeilCompactSmoothGV1) :
    (WeilAutocorrelationV1 g 1).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa using (weil_autocorrelation_reciprocal_v1 g (x := 1) zero_lt_one).symm

private theorem reflected_term_eq_conj_v1 (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (f x))
    {x : ℝ} (hx : 0 < x) :
    (1 / (x : ℂ)) * f x⁻¹ = conj (f x) := by
  rw [hf x hx]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp [div_eq_mul_inv, ← mul_assoc, hxC]

/-- Positive-integer prime terms are fixed by conjugation under the exact
reciprocal involution; no sign is inferred. -/
theorem weil_prime_term_conj_of_reciprocal_v1 (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (f x)) (n : ℕ) :
    conj (WeilPrimeTermV1 f n) = WeilPrimeTermV1 f n := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have href : (1 / ((n + 1 : ℕ) : ℂ)) * f (((n + 1 : ℕ) : ℝ)⁻¹) =
      conj (f ((n + 1 : ℕ) : ℝ)) := by
    simpa only [Complex.ofReal_natCast] using reflected_term_eq_conj_v1 f hf hn
  simp only [WeilPrimeTermV1]
  rw [href]
  simp [add_comm]

/-- The archimedean integrand is real on its integration domain. -/
theorem weil_archimedean_integrand_conj_of_reciprocal_v1 (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (f x))
    {x : ℝ} (hx : 1 < x) :
    conj (WeilArchimedeanIntegrandV1 f x) = WeilArchimedeanIntegrandV1 f x := by
  have h1 : conj (f 1) = f 1 := by simpa using (hf 1 zero_lt_one).symm
  unfold WeilArchimedeanIntegrandV1
  rw [reflected_term_eq_conj_v1 f hf (lt_trans zero_lt_one hx)]
  simp [h1, add_comm, Complex.conj_ofNat]

/-- Reality is an algebraic consequence of the reciprocal identity. This does
not discharge the separately defined convergence obligations. -/
theorem weil_explicit_right_side_real_of_reciprocal_v1 (f : ℝ → ℂ)
    (hf : ∀ x : ℝ, 0 < x → f x⁻¹ = (x : ℂ) * conj (f x)) :
    (WeilExplicitRightSideV1 f).im = 0 := by
  have hp : conj (WeilPrimeSumV1 f) = WeilPrimeSumV1 f := by
    change star (∑' n : ℕ, WeilPrimeTermV1 f n) = ∑' n : ℕ, WeilPrimeTermV1 f n
    rw [tsum_star]
    apply tsum_congr
    intro n
    exact weil_prime_term_conj_of_reciprocal_v1 f hf n
  have ha : conj (WeilArchimedeanIntegralV1 f) = WeilArchimedeanIntegralV1 f := by
    unfold WeilArchimedeanIntegralV1
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact weil_archimedean_integrand_conj_of_reciprocal_v1 f hf hx
  have h1 : conj (f 1) = f 1 := by simpa using (hf 1 zero_lt_one).symm
  apply Complex.conj_eq_iff_im.mp
  simp only [WeilExplicitRightSideV1, map_add, map_mul, hp, ha, h1,
    WeilArchimedeanConstantV1, Complex.conj_ofReal]

/-- The reality conjunct of the existing negativity candidate follows without
the explicit formula, zero localization, or a sign assumption. -/
theorem weil_autocorrelation_explicit_right_side_real_v1 (g : WeilCompactSmoothGV1) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).im = 0 := by
  apply weil_explicit_right_side_real_of_reciprocal_v1
  intro x hx
  exact weil_autocorrelation_reciprocal_v1 g hx

/-- The existing negativity candidate reduces to its real inequality. The
convergence premise is retained verbatim, rather than silently removed. -/
theorem weil_compact_smooth_negativity_iff_real_inequality_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
        WeilExplicitRightSideConvergentV1 (WeilAutocorrelationV1 g) →
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
  constructor
  · intro h g hm hc
    exact (h g hm hc).2
  · intro h g hm hc
    exact ⟨weil_autocorrelation_explicit_right_side_real_v1 g, h g hm hc⟩

#print axioms weil_autocorrelation_reciprocal_v1
#print axioms weil_autocorrelation_one_real_v1
#print axioms weil_prime_term_conj_of_reciprocal_v1
#print axioms weil_archimedean_integrand_conj_of_reciprocal_v1
#print axioms weil_explicit_right_side_real_of_reciprocal_v1
#print axioms weil_autocorrelation_explicit_right_side_real_v1
#print axioms weil_compact_smooth_negativity_iff_real_inequality_v1
