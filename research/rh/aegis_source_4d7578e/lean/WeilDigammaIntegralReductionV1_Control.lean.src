/-
AEGIS Ω — adversarial controls for `WeilDigammaIntegralReductionV1`.

`tsum_seriesTerm_eq_integral` is an equality between two quantities that a
mis-stated definition could render simultaneously `0`, or simultaneously
undefined-and-totalised-to-`0`.  These controls rule that out by evaluating both
sides independently at `z = 2`, where the answer is known by hand:

  * the integrand collapses, `(e^{-u} - e^{-2u}) / (1 - e^{-u}) = e^{-u}`, so the
    right-hand side is `∫_0^∞ e^{-u} du = 1`;
  * the series telescopes, `∑_{n≥0} (1/(n+1) - 1/(n+2)) = 1`.

Both are proved here WITHOUT using `tsum_seriesTerm_eq_integral`.  Their
agreement at `1` is therefore an independent check of the main theorem, and the
value `1` is nonzero, so neither side is vacuous.  (`ψ(2) + γ = 1` is the
classical value, consistent with the half of Gauss's formula this module does
not prove.)
-/
import WeilDigammaIntegralReductionV1

open Set Filter MeasureTheory
open scoped Topology
open AEGIS.WeilDigammaIntegralReductionV1

namespace AEGIS.WeilDigammaIntegralReductionV1Control

/-! ### Right-hand side at `z = 2` -/

theorem gaussIntegrand_two {u : ℝ} (hu : 0 < u) :
    gaussIntegrand 2 u = Complex.exp (-(u : ℂ)) := by
  have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hne : (1 : ℂ) - Complex.exp (-(u : ℂ)) ≠ 0 := by
    intro h
    have h' : Complex.exp (-(u : ℂ)) = 1 := by linear_combination -h
    have hn : ‖Complex.exp (-(u : ℂ))‖ = Real.exp (-u) := by rw [Complex.norm_exp]; simp
    rw [h'] at hn
    simp at hn
    linarith
  have h2 : Complex.exp (-(2 : ℂ) * u) = Complex.exp (-(u : ℂ)) * Complex.exp (-(u : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [gaussIntegrand, h2,
    show Complex.exp (-(u : ℂ)) - Complex.exp (-(u : ℂ)) * Complex.exp (-(u : ℂ))
      = Complex.exp (-(u : ℂ)) * (1 - Complex.exp (-(u : ℂ))) by ring,
    mul_div_assoc, div_self hne, mul_one]

theorem integral_gaussIntegrand_two :
    (∫ u in Ioi (0 : ℝ), gaussIntegrand 2 u) = 1 := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun u hu => gaussIntegrand_two (mem_Ioi.1 hu))]
  have hrw : ∀ u : ℝ, Complex.exp (-(u : ℂ)) = Complex.exp ((-1 : ℂ) * u) := by
    intro u; congr 1; ring
  simp_rw [hrw]
  rw [integral_exp_mul_complex_Ioi (a := (-1 : ℂ)) (by norm_num) 0]
  simp

/-! ### Left-hand side at `z = 2` -/

theorem seriesTerm_two_split (n : ℕ) :
    seriesTerm 2 n = 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + 2) := by
  simp only [seriesTerm]
  rw [show (2 : ℂ) + (n : ℂ) = (n : ℂ) + 2 by ring]

theorem natCast_add_ne_zero (n : ℕ) (c : ℝ) (hc : 0 < c) : ((n : ℂ) + (c : ℂ)) ≠ 0 := by
  have h : ((n : ℂ) + (c : ℂ)) = (((n : ℝ) + c : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  exact Complex.ofReal_ne_zero.2 (by positivity)

theorem seriesTerm_two_eq (n : ℕ) :
    seriesTerm 2 n = (((((n : ℝ) + 1) * ((n : ℝ) + 2))⁻¹ : ℝ) : ℂ) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by
    simpa using natCast_add_ne_zero n 1 one_pos
  have h2 : ((n : ℂ) + 2) ≠ 0 := by
    simpa using natCast_add_ne_zero n 2 two_pos
  have hcast : (((((n : ℝ) + 1) * ((n : ℝ) + 2))⁻¹ : ℝ) : ℂ)
      = (((n : ℂ) + 1) * ((n : ℂ) + 2))⁻¹ := by push_cast; ring
  rw [seriesTerm_two_split, hcast, div_sub_div _ _ h1 h2,
    show (1 : ℂ) * ((n : ℂ) + 2) - ((n : ℂ) + 1) * 1 = 1 by ring, one_div]

theorem summable_seriesTerm_two : Summable (seriesTerm 2) := by
  have hps : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    ring
  refine hps.of_norm_bounded fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [seriesTerm_two_eq, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  gcongr
  nlinarith

theorem sum_range_seriesTerm_two (n : ℕ) :
    ∑ i ∈ Finset.range n, seriesTerm 2 i = 1 - 1 / ((n : ℂ) + 1) := by
  induction n with
  | zero => simp [seriesTerm]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, seriesTerm_two_split]
    push_cast
    ring

/-- The series side, telescoped — proved without the main theorem. -/
theorem hasSum_seriesTerm_two : HasSum (seriesTerm 2) 1 := by
  have h1 := summable_seriesTerm_two.hasSum
  have h2 := h1.tendsto_sum_nat
  have h3 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, seriesTerm 2 i) atTop (𝓝 1) := by
    simp only [sum_range_seriesTerm_two]
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℕ))).sub hz
  have heq : ∑' n : ℕ, seriesTerm 2 n = 1 := tendsto_nhds_unique h2 h3
  rwa [heq] at h1

/-! ### The controls -/

/-- CONTROL 1 (non-vacuity). Both sides of the reduction are the nonzero
value `1` at `z = 2`, each computed without reference to the other. -/
theorem control_nonvacuous :
    (∑' n : ℕ, seriesTerm 2 n) = 1 ∧ (∫ u in Ioi (0 : ℝ), gaussIntegrand 2 u) = 1 :=
  ⟨hasSum_seriesTerm_two.tsum_eq, integral_gaussIntegrand_two⟩

/-- CONTROL 2 (the hypothesis is load-bearing). At `z = 0` the `n = 0` summand
divides by zero, and Lean's totalised division silently returns `1` rather than
diverging.  `0 < z.re` in the main theorem is therefore not decoration: without
it the left-hand side is a junk value, not the classical series. -/
theorem control_hypothesis_load_bearing : seriesTerm 0 0 = 1 := by
  simp [seriesTerm]

/-- CONTROL 3 (the integrand is not the zero function, so the right-hand side is
not an "integral of nothing"). -/
theorem control_integrand_ne_zero {u : ℝ} (hu : 0 < u) : gaussIntegrand 2 u ≠ 0 := by
  rw [gaussIntegrand_two hu]
  exact Complex.exp_ne_zero _

end AEGIS.WeilDigammaIntegralReductionV1Control

#print axioms AEGIS.WeilDigammaIntegralReductionV1Control.integral_gaussIntegrand_two
#print axioms AEGIS.WeilDigammaIntegralReductionV1Control.hasSum_seriesTerm_two
#print axioms AEGIS.WeilDigammaIntegralReductionV1Control.control_nonvacuous
#print axioms AEGIS.WeilDigammaIntegralReductionV1Control.control_hypothesis_load_bearing
#print axioms AEGIS.WeilDigammaIntegralReductionV1Control.control_integrand_ne_zero
