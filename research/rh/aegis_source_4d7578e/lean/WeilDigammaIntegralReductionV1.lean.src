/-
AEGIS Ω — the series-to-integral reduction behind Gauss's digamma integral, V1.

`WeilPairedHadamardIdentityV1.md` (lane #490) carries exactly one
`[EXTERNAL-THEOREM]` dependency: Gauss's integral representation of the
digamma function (DLMF 5.9.16),

    ψ(z) + γ = ∫_0^∞ (exp (-u) - exp (-z u)) / (1 - exp (-u)) du,   Re z > 0,

used at `z = s/2` in its Section 5.  Mathlib 0df444a3 has `digamma` (as
`logDeriv Gamma`) but not this representation — `Gamma/Digamma.lean` lists it
as an open TODO.

Gauss's formula factors into two independent halves:

  (a)  ∑_{n≥0} (1/(n+1) - 1/(z+n)) = ∫_0^∞ (exp (-u) - exp (-z u))/(1 - exp (-u)) du
  (b)  ψ(z) + γ = ∑_{n≥0} (1/(n+1) - 1/(z+n))                    [series form of ψ]

This module proves (a), unconditionally, for every `z` with `0 < z.re`, from
Mathlib's trust surface only.  Half (b) — the series representation of
`digamma` — is NOT proven here and remains the open half of the dependency.

What this module does NOT do: it does not prove Gauss's formula, it does not
touch `digamma`, it proves no part of `WeilPairedHadamardIdentityV1`, and it
proves nothing about the Weil criterion or RH.  It removes one of the two
obstructions to importing that single external theorem, and nothing more.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

open Set Filter MeasureTheory
open scoped Topology

namespace AEGIS.WeilDigammaIntegralReductionV1

/-- `n`-th summand of the digamma-type series `∑ (1/(n+1) - 1/(z+n))`. -/
noncomputable def seriesTerm (z : ℂ) (n : ℕ) : ℂ :=
  1 / ((n : ℂ) + 1) - 1 / (z + n)

/-- `n`-th summand of the geometric expansion of the Gauss integrand. -/
noncomputable def kernelTerm (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) + 1) * u) - Complex.exp (-(z + n) * u)

/-- The Gauss integrand. -/
noncomputable def gaussIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  (Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)) / (1 - Complex.exp (-(u : ℂ)))

/-! ### Step 1 — each summand is the integral of its kernel term -/

theorem integrableOn_kernelTerm (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (kernelTerm z n) (Ioi (0 : ℝ)) := by
  have h1 : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re, neg_lt_zero]
    positivity
  have h2 : (-(z + (n : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, neg_lt_zero]
    positivity
  exact (integrableOn_exp_mul_complex_Ioi h1 0).sub (integrableOn_exp_mul_complex_Ioi h2 0)

theorem integral_kernelTerm (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), kernelTerm z n u) = seriesTerm z n := by
  have h1 : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re, neg_lt_zero]
    positivity
  have h2 : (-(z + (n : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, neg_lt_zero]
    positivity
  have hne1 : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
  have hne2 : (z + (n : ℂ)) ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  simp only [kernelTerm]
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi h1 0)
      (integrableOn_exp_mul_complex_Ioi h2 0),
    integral_exp_mul_complex_Ioi h1 0, integral_exp_mul_complex_Ioi h2 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg,
    seriesTerm]

/-! ### Step 2 — a uniform majorant for the kernel terms -/

/-- Two-regime bound on `exp (-u) - exp (-z u)`: the linear factor `u` comes from
the cancellation at `u = 0`, and is what makes the majorant summable in `n`. -/
theorem norm_exp_diff_le (z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
      ≤ 2 * (1 + ‖z - 1‖) * u * Real.exp (-(min 1 z.re * u)) := by
  set C := ‖z - 1‖ with hCdef
  set m := min 1 z.re with hmdef
  have hC0 : 0 ≤ C := norm_nonneg _
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmre : m ≤ z.re := min_le_right _ _
  have hfac : Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)
      = Complex.exp (-(u : ℂ)) * (1 - Complex.exp (-(z - 1) * u)) := by
    have h : Complex.exp (-(u : ℂ)) * Complex.exp (-(z - 1) * u)
        = Complex.exp (-z * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [mul_sub, mul_one, h]
  have hnorm1 : ‖Complex.exp (-(u : ℂ))‖ = Real.exp (-u) := by
    rw [Complex.norm_exp]; simp
  have hnorm2 : ‖Complex.exp (-z * (u : ℂ))‖ = Real.exp (-(z.re * u)) := by
    rw [Complex.norm_exp]; simp
  have hexp1 : Real.exp (-u) ≤ Real.exp (-(m * u)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hexp2 : Real.exp (-(z.re * u)) ≤ Real.exp (-(m * u)) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hpos := Real.exp_pos (-(m * u))
  by_cases h : C * u ≤ 1
  · have harg : ‖-(z - 1) * (u : ℂ)‖ ≤ 1 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu.le]
      exact h
    have hb : ‖Complex.exp (-(z - 1) * (u : ℂ)) - 1‖ ≤ 2 * (C * u) := by
      have := Complex.norm_exp_sub_one_le harg
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu.le] at this
      exact this
    have hb' : ‖1 - Complex.exp (-(z - 1) * (u : ℂ))‖ ≤ 2 * (C * u) := by
      rw [norm_sub_rev]; exact hb
    calc ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
        = Real.exp (-u) * ‖1 - Complex.exp (-(z - 1) * (u : ℂ))‖ := by
          rw [hfac, norm_mul, hnorm1]
      _ ≤ Real.exp (-(m * u)) * (2 * (C * u)) := by
          apply mul_le_mul hexp1 hb' (norm_nonneg _) hpos.le
      _ ≤ 2 * (1 + C) * u * Real.exp (-(m * u)) := by nlinarith
  · push_neg at h
    have hu1 : 1 ≤ (1 + C) * u := by nlinarith
    calc ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
        ≤ ‖Complex.exp (-(u : ℂ))‖ + ‖Complex.exp (-z * (u : ℂ))‖ := norm_sub_le _ _
      _ = Real.exp (-u) + Real.exp (-(z.re * u)) := by rw [hnorm1, hnorm2]
      _ ≤ 2 * Real.exp (-(m * u)) := by linarith
      _ ≤ 2 * (1 + C) * u * Real.exp (-(m * u)) := by nlinarith

theorem norm_kernelTerm_le (z : ℂ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖kernelTerm z n u‖
      ≤ 2 * (1 + ‖z - 1‖) * u * Real.exp (-(((n : ℝ) + min 1 z.re) * u)) := by
  have hfac : kernelTerm z n u
      = Complex.exp (-(n : ℂ) * u) * (Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)) := by
    simp only [kernelTerm, mul_sub]
    congr 1
    · rw [← Complex.exp_add]; congr 1; ring
    · rw [← Complex.exp_add]; congr 1; ring
  have hnorm : ‖Complex.exp (-(n : ℂ) * (u : ℝ))‖ = Real.exp (-((n : ℝ) * u)) := by
    rw [Complex.norm_exp]; simp
  rw [hfac, norm_mul, hnorm]
  have hb := norm_exp_diff_le z hu
  have hp := Real.exp_pos (-((n : ℝ) * u))
  calc Real.exp (-((n : ℝ) * u)) * ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
      ≤ Real.exp (-((n : ℝ) * u)) * (2 * (1 + ‖z - 1‖) * u * Real.exp (-(min 1 z.re * u))) := by
        exact mul_le_mul_of_nonneg_left hb hp.le
    _ = 2 * (1 + ‖z - 1‖) * u * Real.exp (-(((n : ℝ) + min 1 z.re) * u)) := by
        rw [show -(((n : ℝ) + min 1 z.re) * u) = -((n : ℝ) * u) + -(min 1 z.re * u) by ring,
          Real.exp_add]
        ring

/-! ### Step 3 — the majorant integrates to `O(n⁻²)` -/

/-- `u * exp (-(b * u)) ≤ 1 / b` for `b > 0`: the only input is `x + 1 ≤ exp x`. -/
theorem mul_exp_neg_le (b : ℝ) (hb : 0 < b) (u : ℝ) (hu : 0 ≤ u) :
    u * Real.exp (-(b * u)) ≤ 1 / b := by
  have h1 : b * u ≤ Real.exp (b * u) := by
    have := Real.add_one_le_exp (b * u)
    linarith
  have hkey : (b * u) * Real.exp (-(b * u)) ≤ 1 := by
    have h2 : (b * u) * Real.exp (-(b * u)) ≤ Real.exp (b * u) * Real.exp (-(b * u)) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    rwa [← Real.exp_add, show b * u + -(b * u) = 0 by ring, Real.exp_zero] at h2
  rw [le_div_iff₀ hb]
  calc u * Real.exp (-(b * u)) * b = (b * u) * Real.exp (-(b * u)) := by ring
    _ ≤ 1 := hkey

theorem integral_norm_kernelTerm_le (z : ℂ) (hz : 0 < z.re) (n : ℕ) :
    (∫ u in Ioi (0 : ℝ), ‖kernelTerm z n u‖)
      ≤ 8 * (1 + ‖z - 1‖) / (((n : ℝ) + min 1 z.re) ^ 2) := by
  set C := ‖z - 1‖ with hCdef
  set m := min 1 z.re with hmdef
  have hm0 : 0 < m := lt_min one_pos hz
  set a : ℝ := (n : ℝ) + m with hadef
  have ha0 : 0 < a := by positivity
  set b : ℝ := a / 2 with hbdef
  have hb0 : 0 < b := by positivity
  set K : ℝ := 2 * (1 + C) with hKdef
  have hK0 : 0 < K := by
    have : (0 : ℝ) ≤ C := norm_nonneg _
    simp only [hKdef]; linarith
  have hmaj : IntegrableOn (fun u : ℝ => K / b * Real.exp (-b * u)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).const_mul _
  have hle : ∀ u ∈ Ioi (0 : ℝ), ‖kernelTerm z n u‖ ≤ K / b * Real.exp (-b * u) := by
    intro u hu
    rw [mem_Ioi] at hu
    have h1 : ‖kernelTerm z n u‖ ≤ K * u * Real.exp (-(a * u)) := norm_kernelTerm_le z n hu
    have hsplit : Real.exp (-(a * u)) = Real.exp (-(b * u)) * Real.exp (-(b * u)) := by
      rw [← Real.exp_add]
      congr 1
      simp only [hbdef]
      ring
    have h2 : u * Real.exp (-(b * u)) ≤ 1 / b := mul_exp_neg_le b hb0 u hu.le
    have hp := Real.exp_pos (-(b * u))
    have : K * u * Real.exp (-(a * u)) = K * (u * Real.exp (-(b * u))) * Real.exp (-(b * u)) := by
      rw [hsplit]; ring
    rw [this] at h1
    have h3 : K * (u * Real.exp (-(b * u))) ≤ K * (1 / b) :=
      mul_le_mul_of_nonneg_left h2 hK0.le
    have h4 : K * (u * Real.exp (-(b * u))) * Real.exp (-(b * u))
        ≤ K * (1 / b) * Real.exp (-(b * u)) := mul_le_mul_of_nonneg_right h3 hp.le
    calc ‖kernelTerm z n u‖ ≤ K * (u * Real.exp (-(b * u))) * Real.exp (-(b * u)) := h1
      _ ≤ K * (1 / b) * Real.exp (-(b * u)) := h4
      _ = K / b * Real.exp (-b * u) := by rw [neg_mul]; ring
  have hnn : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) ≤ ‖kernelTerm z n u‖ :=
    Filter.Eventually.of_forall (fun u => norm_nonneg _)
  have hlea : (fun u => ‖kernelTerm z n u‖)
      ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => K / b * Real.exp (-b * u) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hle)
  have hmono := integral_mono_of_nonneg hnn hmaj hlea
  have hval : (∫ u in Ioi (0 : ℝ), K / b * Real.exp (-b * u)) = K / b * (1 / b) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -b) (by linarith) 0]
    simp
  rw [hval] at hmono
  have hfin : K / b * (1 / b) = 8 * (1 + C) / (a ^ 2) := by
    field_simp [hbdef, hKdef]
    ring
  rw [hfin] at hmono
  exact hmono

theorem summable_integral_norm_kernelTerm (z : ℂ) (hz : 0 < z.re) :
    Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖kernelTerm z n u‖ := by
  set C := ‖z - 1‖ with hCdef
  set m := min 1 z.re with hmdef
  have hm0 : 0 < m := lt_min one_pos hz
  have hm1 : m ≤ 1 := min_le_left _ _
  have hC0 : (0 : ℝ) ≤ C := norm_nonneg _
  have hps : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1).2 h
    refine h2.congr fun n => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _)
    (fun n => integral_norm_kernelTerm_le z hz n) ?_
  have hbound : ∀ n : ℕ, 8 * (1 + C) / (((n : ℝ) + m) ^ 2)
      ≤ (8 * (1 + C) / m ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have h1 : m * ((n : ℝ) + 1) ≤ (n : ℝ) + m := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have h2 : (0 : ℝ) < m * ((n : ℝ) + 1) := by positivity
    have h3 : (m * ((n : ℝ) + 1)) ^ 2 ≤ ((n : ℝ) + m) ^ 2 := by nlinarith
    have h4 : (0 : ℝ) < (m * ((n : ℝ) + 1)) ^ 2 := by positivity
    have h5 : (0 : ℝ) ≤ 8 * (1 + C) := by linarith
    calc 8 * (1 + C) / (((n : ℝ) + m) ^ 2)
        ≤ 8 * (1 + C) / ((m * ((n : ℝ) + 1)) ^ 2) := by
          apply div_le_div_of_nonneg_left h5 h4 h3
      _ = (8 * (1 + C) / m ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
          field_simp
  exact Summable.of_nonneg_of_le
    (fun n => by positivity)
    hbound (hps.mul_left _)

/-! ### Step 4 — the pointwise geometric sum -/

theorem tsum_kernelTerm (z : ℂ) {u : ℝ} (hu : 0 < u) :
    ∑' n : ℕ, kernelTerm z n u = gaussIntegrand z u := by
  have hr : ‖Complex.exp (-(u : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hterm : ∀ n : ℕ, kernelTerm z n u
      = (Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)) * Complex.exp (-(u : ℂ)) ^ n := by
    intro n
    rw [← Complex.exp_nat_mul]
    simp only [kernelTerm, sub_mul]
    congr 1
    · rw [← Complex.exp_add]; congr 1; ring
    · rw [← Complex.exp_add]; congr 1; ring
  simp only [hterm, gaussIntegrand]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
  rw [div_eq_mul_inv]

/-! ### Step 5 — the reduction -/

/-- **The series-to-integral half of Gauss's digamma integral.**  For every `z`
with `0 < z.re`,

    ∑_{n≥0} (1/(n+1) - 1/(z+n)) = ∫_0^∞ (exp (-u) - exp (-z u)) / (1 - exp (-u)) du.

No axiom beyond Mathlib's standard trust surface; `digamma` does not appear. -/
theorem tsum_seriesTerm_eq_integral (z : ℂ) (hz : 0 < z.re) :
    ∑' n : ℕ, seriesTerm z n = ∫ u in Ioi (0 : ℝ), gaussIntegrand z u := by
  have key := integral_tsum_of_summable_integral_norm
    (F := fun (n : ℕ) (u : ℝ) => kernelTerm z n u)
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun n => integrableOn_kernelTerm z hz n)
    (summable_integral_norm_kernelTerm z hz)
  have hL : (∑' n : ℕ, ∫ u in Ioi (0 : ℝ), kernelTerm z n u) = ∑' n : ℕ, seriesTerm z n := by
    exact tsum_congr fun n => integral_kernelTerm z hz n
  have hR : (∫ u in Ioi (0 : ℝ), ∑' n : ℕ, kernelTerm z n u)
      = ∫ u in Ioi (0 : ℝ), gaussIntegrand z u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact tsum_kernelTerm z (mem_Ioi.1 hu)
  rw [← hL, key, hR]

end AEGIS.WeilDigammaIntegralReductionV1

#print axioms AEGIS.WeilDigammaIntegralReductionV1.integral_kernelTerm
#print axioms AEGIS.WeilDigammaIntegralReductionV1.norm_exp_diff_le
#print axioms AEGIS.WeilDigammaIntegralReductionV1.norm_kernelTerm_le
#print axioms AEGIS.WeilDigammaIntegralReductionV1.integral_norm_kernelTerm_le
#print axioms AEGIS.WeilDigammaIntegralReductionV1.summable_integral_norm_kernelTerm
#print axioms AEGIS.WeilDigammaIntegralReductionV1.tsum_kernelTerm
#print axioms AEGIS.WeilDigammaIntegralReductionV1.tsum_seriesTerm_eq_integral
