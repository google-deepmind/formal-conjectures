import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
AEGIS Ω — Epstein Weil t-form ↔ x-form identity, constant pieces (v1).

PR #693 evaluates the fixed-witness Weil quadratic in x-space:

  W = h(0)·[2ψ(1/2) + 2·log((1+e^{-L/2})/(1-e^{-L/2})) + log(5/π²)]
      + ∫₀^L (h(0) − h(u))/sinh(u/2) du − 2 Σ Λ(n) n^{-1/2} h(log n).

The passage from the t-space target form needs three analytic inputs:
  (1) the value ψ(1/2) = −γ − 2 log 2            — proved here (from Mathlib);
  (2) the kernel tail ∫_L^∞ du / sinh(u/2)
        = 2·log((1+e^{-L/2})/(1-e^{-L/2}))        — proved here;
  (3) Gauss' integral for Re ψ(1/2+it) − ψ(1/2)  — OPEN (Mathlib TODO in
      `Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean`).

Nothing here proves RH or the Weil positivity criterion.
-/

open Real MeasureTheory Filter Set Topology

noncomputable section

/-- (1) The digamma constant at 1/2, as used in the x-space constant. -/
theorem epsteinWeil_digamma_one_half_re_v1 :
    (Complex.digamma (1 / 2)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  rw [Complex.digamma_one_half]
  simp [Complex.log_re]

/-- Antiderivative of `1 / sinh (u/2)` vanishing at `+∞`. -/
def sinhHalfTailPrimitiveV1 (u : ℝ) : ℝ :=
  -2 * (Real.log (1 + Real.exp (-u / 2)) - Real.log (1 - Real.exp (-u / 2)))

theorem sinhHalfTailPrimitive_hasDerivAt_v1 {u : ℝ} (hu : 0 < u) :
    HasDerivAt sinhHalfTailPrimitiveV1 (1 / Real.sinh (u / 2)) u := by
  set q := Real.exp (-u / 2) with hq_def
  have hq : HasDerivAt (fun x : ℝ => Real.exp (-x / 2)) (q * (-1 / 2)) u := by
    have h1 : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) u := by
      simpa using ((hasDerivAt_id u).neg).div_const 2
    exact (Real.hasDerivAt_exp (-u / 2)).comp u h1
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt : q < 1 := by
    have h := Real.exp_lt_exp.mpr (show -u / 2 < 0 by linarith)
    rwa [Real.exp_zero, ← hq_def] at h
  have h1p : (1 + q) ≠ 0 := by linarith
  have h1m : (1 - q) ≠ 0 := by linarith
  have hp : HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp (-x / 2)))
      ((q * (-1 / 2)) / (1 + q)) u :=
    ((hq.const_add 1).log h1p)
  have hm : HasDerivAt (fun x : ℝ => Real.log (1 - Real.exp (-x / 2)))
      ((-(q * (-1 / 2))) / (1 - q)) u :=
    ((hq.const_sub 1).log h1m)
  have h : HasDerivAt sinhHalfTailPrimitiveV1
      (-2 * ((q * (-1 / 2)) / (1 + q) - (-(q * (-1 / 2))) / (1 - q))) u :=
    ((hp.sub hm).const_mul (-2 : ℝ))
  convert h using 1
  have he : Real.exp (u / 2) * q = 1 := by
    rw [hq_def, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hsinh : Real.sinh (u / 2) = (Real.exp (u / 2) - q) / 2 := by
    rw [Real.sinh_eq, hq_def]; ring_nf
  have hs_ne : Real.exp (u / 2) - q ≠ 0 := by
    have : q < Real.exp (u / 2) := by
      rw [hq_def]; exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  rw [hsinh]
  field_simp
  linear_combination (-2 : ℝ) * he

theorem sinhHalfTailPrimitive_tendsto_v1 :
    Tendsto sinhHalfTailPrimitiveV1 atTop (𝓝 0) := by
  have hq : Tendsto (fun u : ℝ => Real.exp (-u / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun u : ℝ => u / 2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp this
    refine h.congr (fun u => ?_)
    simp [Function.comp, neg_div]
  have hφ : ContinuousAt
      (fun x : ℝ => -2 * (Real.log (1 + x) - Real.log (1 - x))) 0 := by
    refine ContinuousAt.mul continuousAt_const (ContinuousAt.sub ?_ ?_)
    · exact (continuousAt_const.add continuousAt_id).log (by norm_num)
    · exact (continuousAt_const.sub continuousAt_id).log (by norm_num)
  have h := hφ.tendsto.comp hq
  have h0 : (-2 * (Real.log (1 + 0) - Real.log (1 - 0)) : ℝ) = 0 := by simp
  rw [h0] at h
  exact h

/-- (2) The kernel tail beyond the support length `L`:
    `∫_{(L,∞)} du / sinh(u/2) = 2·(log(1+e^{-L/2}) − log(1−e^{-L/2}))`. -/
theorem sinhHalf_tail_integral_v1 {L : ℝ} (hL : 0 < L) :
    ∫ u in Ioi L, 1 / Real.sinh (u / 2)
      = 2 * (Real.log (1 + Real.exp (-L / 2)) - Real.log (1 - Real.exp (-L / 2))) := by
  have hderiv : ∀ x ∈ Ici L,
      HasDerivAt sinhHalfTailPrimitiveV1 (1 / Real.sinh (x / 2)) x :=
    fun x hx => sinhHalfTailPrimitive_hasDerivAt_v1 (lt_of_lt_of_le hL hx)
  have hpos : ∀ x ∈ Ioi L, 0 ≤ 1 / Real.sinh (x / 2) := by
    intro x hx
    have : 0 < Real.sinh (x / 2) :=
      Real.sinh_pos_iff.mpr (by have := lt_trans hL hx; linarith)
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos sinhHalfTailPrimitive_tendsto_v1]
  simp [sinhHalfTailPrimitiveV1]

end

#print axioms epsteinWeil_digamma_one_half_re_v1
#print axioms sinhHalf_tail_integral_v1
