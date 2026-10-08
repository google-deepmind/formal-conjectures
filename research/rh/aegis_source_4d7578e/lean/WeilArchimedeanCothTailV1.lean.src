/-
AEGIS Ω — the `coth` tail of the archimedean diagonal kernel, V1.

`WeilThreeBlockAnalyticConstantsV21` closes the numeric margin of the diagonal
threshold once the archimedean diagonal kernel has been reduced to

    log (coth (1/64)) - log (4π) - γ - (1/64) * exp (1/64)

and its docstring is explicit that "no kernel identity is asserted here".
The `log (coth (1/64))` there is a tail integral: in the log coordinate
`x = exp u` the archimedean denominator `x - x⁻¹` is `2 sinh u`, and outside the
packet's log-support the autocorrelation vanishes, leaving

    ∫_{w}^{∞} du / sinh u = log (coth (w/2)).

This module proves that identity and connects it to the constant the
certificate consumes. Mathlib 0df444a3 has no `coth` and no `∫ 1 / sinh`, so
both are built here from `exp`/`log` only.

What this module does NOT do: it does not prove the archimedean diagonal lower
bound `(103/100) ‖g‖² ≤ -Re (B g g)`, it does not identify this tail with the
kernel of `WeilArchimedeanIntegrandV1` for a concrete packet, and it proves
nothing about the Weil criterion or RH. It supplies one reusable analytic
ingredient of that reduction, nothing more.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

open Set Filter MeasureTheory Real
open scoped Topology

namespace AEGIS.WeilArchimedeanCothTailV1

/-- Antiderivative of `1 / sinh` on `(0, ∞)`, written with `exp`/`log` only
(Mathlib 0df444a3 has no `coth`). -/
noncomputable def cothPrim (u : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-u)) - Real.log (1 + Real.exp (-u))

theorem exp_neg_lt_one {u : ℝ} (hu : 0 < u) : Real.exp (-u) < 1 := by
  rw [Real.exp_lt_one_iff]; linarith

theorem cothPrim_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt cothPrim (1 / Real.sinh u) u := by
  have hp : (0 : ℝ) < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := exp_neg_lt_one hu
  have h1 : (1 : ℝ) - Real.exp (-u) ≠ 0 := by linarith
  have h2 : (1 : ℝ) + Real.exp (-u) ≠ 0 := by positivity
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
    simpa using ((hasDerivAt_id u).neg).exp
  have hA : HasDerivAt (fun t : ℝ => Real.log (1 - Real.exp (-t)))
      (Real.exp (-u) / (1 - Real.exp (-u))) u := by
    simpa using (((hasDerivAt_const u (1 : ℝ)).sub he).log h1)
  have hB : HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-t)))
      (-Real.exp (-u) / (1 + Real.exp (-u))) u := by
    simpa using (((hasDerivAt_const u (1 : ℝ)).add he).log h2)
  have hinv : Real.exp u = (Real.exp (-u))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  have hgt : (1 : ℝ) < Real.exp u := by
    have := Real.add_one_le_exp u
    linarith
  have hsq : (1 : ℝ) - Real.exp (-u) ^ 2 ≠ 0 := by nlinarith
  have key :
      Real.exp (-u) / (1 - Real.exp (-u)) - -Real.exp (-u) / (1 + Real.exp (-u))
        = 1 / Real.sinh u := by
    rw [Real.sinh_eq, hinv]
    have hne : (Real.exp (-u))⁻¹ - Real.exp (-u) ≠ 0 := by
      rw [← hinv]; intro h; nlinarith
    field_simp [h1, h2, hne, hsq]
    ring
  show HasDerivAt
    (fun t : ℝ => Real.log (1 - Real.exp (-t)) - Real.log (1 + Real.exp (-t)))
    (1 / Real.sinh u) u
  rw [← key]
  exact hA.sub hB

theorem cothPrim_tendsto_atTop : Tendsto cothPrim atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hA : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-u))) atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => 1 - Real.exp (-u)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub he
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp h
  have hB : Tendsto (fun u : ℝ => Real.log (1 + Real.exp (-u))) atTop (𝓝 0) := by
    have h : Tendsto (fun u : ℝ => 1 + Real.exp (-u)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add he
    simpa [Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp h
  show Tendsto
    (fun u : ℝ => Real.log (1 - Real.exp (-u)) - Real.log (1 + Real.exp (-u)))
    atTop (𝓝 0)
  simpa using hA.sub hB

theorem sinh_pos_of_pos {u : ℝ} (hu : 0 < u) : 0 < Real.sinh u := by
  rw [Real.sinh_eq]
  have : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **The tail integral of `1 / sinh`.**  For `w > 0`,
`∫_w^∞ du / sinh u = log ((1 + e^{-w}) / (1 - e^{-w})) = log (coth (w/2))`. -/
theorem integral_one_div_sinh_Ioi {w : ℝ} (hw : 0 < w) :
    (∫ u in Ioi w, 1 / Real.sinh u)
      = Real.log ((1 + Real.exp (-w)) / (1 - Real.exp (-w))) := by
  have hderiv : ∀ u ∈ Ici w, HasDerivAt cothPrim (1 / Real.sinh u) u := fun u hu =>
    cothPrim_hasDerivAt (lt_of_lt_of_le hw hu)
  have hpos : ∀ u ∈ Ioi w, 0 ≤ 1 / Real.sinh u := by
    intro u hu
    have := sinh_pos_of_pos (lt_trans hw hu)
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos cothPrim_tendsto_atTop]
  have hlt : Real.exp (-w) < 1 := exp_neg_lt_one hw
  have h1 : (0 : ℝ) < 1 - Real.exp (-w) := by linarith
  have h2 : (0 : ℝ) < 1 + Real.exp (-w) := by positivity
  rw [Real.log_div (ne_of_gt h2) (ne_of_gt h1)]
  simp [cothPrim]

/-- `exp (1/32) < 65/63`, via the degree-3 Taylor bound.  The margin is
`65 * 147456 - 152137 * 63 = 9`, so the cubic term is genuinely needed. -/
theorem exp_one_div_32_lt : Real.exp (1 / 32) < 65 / 63 := by
  have h := Real.exp_bound (x := (1 / 32 : ℝ)) (by norm_num) (n := 3) (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at h
  norm_num at h
  rw [abs_le] at h
  linarith [h.2]

theorem exp_neg_one_div_32_gt : (63 : ℝ) / 65 < Real.exp (-(1 / 32)) := by
  have hpos : (0 : ℝ) < Real.exp (1 / 32) := Real.exp_pos _
  have hlt := exp_one_div_32_lt
  rw [Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num) hpos]
  calc Real.exp (1 / 32) < 65 / 65 * (65 / 63) := by
        rw [show (65:ℝ)/65 = 1 by norm_num, one_mul]; exact hlt
    _ = ((63 : ℝ) / 65)⁻¹ := by norm_num

/-- The coth ratio at half-width `1/64` exceeds `64 = 2 ^ 6`. -/
theorem coth_ratio_gt_64 :
    (64 : ℝ) < (1 + Real.exp (-(1 / 32))) / (1 - Real.exp (-(1 / 32))) := by
  set a := Real.exp (-(1 / 32)) with ha
  have h63 : (63 : ℝ) / 65 < a := exp_neg_one_div_32_gt
  have hlt1 : a < 1 := by
    rw [ha, Real.exp_lt_one_iff]; norm_num
  have hden : (0 : ℝ) < 1 - a := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- **Bridge to the certificate constant.**  The `1/sinh` tail at `w = 1/32`,
which equals `log (coth (1/64))`, is strictly above the `6 * log 2` that
`WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor` uses. -/
theorem six_log_two_lt_log_coth_ratio :
    6 * Real.log 2
      < Real.log ((1 + Real.exp (-(1 / 32))) / (1 - Real.exp (-(1 / 32)))) := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [← h64]
  exact Real.log_lt_log (by norm_num) coth_ratio_gt_64

/-- **Punchline.**  At the certificate's packet half-width `w = 1/32`, the
`1 / sinh` tail — that is `log (coth (1/64))` — strictly exceeds the `6 * log 2`
used by `WeilThreeBlockAnalyticConstantsV21.diagonal_constant_floor`. -/
theorem six_log_two_lt_integral_one_div_sinh_Ioi :
    6 * Real.log 2 < ∫ u in Ioi (1 / 32 : ℝ), 1 / Real.sinh u := by
  rw [integral_one_div_sinh_Ioi (by norm_num : (0:ℝ) < 1 / 32)]
  simpa using six_log_two_lt_log_coth_ratio

end AEGIS.WeilArchimedeanCothTailV1

#print axioms AEGIS.WeilArchimedeanCothTailV1.cothPrim_hasDerivAt
#print axioms AEGIS.WeilArchimedeanCothTailV1.cothPrim_tendsto_atTop
#print axioms AEGIS.WeilArchimedeanCothTailV1.integral_one_div_sinh_Ioi
#print axioms AEGIS.WeilArchimedeanCothTailV1.exp_one_div_32_lt
#print axioms AEGIS.WeilArchimedeanCothTailV1.coth_ratio_gt_64
#print axioms AEGIS.WeilArchimedeanCothTailV1.six_log_two_lt_log_coth_ratio
#print axioms AEGIS.WeilArchimedeanCothTailV1.six_log_two_lt_integral_one_div_sinh_Ioi
