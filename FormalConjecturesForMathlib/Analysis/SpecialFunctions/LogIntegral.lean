/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cauchy Principal-Value Logarithmic Integral

This file defines `Real.logIntegralTwo` ($\operatorname{li}(2)$) and `Real.logIntegral`
($\operatorname{li}(x) = \operatorname{li}(2) + \int_2^x \frac{dt}{\log t}$) and establishes basic
positivity, integrability, and monotonicity properties.
-/

@[expose] public section

namespace Real

/-- Cauchy principal value
$\operatorname{li}(2) = \int_0^1 \left(\frac{1}{\log(1 + u)} + \frac{1}{\log(1 - u)}\right) du
\approx 1.04516378$. -/
noncomputable def logIntegralTwo : ℝ :=
  ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u))

/-- Principal-value logarithmic integral
$\operatorname{li}(x) = \operatorname{li}(2) + \int_2^x \frac{dt}{\log t}$ for $x > 1$ (for
$x \le 1$, the non-integrable interval integral across $t = 1$ vanishes in Mathlib). -/
noncomputable def logIntegral (x : ℝ) : ℝ :=
  logIntegralTwo + ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- On $(0, 1)$, the symmetrized Cauchy principal-value integrand defining `logIntegralTwo` is
strictly positive. -/
theorem logIntegralTwo_integrand_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < 1 / Real.log (1 + u) + 1 / Real.log (1 - u) := by
  have hpos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hneg : Real.log (1 - u) < 0 := Real.log_neg (by linarith) (by linarith)
  have hsum : Real.log (1 - u) + Real.log (1 + u) < 0 := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_neg (by nlinarith) (by nlinarith)
  rw [div_add_div _ _ hpos.ne' hneg.ne]
  exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hpos hneg)

/-- On $(0, 1)$, the symmetrized Cauchy principal-value integrand defining `logIntegralTwo` is
bounded above by $2$. -/
theorem logIntegralTwo_integrand_le_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 / Real.log (1 + u) + 1 / Real.log (1 - u) ≤ 2 := by
  have h1pu : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have hpos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
  have hneg : 0 < -Real.log (1 - u) := neg_pos.mpr (Real.log_neg h1mu (by linarith))
  have hb1 : 1 / Real.log (1 + u) ≤ (1 + u) / u := by
    rw [div_le_div_iff₀ hpos hu0]
    have := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos h1pu) h1pu.le
    have : (1 - (1 + u)⁻¹) * (1 + u) = u := by field_simp [h1pu.ne']; ring
    linarith
  have hb2 : (1 - u) / u ≤ 1 / (-Real.log (1 - u)) := by
    rw [div_le_div_iff₀ hu0 hneg]
    have := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos h1mu) h1mu.le
    have : (1 - (1 - u)⁻¹) * (1 - u) = -u := by field_simp [h1mu.ne']; ring
    nlinarith
  have hsum2 : (1 + u) / u - (1 - u) / u = 2 := by field_simp [hu0.ne']; ring
  have hrew : 1 / (-Real.log (1 - u)) = -(1 / Real.log (1 - u)) := div_neg 1
  linarith

/-- The symmetrized integrand defining `logIntegralTwo` is Bochner-integrable on $(0, 1)$. -/
theorem logIntegralTwo_integrand_integrableOn :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => 1 / Real.log (1 + u) + 1 / Real.log (1 - u)) (Set.Ioo 0 1) := by
  have hcont : ContinuousOn (fun u : ℝ => 1 / Real.log (1 + u) + 1 / Real.log (1 - u))
      (Set.Ioo 0 1) := fun u ⟨hu0, hu1⟩ => by
    have h1 : ContinuousAt (fun x : ℝ => Real.log (1 + x)) u :=
      (Real.continuousAt_log (by linarith)).comp (continuous_const.add continuous_id).continuousAt
    have h2 : ContinuousAt (fun x : ℝ => Real.log (1 - x)) u :=
      (Real.continuousAt_log (by linarith)).comp (continuous_const.sub continuous_id).continuousAt
    exact ((continuousAt_const.div h1 (Real.log_pos (by linarith)).ne').add
      (continuousAt_const.div h2
        (Real.log_neg (by linarith) (by linarith)).ne)).continuousWithinAt
  refine MeasureTheory.Integrable.mono'
    (MeasureTheory.integrableOn_const (hs := by simp) (hC := by simp) (C := (2 : ℝ)))
    (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u ⟨hu0, hu1⟩
  rw [Real.norm_eq_abs, abs_of_pos (logIntegralTwo_integrand_pos hu0 hu1)]
  exact logIntegralTwo_integrand_le_two hu0 hu1

@[simp]
theorem logIntegral_two : logIntegral 2 = logIntegralTwo := by
  simp [logIntegral]

/-- `logIntegral 2` is strictly positive. -/
theorem logIntegral_two_pos : 0 < logIntegral 2 := by
  rw [logIntegral_two, logIntegralTwo]
  set f : ℝ → ℝ := fun u => 1 / Real.log (1 + u) + 1 / Real.log (1 - u)
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u ⟨hu0, hu1⟩
    exact (logIntegralTwo_integrand_pos hu0 hu1).le
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hae
    logIntegralTwo_integrand_integrableOn]
  have hsupp : Function.support f ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 :=
    Set.inter_eq_right.mpr fun u ⟨hu0, hu1⟩ => (logIntegralTwo_integrand_pos hu0 hu1).ne'
  simp [hsupp, Real.volume_Ioo]

/-- Offset identity $\operatorname{li}(x) - \operatorname{li}(2) = \int_2^x \frac{dt}{\log t}$. -/
theorem logIntegral_sub_logIntegralTwo (x : ℝ) :
    logIntegral x - logIntegralTwo = ∫ t in (2 : ℝ)..x, 1 / Real.log t := by
  simp [logIntegral]

/-- Monotonicity bound $\operatorname{li}(2) \le \operatorname{li}(x)$ for $x \ge 2$. -/
theorem logIntegralTwo_le_logIntegral {x : ℝ} (hx : 2 ≤ x) :
    logIntegralTwo ≤ logIntegral x := by
  unfold logIntegral
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t :=
    intervalIntegral.integral_nonneg hx fun t ht => by
      have ht1 : (1 : ℝ) ≤ t := by linarith [(Set.mem_Icc.mp ht).1]
      exact div_nonneg zero_le_one (Real.log_nonneg ht1)
  linarith

end Real
