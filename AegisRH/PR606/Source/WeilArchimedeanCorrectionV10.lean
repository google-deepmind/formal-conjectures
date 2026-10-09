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

import WeilFixedLineGammaAssemblyV10
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
AEGIS Ω — elementary Archimedean correction integral V10.

This file closes the last scalar correction used in the normalized gamma term:

  ∫_{1}^{∞} dx / (x (x + 1)) = log 2.

The antiderivative is log x - log (x+1), whose limit at +∞ is zero by
`Real.tendsto_log_comp_add_sub_log 1`.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter MeasureTheory
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilArchimedeanCorrectionV10

private theorem correction_antideriv_v10 (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt
      (fun y : ℝ => Real.log y - Real.log (y + 1))
      (1 / x - 1 / (x + 1)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hlogx := Real.hasDerivAt_log hx0
  have hlogx1 :
      HasDerivAt (fun y : ℝ => Real.log (y + 1)) (1 / (x + 1)) x := by
    simpa using ((hasDerivAt_id' x).add_const 1).log hx1
  exact (hlogx.sub hlogx1).congr_deriv (by simp [one_div])

private theorem correction_deriv_nonneg_v10 {x : ℝ} (hx : 1 < x) :
    0 ≤ 1 / x - 1 / (x + 1) := by
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

private theorem correction_antideriv_tendsto_zero_v10 :
    Tendsto
      (fun x : ℝ => Real.log x - Real.log (x + 1))
      atTop (𝓝 0) := by
  have h := (Real.tendsto_log_comp_add_sub_log 1).neg
  convert h using 1 <;> simp [sub_eq_add_neg]


/-- Integrability of the scalar correction, obtained from the same monotone-FTC
argument used for its exact value. -/
theorem integrableOn_one_div_mul_one_add_v10 :
    IntegrableOn
      (fun x : ℝ => 1 / (x * (x + 1)))
      (Ioi (1 : ℝ)) := by
  have hderiv :
      ∀ x ∈ Ici (1 : ℝ),
        HasDerivAt
          (fun y : ℝ => Real.log y - Real.log (y + 1))
          (1 / x - 1 / (x + 1)) x :=
    fun x hx => correction_antideriv_v10 x hx
  have hpos :
      ∀ x ∈ Ioi (1 : ℝ), 0 ≤ 1 / x - 1 / (x + 1) :=
    fun x hx => correction_deriv_nonneg_v10 hx
  have hdiff :
      IntegrableOn
        (fun x : ℝ => 1 / x - 1 / (x + 1))
        (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg'
      hderiv hpos correction_antideriv_tendsto_zero_v10
  refine IntegrableOn.congr_fun hdiff ?_ measurableSet_Ioi
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [mem_Ioi] at hx
    linarith
  have hx1 : x + 1 ≠ 0 := by
    rw [mem_Ioi] at hx
    linarith
  field_simp [hx0, hx1]
  ring

/-- Exact tail correction. -/
theorem integral_one_div_mul_one_add_v10 :
    (∫ x : ℝ in Ioi (1 : ℝ), 1 / (x * (x + 1))) =
      Real.log 2 := by
  have hbase :=
    integral_Ioi_of_hasDerivAt_of_nonneg'
      (a := (1 : ℝ))
      (g := fun x : ℝ => Real.log x - Real.log (x + 1))
      (g' := fun x : ℝ => 1 / x - 1 / (x + 1))
      (l := (0 : ℝ))
      (fun x hx => correction_antideriv_v10 x hx)
      (fun x hx => correction_deriv_nonneg_v10 hx)
      correction_antideriv_tendsto_zero_v10
  have hpoint :
      ∀ x ∈ Ioi (1 : ℝ),
        1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    intro x hx
    have hx' : (1 : ℝ) < x := hx
    have hx0 : x ≠ 0 := ne_of_gt (by linarith [hx'])
    have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith [hx'])
    field_simp [hx0, hx1]
    ring
  calc
    (∫ x : ℝ in Ioi (1 : ℝ), 1 / (x * (x + 1))) =
        ∫ x : ℝ in Ioi (1 : ℝ), (1 / x - 1 / (x + 1)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact (hpoint x hx).symm
    _ = 0 - (Real.log 1 - Real.log (1 + 1)) := hbase
    _ = Real.log 2 := by rw [Real.log_one, show (1 : ℝ) + 1 = 2 by norm_num]; ring

end AEGIS.WeilArchimedeanCorrectionV10

#print axioms AEGIS.WeilArchimedeanCorrectionV10.integral_one_div_mul_one_add_v10
