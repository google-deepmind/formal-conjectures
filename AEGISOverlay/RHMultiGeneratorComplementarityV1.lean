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

import FormalConjectures.Millennium.RHSnowflakeLog23
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Complementary sinc symbols at irrationally related scales

An irrational scale ratio prevents two sinc symbols from sharing a real zero.
Positive integer powers and the positive real moment multiplier preserve this
property. The resulting two symbols admit an explicit continuous spectral
Bézout identity.

The conclusions concern these explicit real-frequency symbols. They do not
assert that finite-order splines are smooth Weil packets, or that the
translation span is dense in a topology controlling compact support and Mellin
evaluation. No positivity of the Weil form is assumed or concluded.
-/

set_option autoImplicit false

noncomputable section

namespace AEGIS.RHMultiGeneratorComplementarityV1

/-- Sinc zeros at two scales force a rational ratio of the scales. -/
theorem sinc_no_common_zero_of_irrational {a b : ℝ}
    (hirr : Irrational (a / b)) (t : ℝ) :
    ¬ (Real.sinc (a * t) = 0 ∧ Real.sinc (b * t) = 0) := by
  rintro ⟨ha, hb⟩
  have hat : a * t ≠ 0 := by
    intro h
    simp [h] at ha
  have hbt : b * t ≠ 0 := by
    intro h
    simp [h] at hb
  have hb0 : b ≠ 0 := fun h => hbt (by simp [h])
  have ht0 : t ≠ 0 := fun h => hbt (by simp [h])
  have hsinA : Real.sin (a * t) = 0 := by
    rw [Real.sinc_of_ne_zero hat] at ha
    exact (div_eq_zero_iff.mp ha).resolve_right hat
  have hsinB : Real.sin (b * t) = 0 := by
    rw [Real.sinc_of_ne_zero hbt] at hb
    exact (div_eq_zero_iff.mp hb).resolve_right hbt
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsinA
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsinB
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h
    apply hbt
    simpa [h] using hn.symm
  have hprod : (a * (n : ℝ) - (m : ℝ) * b) * t = 0 := by
    nlinarith [congrArg (fun x : ℝ => (n : ℝ) * x) hm,
      congrArg (fun x : ℝ => (m : ℝ) * x) hn]
  have hcross : a * (n : ℝ) = (m : ℝ) * b :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right ht0)
  apply hirr
  refine ⟨(m : ℚ) / (n : ℚ), ?_⟩
  push_cast
  exact (div_eq_div_iff hn0 hb0).2 hcross.symm

/-- The log-2 and log-3 sinc symbols have no common real zero. -/
theorem log23_sinc_no_common_zero (t : ℝ) :
    ¬ (Real.sinc (Real.log 2 * t) = 0 ∧
      Real.sinc (Real.log 3 * t) = 0) :=
  sinc_no_common_zero_of_irrational
    RHSnowflakeLog23.irrational_log_two_div_log_three t

/-- Explicit real symbol with the angular-frequency moment multiplier.
The finite power is a spline symbol, not a definition of a smooth Weil packet. -/
def momentSplineSymbol (order : ℕ) (scale t : ℝ) : ℝ :=
  (t ^ 2 + 1 / 4) * Real.sinc (scale * t) ^ order

/-- The moment multiplier introduces no real zero. -/
theorem momentSplineSymbol_eq_zero_iff {order : ℕ} (horder : order ≠ 0)
    (scale t : ℝ) :
    momentSplineSymbol order scale t = 0 ↔ Real.sinc (scale * t) = 0 := by
  have hmult : t ^ 2 + 1 / 4 ≠ 0 := by nlinarith [sq_nonneg t]
  simp only [momentSplineSymbol, mul_eq_zero, hmult, false_or]
  exact pow_eq_zero_iff horder

/-- Complementarity holds at every positive spline order, including order 19. -/
theorem log23_momentSpline_no_common_zero {order : ℕ} (horder : order ≠ 0)
    (t : ℝ) :
    ¬ (momentSplineSymbol order (Real.log 2) t = 0 ∧
      momentSplineSymbol order (Real.log 3) t = 0) := by
  simpa only [momentSplineSymbol_eq_zero_iff horder] using log23_sinc_no_common_zero t

/-- Each finite-order moment spline symbol is continuous. -/
theorem continuous_momentSplineSymbol (order : ℕ) (scale : ℝ) :
    Continuous (momentSplineSymbol order scale) := by
  unfold momentSplineSymbol
  exact ((continuous_id.pow 2).add continuous_const).mul
    ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow order)

/-- A complementary pair has a strictly positive squared-symbol denominator. -/
theorem log23_spectral_denominator_pos {order : ℕ} (horder : order ≠ 0) (t : ℝ) :
    0 < momentSplineSymbol order (Real.log 2) t ^ 2 +
      momentSplineSymbol order (Real.log 3) t ^ 2 := by
  have h := log23_momentSpline_no_common_zero horder t
  have hA := sq_nonneg (momentSplineSymbol order (Real.log 2) t)
  have hB := sq_nonneg (momentSplineSymbol order (Real.log 3) t)
  by_contra! hnot
  have hAz : momentSplineSymbol order (Real.log 2) t = 0 := by nlinarith
  have hBz : momentSplineSymbol order (Real.log 3) t = 0 := by nlinarith
  exact h ⟨hAz, hBz⟩

/-- Continuous real multipliers reconstruct the constant symbol exactly.
This is a spectral identity, not a compact-support approximation theorem. -/
theorem log23_continuous_spectral_bezout {order : ℕ} (horder : order ≠ 0) :
    ∃ A B : ℝ → ℝ, Continuous A ∧ Continuous B ∧
      ∀ t : ℝ, A t * momentSplineSymbol order (Real.log 2) t +
        B t * momentSplineSymbol order (Real.log 3) t = 1 := by
  let F := momentSplineSymbol order (Real.log 2)
  let G := momentSplineSymbol order (Real.log 3)
  have hF : Continuous F := continuous_momentSplineSymbol order _
  have hG : Continuous G := continuous_momentSplineSymbol order _
  have hden : Continuous (fun t => F t ^ 2 + G t ^ 2) :=
    (hF.pow 2).add (hG.pow 2)
  have hne : ∀ t, F t ^ 2 + G t ^ 2 ≠ 0 :=
    fun t => ne_of_gt (log23_spectral_denominator_pos horder t)
  refine ⟨fun t => F t / (F t ^ 2 + G t ^ 2),
    fun t => G t / (F t ^ 2 + G t ^ 2),
    hF.div hden hne, hG.div hden hne, ?_⟩
  intro t
  field_simp [hne t]
  ring

/-- Order 19 is one instance of the all-orders complementarity theorem. -/
theorem order19_log23_continuous_spectral_bezout :
    ∃ A B : ℝ → ℝ, Continuous A ∧ Continuous B ∧
      ∀ t : ℝ, A t * momentSplineSymbol 19 (Real.log 2) t +
        B t * momentSplineSymbol 19 (Real.log 3) t = 1 :=
  log23_continuous_spectral_bezout (by norm_num)

#print axioms AEGIS.RHMultiGeneratorComplementarityV1.sinc_no_common_zero_of_irrational
#print axioms AEGIS.RHMultiGeneratorComplementarityV1.log23_momentSpline_no_common_zero
#print axioms AEGIS.RHMultiGeneratorComplementarityV1.order19_log23_continuous_spectral_bezout

end AEGIS.RHMultiGeneratorComplementarityV1
