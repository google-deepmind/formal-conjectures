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

import RHCriticalLineSignV1
import RHRiemannThetaFormulaV1

/-!
# `Λ(1/2 + it)` as one real Mellin integral

`Λ(1/2 + it) = re 𝓜A(1/4 + it/2) − 1/(1/4 + t²)`, where `A = 1_{x>1}(θ − 1)` is real-valued, so
`𝓜A(conj w) = conj 𝓜A(w)` and the two Mellin terms of Riemann's formula are conjugate on the line.
AUTHORITY_EFFECT = NONE.
-/

open Complex ComplexConjugate Set MeasureTheory HurwitzZeta

namespace AEGIS.RHLambdaLineV1

open AEGIS.RHCriticalLineSignV1 AEGIS.RHRiemannThetaFormulaV1

lemma A_real (x : ℝ) : ∃ r : ℝ, A x = r := by
  by_cases h : 1 < x
  · exact ⟨_, A_apply_of_one_lt h⟩
  · exact ⟨0, by simp [A, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from h)]⟩

lemma conj_A (x : ℝ) : conj (A x) = A x := by
  obtain ⟨r, hr⟩ := A_real x; rw [hr, conj_ofReal]

lemma mellin_A_conj (w : ℂ) : mellin A (conj w) = conj (mellin A w) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hπ : ((t : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (le_of_lt ht)]; exact Real.pi_pos.ne'.symm
  simp only [smul_eq_mul, map_mul, conj_A]
  rw [show conj w - 1 = conj (w - 1) by simp, cpow_conj _ _ hπ, conj_ofReal]

lemma half_sub_line (t : ℝ) : 1 / 2 - lineAt t / 2 = conj (lineAt t / 2) := by
  rw [map_div₀, map_ofNat, conj_lineAt]; ring

lemma inv_add_inv_line (t : ℝ) :
    1 / lineAt t + 1 / (1 - lineAt t) = ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ) := by
  have h0 := lineAt_ne_zero t
  have h1 : 1 - lineAt t ≠ 0 := sub_ne_zero.mpr (lineAt_ne_one t).symm
  have hp : lineAt t * (1 - lineAt t) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [lineAt, pow_two] <;> ring
  rw [div_add_div _ _ h0 h1, one_mul, mul_one, sub_add_cancel, hp]; push_cast; ring

/-- **`Λ(1/2 + it) = re 𝓜A(1/4 + it/2) − 1/(1/4 + t²)`.** -/
theorem Xi_re_eq (t : ℝ) :
    (Xi t).re = (mellin A (lineAt t / 2)).re - 1 / (1 / 4 + t ^ 2) := by
  have H := RHRiemannThetaFormulaV1.completedRiemannZeta_eq (lineAt t)
  rw [half_sub_line, mellin_A_conj, sub_sub, inv_add_inv_line, add_conj] at H
  have e : (((2 * (mellin A (lineAt t / 2)).re : ℝ) : ℂ) / 2) = (((mellin A (lineAt t / 2)).re : ℝ) : ℂ) := by
    push_cast; ring
  rw [Xi, H, e, ← ofReal_sub, ofReal_re]

end AEGIS.RHLambdaLineV1

#print axioms AEGIS.RHLambdaLineV1.Xi_re_eq
