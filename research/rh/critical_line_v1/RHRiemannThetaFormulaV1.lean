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

import Mathlib

/-!
# Riemann's theta formula for `Λ`

With `θ(x) = Σ_{n ∈ ℤ} e^{-π n² x}` (`evenKernel 0`) and `A = 1_{x > 1}·(θ(x) − 1)`,

  `Λ(s) = (𝓜A(s/2) + 𝓜A(1/2 − s/2)) / 2 − 1/s − 1/(1 − s)`.

Mathlib defines `Λ₀(w) = 𝓜 f_modif (w)` with `f_modif` piecewise on `(0, 1)` and `(1, ∞)`; the
`(0, 1)` piece is `x^{-1/2}·A(1/x)` by the theta functional equation, and `x ↦ 1/x` turns its Mellin
transform into `𝓜A(1/2 − w)`.  `A` decays like `e^{-π x}`, so this is the formula used to evaluate
`Λ(1/2 + it)` numerically.  AUTHORITY_EFFECT = NONE.
-/

open Complex Set MeasureTheory HurwitzZeta

namespace AEGIS.RHRiemannThetaFormulaV1

/-- The FE-pair of `ζ`. -/
noncomputable abbrev P : WeakFEPair ℂ := hurwitzEvenFEPair (0 : UnitAddCircle)

/-- `(θ(x) − 1)` on `x > 1`, zero elsewhere. -/
noncomputable def A : ℝ → ℂ := (Ioi (1 : ℝ)).indicator P.f_modif

/-- The `(0, 1)` piece of `f_modif`. -/
noncomputable def B : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator P.f_modif

lemma f_modif_eq (x : ℝ) : P.f_modif x = A x + B x := by
  by_cases h1 : x ∈ Ioi (1 : ℝ) <;> by_cases h2 : x ∈ Ioo (0 : ℝ) 1
  · exact (lt_irrefl _ (lt_trans h1 h2.2)).elim
  · simp [A, B, h1, h2]
  · simp [A, B, h1, h2]
  · simp [A, B, h1, h2, WeakFEPair.f_modif]

lemma A_apply_of_one_lt {x : ℝ} (hx : 1 < x) : A x = ((evenKernel 0 x - 1 : ℝ) : ℂ) := by
  have h2 : x ∉ Ioo (0 : ℝ) 1 := fun h => lt_irrefl _ (lt_trans hx h.2)
  simp [A, WeakFEPair.f_modif, hx, h2, hurwitzEvenFEPair]

lemma mellinConvergent_f_modif (w : ℂ) : MellinConvergent P.f_modif w :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin w).1

lemma mellinConvergent_indicator {S : Set ℝ} (hS : MeasurableSet S) (w : ℂ) :
    MellinConvergent (S.indicator P.f_modif) w := by
  have h := (mellinConvergent_f_modif w).indicator hS
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  by_cases ht : t ∈ S <;> simp [ht]

/-- `B x = x^{-1/2} A(1/x)` for `x > 0` (theta functional equation). -/
lemma B_eq (x : ℝ) (hx : 0 < x) : B x = (x : ℂ) ^ (-(1 / 2 : ℂ)) • A x⁻¹ := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · have hxi : 1 < x⁻¹ := one_lt_inv_iff₀.mpr ⟨hx, h⟩
    rw [A_apply_of_one_lt hxi]
    have hm : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, h⟩
    have hn : x ∉ Ioi (1 : ℝ) := fun h' => lt_irrefl _ (lt_trans h h')
    simp only [B, WeakFEPair.f_modif, Pi.add_apply,
      indicator_of_notMem hn, indicator_of_mem hm, zero_add, hurwitzEvenFEPair]
    have hfe := evenKernel_functional_equation (0 : UnitAddCircle) x
    rw [← evenKernel_eq_cosKernel_of_zero, one_div x] at hfe
    have hc : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [ofReal_cpow hx.le]; push_cast; ring_nf
    rw [hc, smul_eq_mul, Function.comp_apply, hfe]
    simp only [one_mul, mul_one]
    have hr : x ^ (-(1 / 2 : ℝ)) = 1 / x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hx.le, inv_eq_one_div]
    rw [hr]; push_cast; ring
  · simp [A, B]
  · have hxi : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    have hn : x ∉ Ioo (0 : ℝ) 1 := fun h' => lt_irrefl _ (lt_trans h h'.2)
    have hn' : x⁻¹ ∉ Ioi (1 : ℝ) := fun h' => lt_irrefl _ (lt_trans hxi h')
    simp [A, B, indicator_of_notMem hn, indicator_of_notMem hn']

lemma mellin_B (w : ℂ) : mellin B w = mellin A (1 / 2 - w) := by
  have h1 : mellin B w = mellin (fun t => (t : ℂ) ^ (-(1 / 2 : ℂ)) • A t⁻¹) w :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp only [B_eq t ht]
  rw [h1, mellin_cpow_smul, mellin_comp_inv]; congr 1; ring

theorem Λ₀_eq (w : ℂ) : P.Λ₀ w = mellin A w + mellin A (1 / 2 - w) := by
  have hA := mellinConvergent_indicator (measurableSet_Ioi (a := (1 : ℝ))) w
  have hB := mellinConvergent_indicator (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) w
  have h := (hasMellin_add hA hB).2
  rw [← mellin_B]
  change mellin P.f_modif w = _
  rw [show P.f_modif = fun t => A t + B t from funext f_modif_eq]
  exact h

/-- **Riemann's formula.** -/
theorem completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = (mellin A (s / 2) + mellin A (1 / 2 - s / 2)) / 2 - 1 / s - 1 / (1 - s) := by
  rw [← completedHurwitzZetaEven_zero, completedHurwitzZetaEven_eq, completedHurwitzZetaEven₀, Λ₀_eq]
  simp

end AEGIS.RHRiemannThetaFormulaV1

#print axioms AEGIS.RHRiemannThetaFormulaV1.completedRiemannZeta_eq
