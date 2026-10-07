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
# Sign changes of `Λ(1/2 + it)` give zeros on the critical line

`Λ = completedRiemannZeta` is real on the critical line: `conj (1/2 + it) = 1 - (1/2 + it)`, so the
functional equation `Λ (1 - s) = Λ s` and `Λ (conj s) = conj (Λ s)` force `Λ (1/2 + it) ∈ ℝ`.
It is continuous in `t`, so a sign change of `t ↦ re Λ(1/2 + it)` on `[a, b]` gives `t ∈ [a, b]` with
`ζ(1/2 + it) = 0`.  This is the first half of Turing's method (zeros *on* the line); the count `N(T)`
that excludes zeros *off* the line is not here.  AUTHORITY_EFFECT = NONE.
-/

open Complex ComplexConjugate

namespace AEGIS.RHCriticalLineSignV1

/-- The point `1/2 + it` of the critical line. -/
noncomputable def lineAt (t : ℝ) : ℂ := 1 / 2 + t * I

/-- `Λ(1/2 + it)`. -/
noncomputable def Xi (t : ℝ) : ℂ := completedRiemannZeta (lineAt t)

lemma lineAt_re (t : ℝ) : (lineAt t).re = 1 / 2 := by simp [lineAt]

lemma lineAt_ne_zero (t : ℝ) : lineAt t ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [lineAt] at this

lemma lineAt_ne_one (t : ℝ) : lineAt t ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp [lineAt] at this

lemma conj_lineAt (t : ℝ) : conj (lineAt t) = 1 - lineAt t := by
  apply Complex.ext <;> simp [lineAt]; norm_num

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have hπ : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
  have e1 : -conj s / 2 = conj (-s / 2) := by rw [map_div₀, map_neg, map_ofNat]
  have e2 : conj s / 2 = conj (s / 2) := by rw [map_div₀, map_ofNat]
  rw [Gammaℝ, Gammaℝ, e1, e2, Complex.cpow_conj _ _ hπ, Complex.conj_ofReal, Gamma_conj, map_mul]

/-- `Λ s = Γℝ(s) ζ(s)` off `0` with positive real part. -/
lemma completed_eq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [riemannZeta_def_of_ne_zero h0, mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

theorem Xi_conj (t : ℝ) : conj (Xi t) = Xi t := by
  have hpos : 0 < (lineAt t).re := by rw [lineAt_re]; norm_num
  have hcpos : 0 < (conj (lineAt t)).re := by rw [Complex.conj_re, lineAt_re]; norm_num
  have h1 : completedRiemannZeta (conj (lineAt t)) = conj (completedRiemannZeta (lineAt t)) := by
    rw [completed_eq_mul hcpos, completed_eq_mul hpos, Gammaℝ_conj, riemannZeta_conj, map_mul]
  rw [Xi, ← h1, conj_lineAt, completedRiemannZeta_one_sub]

/-- `Λ(1/2 + it)` is real. -/
theorem Xi_im (t : ℝ) : (Xi t).im = 0 := Complex.conj_eq_iff_im.mp (Xi_conj t)

theorem continuous_Xi : Continuous Xi := by
  rw [continuous_iff_continuousAt]; intro t
  have hl : Continuous lineAt := by unfold lineAt; fun_prop
  exact (differentiableAt_completedZeta (lineAt_ne_zero t) (lineAt_ne_one t)).continuousAt.comp
    hl.continuousAt

theorem zeta_zero_of_Xi_re_zero {t : ℝ} (h : (Xi t).re = 0) : riemannZeta (lineAt t) = 0 := by
  have hX : Xi t = 0 := Complex.ext h (Xi_im t)
  rw [riemannZeta_def_of_ne_zero (lineAt_ne_zero t)]
  simp only [Xi] at hX; rw [hX, zero_div]

/-- **A sign change of `re Λ(1/2 + it)` on `[a, b]` gives a zero of `ζ` on the critical line.** -/
theorem exists_zero_of_sign_change {a b : ℝ} (hab : a ≤ b)
    (hsign : (Xi a).re ≤ 0 ∧ 0 ≤ (Xi b).re ∨ 0 ≤ (Xi a).re ∧ (Xi b).re ≤ 0) :
    ∃ t ∈ Set.Icc a b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hc : ContinuousOn (fun t => (Xi t).re) (Set.Icc a b) :=
    (Complex.continuous_re.comp continuous_Xi).continuousOn
  rcases hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, h⟩ := intermediate_value_Icc hab hc ⟨ha, hb⟩
    exact ⟨t, ht, zeta_zero_of_Xi_re_zero h⟩
  · obtain ⟨t, ht, h⟩ := intermediate_value_Icc' hab hc ⟨hb, ha⟩
    exact ⟨t, ht, zeta_zero_of_Xi_re_zero h⟩

end AEGIS.RHCriticalLineSignV1

#print axioms AEGIS.RHCriticalLineSignV1.Xi_im
#print axioms AEGIS.RHCriticalLineSignV1.exists_zero_of_sign_change
