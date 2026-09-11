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

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Meromorphic.Order

@[expose] public section

/-!
# Products of Deligne's Archimedean Gamma factors

We study `Complex.prodGammaℝ N s = ∏ a ∈ N, Γℝ (s + a)` for a multiset `N` of integer shifts,
the shape of the Archimedean factor of a motivic L-function. The main results are that it is
meromorphic with no zeros of its own (`meromorphicOrderAt_prodGammaℝ_nonpos`), and the
characterisation `meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff` of the integers at which it
is regular, which are the critical integers in the sense of Deligne.
-/

namespace Complex

/-- At an integer, `Gammaℝ` vanishes exactly at the non-positive even ones, equivalently where
it has a pole. -/
lemma Gammaℝ_intCast_eq_zero_iff {m : ℤ} : Gammaℝ (m : ℂ) = 0 ↔ m ≤ 0 ∧ Even m := by
  rw [Gammaℝ_eq_zero_iff, Int.even_iff]
  refine ⟨fun ⟨j, hj⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ⟨(-m / 2).toNat, ?_⟩⟩
  · have hm : m = -(2 * (j : ℤ)) := by exact_mod_cast hj
    lia
  · exact_mod_cast (by lia : m = -(2 * ((-m / 2).toNat : ℤ)))

/-- `Complex.prodGammaℝ` is the product of Deligne Archimedean Gamma factors with arguments
shifted by integers, possibly with repetition. -/
noncomputable def prodGammaℝ (N : Multiset ℤ) (s : ℂ) : ℂ :=
  (N.map fun a : ℤ ↦ Gammaℝ (s + a)).prod

lemma analyticOnNhd_inv_Gammaℝ_add (a : ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) Set.univ :=
  (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a)).differentiableOn.analyticOnNhd
    isOpen_univ

lemma analyticAt_inv_Gammaℝ_add (a s : ℂ) :
    AnalyticAt ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) s :=
  analyticOnNhd_inv_Gammaℝ_add a s (Set.mem_univ s)

/-- A shifted `Gammaℝ` is meromorphic everywhere: it is the inverse of an entire function. -/
lemma meromorphicAt_Gammaℝ_add (a s : ℂ) : MeromorphicAt (fun z ↦ Gammaℝ (z + a)) s := by
  have : (fun z ↦ Gammaℝ (z + a)) = (fun z ↦ (Gammaℝ (z + a))⁻¹)⁻¹ := by funext; simp
  exact this ▸ (analyticAt_inv_Gammaℝ_add a s).meromorphicAt.inv

/-- `Gammaℝ⁻¹` is entire and takes the value `1` at `1`, so by the identity theorem it does not
vanish identically near any point and its analytic order there is finite. -/
lemma analyticOrderAt_inv_Gammaℝ_add_ne_top (a s : ℂ) :
    analyticOrderAt (fun z ↦ (Gammaℝ (z + a))⁻¹) s ≠ ⊤ := by
  intro h
  have hev : (fun z ↦ (Gammaℝ (z + a))⁻¹) =ᶠ[nhds s] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp h] with z hz using hz
  have hzero := (analyticOnNhd_inv_Gammaℝ_add a).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) hev
  have h₁ := hzero (Set.mem_univ (1 - a))
  simp only [Pi.zero_apply, show (1 - a) + a = 1 by ring, Gammaℝ_one, inv_one] at h₁
  exact one_ne_zero h₁

/-- The order of a shifted `Gammaℝ` at any point is `-n` for a natural number `n`, and `n = 0`
exactly when the value is nonzero. `Gammaℝ` is the inverse of an entire function, so it has no
zeros of its own: every point is either a regular point or a pole. -/
theorem meromorphicOrderAt_Gammaℝ_add_eq_neg (a s : ℂ) :
    ∃ n : ℕ, meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s = ((-n : ℤ) : WithTop ℤ) ∧
      (Gammaℝ (s + a) = 0 ↔ n ≠ 0) := by
  have hg : AnalyticAt ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) s := analyticAt_inv_Gammaℝ_add a s
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_inv_Gammaℝ_add_ne_top a s)
  refine ⟨n, ?_, ?_⟩
  · have : (fun z ↦ Gammaℝ (z + a)) = (fun z ↦ (Gammaℝ (z + a))⁻¹)⁻¹ := by funext; simp
    simp [this, meromorphicOrderAt_inv, hg.meromorphicOrderAt_eq, ← hn]
  · simp [← inv_eq_zero, ← hg.analyticOrderAt_ne_zero, ← hn]

/-- `Gammaℝ (s + a)` is only ever zero when it has a pole. -/
theorem meromorphicOrderAt_Gammaℝ_add_neg_iff {a s : ℂ} :
    meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s < 0 ↔ Gammaℝ (s + a) = 0 := by
  obtain ⟨n, hord, hzero⟩ := meromorphicOrderAt_Gammaℝ_add_eq_neg a s
  rw [hord, hzero, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
  lia

/-- A shifted `Gammaℝ` never has a zero, so its order is at most `0` everywhere. -/
lemma meromorphicOrderAt_Gammaℝ_add_nonpos (a s : ℂ) :
    meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s ≤ 0 := by
  obtain ⟨n, hord, -⟩ := meromorphicOrderAt_Gammaℝ_add_eq_neg a s
  rw [hord, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  lia

@[simp]
lemma prodGammaℝ_zero : prodGammaℝ 0 = fun _ ↦ 1 := by
  funext; simp [prodGammaℝ]

lemma prodGammaℝ_cons (a : ℤ) (N : Multiset ℤ) :
    prodGammaℝ (a ::ₘ N) = (fun z ↦ Gammaℝ (z + a)) * prodGammaℝ N := by
  funext; simp [prodGammaℝ]

lemma meromorphicAt_prodGammaℝ (N : Multiset ℤ) (s : ℂ) :
    MeromorphicAt (prodGammaℝ N) s := by
  induction N using Multiset.induction with
  | empty => exact prodGammaℝ_zero ▸ analyticAt_const.meromorphicAt
  | cons a t ih => exact prodGammaℝ_cons a t ▸ (meromorphicAt_Gammaℝ_add _ s).mul ih

lemma meromorphicOrderAt_prodGammaℝ_zero (s : ℂ) : meromorphicOrderAt (prodGammaℝ 0) s = 0 := by
  rw [prodGammaℝ_zero, analyticAt_const.meromorphicOrderAt_eq,
    analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero]
  rfl

/-- `prodGammaℝ` has no zeros of its own, so its order is at most `0` at every point. -/
lemma meromorphicOrderAt_prodGammaℝ_nonpos (N : Multiset ℤ) (s : ℂ) :
    meromorphicOrderAt (prodGammaℝ N) s ≤ 0 := by
  induction N using Multiset.induction with
  | empty => exact (meromorphicOrderAt_prodGammaℝ_zero s).le
  | cons a t ih =>
    rw [prodGammaℝ_cons, meromorphicOrderAt_mul (meromorphicAt_Gammaℝ_add _ s)
      (meromorphicAt_prodGammaℝ t s)]
    exact add_nonpos (meromorphicOrderAt_Gammaℝ_add_nonpos _ s) ih

private lemma add_nonneg_iff_of_nonpos {x y : WithTop ℤ} (hx : x ≤ 0) (hy : y ≤ 0) :
    0 ≤ x + y ↔ 0 ≤ x ∧ 0 ≤ y := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by rw [le_antisymm hx h₁, le_antisymm hy h₂, add_zero]⟩
  refine ⟨?_, ?_⟩ <;> by_contra hlt <;> rw [not_le] at hlt
  · exact absurd (h.trans (add_le_add_right hy x |>.trans_eq (add_zero x))) hlt.not_ge
  · exact absurd (h.trans (add_le_add_left hx y |>.trans_eq (zero_add y))) hlt.not_ge

lemma meromorphicOrderAt_prodGammaℝ_nonneg_iff {shifts : Multiset ℤ} {s : ℂ} :
    0 ≤ meromorphicOrderAt (prodGammaℝ shifts) s ↔
      ∀ a ∈ shifts, 0 ≤ meromorphicOrderAt (fun z ↦ Gammaℝ (z + (a : ℂ))) s := by
  induction shifts using Multiset.induction with
  | empty => exact ⟨fun _ _ h ↦ absurd h (Multiset.notMem_zero _), fun _ ↦
      (meromorphicOrderAt_prodGammaℝ_zero s).ge⟩
  | cons a t ih =>
    rw [prodGammaℝ_cons, meromorphicOrderAt_mul (meromorphicAt_Gammaℝ_add _ s)
      (meromorphicAt_prodGammaℝ t s),
      add_nonneg_iff_of_nonpos (meromorphicOrderAt_Gammaℝ_add_nonpos _ s)
        (meromorphicOrderAt_prodGammaℝ_nonpos t s), ih]
    simp [Multiset.mem_cons, or_imp, forall_and]

theorem meromorphicOrderAt_Gammaℝ_add_intCast_nonneg_iff {a m : ℤ} :
    0 ≤ meromorphicOrderAt (fun z ↦ Gammaℝ (z + (a : ℂ))) (m : ℂ) ↔ Odd (m + a) ∨ 0 < m + a := by
  rw [← not_lt, meromorphicOrderAt_Gammaℝ_add_neg_iff,
    show ((m : ℂ) + (a : ℂ)) = (((m + a : ℤ)) : ℂ) by push_cast; ring,
    Gammaℝ_intCast_eq_zero_iff, Int.odd_iff, Int.even_iff]
  lia

lemma meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff {shifts : Multiset ℤ} {m : ℤ} :
    0 ≤ meromorphicOrderAt (prodGammaℝ shifts) (m : ℂ) ↔
      ∀ a ∈ shifts, Odd (m + a) ∨ 0 < m + a := by
  simp only [meromorphicOrderAt_prodGammaℝ_nonneg_iff,
    meromorphicOrderAt_Gammaℝ_add_intCast_nonneg_iff]

end Complex
