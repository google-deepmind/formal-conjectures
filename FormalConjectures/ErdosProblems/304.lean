/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 304
*Reference:* [erdosproblems.com/304](https://www.erdosproblems.com/304)
-/

open Asymptotics Filter

namespace Erdos304

/--
The set of `k` for which `a / b` can be expressed as a sum of `k` distinct unit fractions.
-/
def unitFractionExpressible (a b : ℕ) : Set ℕ :=
  {k | ∃ s : Finset ℕ, s.card = k ∧ (∀ n ∈ s, n > 1) ∧ (a / b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹}

@[category API, simp, AMS 11]
lemma zero_mem_unitFractionExpressible_iff {a b : ℕ} :
    0 ∈ unitFractionExpressible a b ↔ a = 0 ∨ b = 0 := by
  simp_all [unitFractionExpressible]

@[category API, AMS 11]
lemma unitFractionExpressible_of_zero {a b : ℕ} (h : a = 0 ∨ b = 0) :
    unitFractionExpressible a b = {0} := by
  simp only [Set.eq_singleton_iff_unique_mem, zero_mem_unitFractionExpressible_iff, *]
  have : (a / b : ℚ) = 0 := by simpa
  simp only [unitFractionExpressible, gt_iff_lt, CharP.cast_eq_zero, div_zero, Set.mem_setOf_eq,
    forall_exists_index, and_imp, true_and, or_true, this]
  rintro _ s rfl hs h
  rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)] at h
  simp only [inv_eq_zero, Nat.cast_eq_zero] at h
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro i hi
  linarith [h i hi, hs i hi]

@[category API, AMS 11]
lemma unitFractionExpressible_zero_left {b : ℕ} :
    unitFractionExpressible 0 b = {0} := unitFractionExpressible_of_zero (by simp)

@[category API, AMS 11]
lemma unitFractionExpressible_zero_right {a : ℕ} :
    unitFractionExpressible a 0 = {0} := unitFractionExpressible_of_zero (by simp)

@[category API, AMS 11]
lemma zero_notMem_unitFractionExpressible {a b : ℕ} :
    0 ∉ unitFractionExpressible a b ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp_all [unitFractionExpressible]

@[category API, AMS 11]
lemma eq_inv_of_one_mem_unitFractionExpressible {a b : ℕ}
    (h : 1 ∈ unitFractionExpressible a b) : ∃ m : ℕ, 1 < m ∧ (a / b : ℚ) = (m : ℚ)⁻¹ := by
  simp only [unitFractionExpressible, gt_iff_lt, Set.mem_setOf_eq, Finset.card_eq_one] at h
  obtain ⟨_, ⟨m, rfl⟩, h₁, h₂⟩ := h
  simp only [Finset.mem_singleton, forall_eq, Finset.sum_singleton] at h₁ h₂
  use m

@[category API, AMS 11]
lemma dvd_of_one_mem_unitFractionExpressible {a b : ℕ}
    (h : 1 ∈ unitFractionExpressible a b) : a ∣ b := by
  obtain ⟨m, hm₁, hm⟩ := eq_inv_of_one_mem_unitFractionExpressible h
  have : b ≠ 0 := by
    rintro rfl
    simp [eq_comm] at hm
    omega
  use m
  field_simp at hm
  exact mod_cast hm.symm

/-- Let $$N(a, b)$$, denoted here by `smallestCollection a b` be the minimal k such that there
exist integers $1 < n_1 < n_2 < ... < n_k$ with
$$\frac{a}{b} = \sum_{i=1}^k \frac{1}{n_i}$$ -/
noncomputable def smallestCollection (a b : ℕ) : ℕ := sInf (unitFractionExpressible a b)

-- in fact `(unitFractionExpressible a b).Nonempty` should always be true, but we do not prove it
-- for now
@[category API, AMS 11]
lemma smallestCollection_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (unitFractionExpressible a b).Nonempty) :
    0 < smallestCollection a b := by
  suffices smallestCollection a b ≠ 0 by omega
  intro h'
  have : 0 ∈ unitFractionExpressible a b := h' ▸ Nat.sInf_mem h
  simp_all

@[category API, AMS 11]
lemma smallestCollection_left_one (b : ℕ) (hb : 1 < b) : smallestCollection 1 b = 1 := by
  have : 1 ∈ unitFractionExpressible 1 b := ⟨{b}, by simpa⟩
  have : smallestCollection 1 b ≤ 1 := Nat.sInf_le this
  have : 0 ∉ unitFractionExpressible 1 b := by simp; omega
  have : smallestCollection 1 b ≠ 0 := ne_of_mem_of_not_mem (Nat.sInf_mem ⟨_, ‹_›⟩) this
  omega

@[category API, AMS 11]
lemma eq_one_of_smallestCollection_eq_one {a b : ℕ}
    (h : smallestCollection a b = 1) : ∃ m : ℕ, 1 < m ∧ (a / b : ℚ) = (m : ℚ)⁻¹ := by
  have : 1 ∈ unitFractionExpressible a b := h ▸ Nat.sInf_mem (Nat.nonempty_of_sInf_eq_succ h)
  apply eq_inv_of_one_mem_unitFractionExpressible this

@[category API, AMS 11]
lemma dvd_of_smallestCollection_eq_one {a b : ℕ}
    (h : smallestCollection a b = 1) : a ∣ b := by
  have : 1 ∈ unitFractionExpressible a b := h ▸ Nat.sInf_mem (Nat.nonempty_of_sInf_eq_succ h)
  apply dvd_of_one_mem_unitFractionExpressible this

@[category test, AMS 11]
lemma smallestCollection_two_fifteen : smallestCollection 2 15 = 2 := by
  have h : 2 ∈ unitFractionExpressible 2 15 := by
    use {10, 30}
    norm_num [Finset.card_insert_of_not_mem, Finset.card_singleton]
  have : smallestCollection 2 15 ≤ 2 := Nat.sInf_le h
  have : 0 < smallestCollection 2 15 := smallestCollection_pos (by simp) (by simp) ⟨_, h⟩
  have : smallestCollection 2 15 ≠ 1 := by
    intro h'
    have := dvd_of_smallestCollection_eq_one h'
    norm_num at this
  omega

/-- Write $$N(b) = max_{1 \leq a < b} N(a, b)$$. -/
noncomputable def smallestCollectionTo (b : ℕ) : ℕ :=
  sSup {smallestCollection a b | a ∈ Finset.Ico 1 b}

/--
In 1950, Erdős [Er50c] proved the upper bound $$N(b) \ll \log b / \log \log b$$.
[Er50c] Erdős, P., Az ${1}/{x_1} + {1}/{x_2} + \ldots + {1}/{x_n} =A/B$ egyenlet eg\'{E}sz sz\'{A}m\'{u} megold\'{A}sairól. Mat. Lapok (1950), 192-210.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.upper_1950 :
    (fun b => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => Real.log b / Real.log (Real.log b)) := by
  sorry

/--
In 1950, Erdős [Er50c] proved the lower bound $$\log \log b \ll N(b)$$.
[Er50c] Erdős, P., Az ${1}/{x_1} + {1}/{x_2} + \ldots + {1}/{x_n} =A/B$ egyenlet eg\'{E}sz sz\'{A}m\'{u} megold\'{A}sairól. Mat. Lapok (1950), 192-210.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.lower_1950 :
    (fun b : ℕ => Real.log (Real.log b)) =O[atTop]
      (fun b => (smallestCollectionTo b : ℝ)) := by
  sorry

/--
In 1985 Vose [Vo85] proved the upper bound $$N(b) \ll \sqrt{\log b}$$.
[Vo85] Vose, Michael D., Egyptian fractions. Bull. London Math. Soc. (1985), 21-24.
-/
@[category research solved, AMS 11]
theorem erdos_304.variants.upper_1985 :
    (fun b => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b => Real.sqrt (Real.log b)) :=
  sorry

/--
Is it true that $$N(b) \ll \log \log b$$?
-/
@[category research open, AMS 11]
theorem upper_bound :
    (fun b : ℕ => (smallestCollectionTo b : ℝ)) =O[atTop]
      (fun b : ℕ => Real.log (Real.log b)) ↔ answer(sorry) := by
  sorry

end Erdos304
