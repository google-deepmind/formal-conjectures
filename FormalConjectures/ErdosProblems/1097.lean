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
# Erdős Problem 1097

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

namespace Erdos1097

/--
Given a finite set of integers `A` (modelled as a `Finset ℤ`), the set
`CommonDifferencesThreeTermAP A` consists of all integers `d` such that there
is a non-trivial three-term arithmetic progression `a, b, c ∈ A` with
`b - a = d` and `c - b = d`.
-/
def CommonDifferencesThreeTermAP (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b - a = d ∧ c - b = d}

/--
The main conjecture: for any finite set of integers $A$ with $|A| = n$, the number of distinct
common differences in three-term arithmetic progressions is $O(n^{3/2})$.
-/
@[category research open, AMS 11]
theorem erdos_1097 : answer(sorry) ↔ ∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
    (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/--
A weaker bound has been proven: there are always at most $n^2$ such values of $d$.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.weaker :
    ∀ A, (CommonDifferencesThreeTermAP A).ncard ≤ A.card ^ 2 := by
  intro A
  set D := Finset.image (fun p : ℤ × ℤ => p.2 - p.1) (A ×ˢ A)
  have h_sub : CommonDifferencesThreeTermAP A ⊆ (D : Set ℤ) := by
    rintro d ⟨-, a, ha, b, hb, -, -, hab, -⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  calc (CommonDifferencesThreeTermAP A).ncard
      ≤ (D : Set ℤ).ncard := Set.ncard_le_ncard h_sub D.finite_toSet
    _ = D.card := Set.ncard_coe_finset _
    _ ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product _ _
    _ = A.card ^ 2 := (sq _).symm

/--
A trivial lower bound: for sufficiently large `n` there exist sets $A$ with $|A| = n$ that contain at least $\Omega(n)$
distinct common differences of three-term arithmetic progressions.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.lower_bound : ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop, ∃ (A : Finset ℤ),
    A.card = n ∧ c * (n : ℝ) ≤ (CommonDifferencesThreeTermAP A).ncard := by
  refine ⟨1/4, by norm_num, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨4, fun n hn => ?_⟩
  refine ⟨(Finset.range n).image (fun k : ℕ => (k : ℤ)), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  set A := (Finset.range n).image (fun k : ℕ => (k : ℤ))
  set k : ℕ := (n - 1) / 2 with hk_def
  set D : Finset ℤ := (Finset.range k).image (fun i : ℕ => ((i + 1 : ℕ) : ℤ))
  have hk_ge_nat : 4 * k ≥ n := by simp [hk_def]; omega
  have hD_card : D.card = k := by
    rw [Finset.card_image_of_injective _, Finset.card_range]
    intro a b h
    simp only at h
    have : (a + 1 : ℤ) = (b + 1 : ℤ) := by exact_mod_cast h
    omega
  have h_finite : (CommonDifferencesThreeTermAP A).Finite := by
    apply Set.Finite.subset
      (Finset.image (fun p : ℤ × ℤ => p.2 - p.1) (A ×ˢ A)).finite_toSet
    rintro d ⟨-, a, ha, b, hb, -, -, hab, -⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩)
  have hD_sub : (D : Set ℤ) ⊆ CommonDifferencesThreeTermAP A := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_image] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    rw [Finset.mem_range] at hi
    have h2d_lt : 2 * (i + 1) < n := by simp [hk_def] at hi; omega
    refine ⟨by push_cast; positivity, 0, ?_, ((i + 1 : ℕ) : ℤ), ?_,
      ((2 * (i + 1) : ℕ) : ℤ), ?_, by push_cast; ring, by push_cast; ring⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by push_cast⟩
    · exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Finset.mem_image.mpr ⟨2 * (i + 1), Finset.mem_range.mpr h2d_lt, rfl⟩
  calc (1 / 4 : ℝ) * n
      = (n : ℝ) / 4 := by ring
    _ ≤ (k : ℝ) := by
        have : (4 : ℝ) * k ≥ n := by exact_mod_cast hk_ge_nat
        linarith
    _ = (D.card : ℝ) := by rw [hD_card]
    _ = ((D : Set ℤ).ncard : ℝ) := by rw [Set.ncard_coe_finset]
    _ ≤ ((CommonDifferencesThreeTermAP A).ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hD_sub h_finite

end Erdos1097
