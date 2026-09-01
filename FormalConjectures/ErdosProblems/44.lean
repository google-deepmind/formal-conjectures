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

import FormalConjecturesUtil

/-!
# Erdős Problem 44: Extending Sidon Sets

*Reference:* [erdosproblems.com/44](https://www.erdosproblems.com/44)
-/

open Function Set Finset

namespace Erdos44

-- Reference: https://arxiv.org/pdf/2103.15850
/-- The maximum size of a Sidon set in `{1, ..., N}` is less than or equal to `2 * √N`. -/
@[category textbook, AMS 5 11]
theorem maxSidonSubsetCard_icc_bound (N : ℕ) (hN : 1 ≤ N) :
    maxSidonSubsetCard (Icc 1 N) ≤ 2 * Real.sqrt N := by
  have key : maxSidonSubsetCard (Finset.Icc 1 N) ^ 2 ≤ 4 * N := by
    -- Pick a Sidon subset of `{1, ..., N}` of maximal size.
    obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup
      ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
      ⟨∅, by simp [IsSidon]⟩ Finset.card
    rw [maxSidonSubsetCard, hBeq]
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    obtain ⟨hsub, hsid⟩ := hB
    -- Distinct ordered pairs of elements of `B` have distinct differences, and each difference
    -- lies in `{-N, ..., N}`.
    have hcard : B.offDiag.card ≤ (Finset.Icc (-(N : ℤ)) N).card := by
      refine Finset.card_le_card_of_injOn (fun p ↦ (p.1 : ℤ) - p.2) ?_ ?_
      · rintro ⟨a, b⟩ hab
        rw [Finset.mem_coe, Finset.mem_offDiag] at hab
        have ha' := Finset.mem_Icc.mp (hsub hab.1)
        have hb' := Finset.mem_Icc.mp (hsub hab.2.1)
        simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · rintro ⟨a, b⟩ ha ⟨c, d⟩ hc hac
        rw [Finset.mem_coe, Finset.mem_offDiag] at ha hc
        simp only at hac
        have hsum : a + d = c + b := by omega
        rcases hsid a ha.1 c hc.1 d hc.2.1 b ha.2.1 hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2]
        · exact absurd h1 ha.2.2
    have hIcc : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    rw [Finset.offDiag_card, hIcc] at hcard
    have hle : B.card ≤ N := by simpa using Finset.card_le_card hsub
    rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · simp [h0]
    have hkk : B.card ≤ B.card * B.card := Nat.le_mul_of_pos_left _ hpos
    calc B.card ^ 2 = B.card * B.card := sq B.card
      _ ≤ 2 * N + 1 + B.card := by omega
      _ ≤ 4 * N := by omega
  have h1 : ((maxSidonSubsetCard (Finset.Icc 1 N) : ℝ)) ^ 2 ≤ 4 * N := by exact_mod_cast key
  have h2 : (2 : ℝ) * Real.sqrt N = Real.sqrt (4 * N) := by
    rw [show (4 : ℝ) * N = 2 ^ 2 * N by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h2, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (maxSidonSubsetCard (Finset.Icc 1 N) : ℝ))]
  exact Real.sqrt_le_sqrt h1

/--
**Erdős Problem 44:** Let N ≥ 1 and `A ⊆ {1,…,N}` be a Sidon set. Is it true that, for any ε > 0,
there exist M = M(ε) and `B ⊆ {N+1,…,M}` such that `A ∪ B ⊆ {1,…,M}` is a Sidon set
of size at least `(1−ε)M^{1/2}`?

This problem asks whether any Sidon set can be extended to achieve a density
arbitrarily close to the optimal density for Sidon sets.
-/
@[category research open, AMS 5 11]
theorem erdos_44 : answer(sorry) ↔ ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) →
    ∀ᵉ (ε > (0 : ℝ)), ∃ᵉ (M > N) (B ⊆ Finset.Icc (N + 1) M),
      IsSidon (A ∪ B : Set ℕ) ∧ (1 - ε) * Real.sqrt M ≤ (A ∪ B).card := by
  sorry

/--
The case where we start with an empty set (constructing large Sidon sets).
-/
@[category research open, AMS 5 11]
theorem erdos_44.variants.empty_start : answer(sorry) ↔ ∀ᵉ (ε > (0 : ℝ)), ∀ᶠ (M : ℕ) in Filter.atTop,
    ∃ᵉ (A ⊆ Finset.Icc 1 M), IsSidon (A : Set ℕ) ∧ (1 - ε) * Real.sqrt M ≤ A.card := by
  sorry

/-  ## Related results and examples -/

/--
The set `{1, 2, 4, 8, 13}` is a Sidon set in `{1, ..., 13}`.
-/
@[category textbook, AMS 5 11]
theorem example_sidon_set : IsSidon ({1, 2, 4, 8, 13} : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  rcases hi₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₁ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hi₂ with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj₂ with rfl | rfl | rfl | rfl | rfl <;>
  simp_all

/--
For any `N`, there exists a Sidon set of size at least `√N/2`.
-/
@[category textbook, AMS 5 11]
theorem sidon_set_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N.sqrt / 2 ≤ A.card := by
  sorry

/--
The greedy construction gives a Sidon set of size approximately `√N`.
-/
@[category textbook, AMS 5 11]
theorem greedy_sidon_construction (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ A.card ≥ N.sqrt := by
  sorry

end Erdos44
