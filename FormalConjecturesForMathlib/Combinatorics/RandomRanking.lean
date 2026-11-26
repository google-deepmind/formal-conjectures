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

public import FormalConjecturesForMathlib.Combinatorics.StableMarriage
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Tactic.NormNum

/-!
# Weighted random complete rankings

A ranking maps candidates to zero-based ranks. Its likelihood is the product of the probabilities
of successive draws without replacement, each proportional to the remaining candidates' weights.
All agents draw independently.

Reference: S. Mauras, *Analysis of Random Models for Stable Matchings* (2021), Definition 3.2,
https://www.irif.fr/~mauras/thesis/thesis.pdf.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace RandomRanking

/-- A nonnegative finite weight vector induces a distribution after normalization.
If every weight is zero, use the uniform distribution. -/
noncomputable def ofWeights {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ≥0) : PMF α := by
  classical
  exact if h : ∑ a, f a = 0 then PMF.uniformOfFintype α else
    PMF.normalize (fun a ↦ (f a : ℝ≥0∞))
      (by
        rw [tsum_fintype, ← ENNReal.ofNNReal_finsetSum]
        exact fun hz ↦ h (ENNReal.coe_eq_zero.mp hz))
      (by simp only [tsum_fintype, ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_ne_top, ne_eq,
        not_false_eq_true])

/-- Normalization divides each weight by the total weight when that total is nonzero. -/
theorem ofWeights_apply {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ≥0)
    (hf : ∑ a, f a ≠ 0) (a : α) :
    ofWeights f a = (f a : ℝ≥0∞) / (∑ b, f b : ℝ≥0) := by
  classical
  simp only [ofWeights, dif_neg hf, PMF.normalize_apply, tsum_fintype,
    ← ENNReal.ofNNReal_finsetSum, div_eq_mul_inv]

/-- Sampling-without-replacement likelihood of a complete ranking. Positive weights give the
usual product of successive choice probabilities. -/
noncomputable def likelihood {n : ℕ} (weight : Fin n → ℝ≥0)
    (rank : Equiv.Perm (Fin n)) : ℝ≥0 :=
  ∏ k, weight (rank.symm k) / ∑ x with k ≤ rank x, weight x

/-- Every complete ranking has positive likelihood when all candidates have positive weight. -/
theorem likelihood_pos {n : ℕ} (weight : Fin n → ℝ≥0) (hw : ∀ i, 0 < weight i)
    (rank : Equiv.Perm (Fin n)) : 0 < likelihood weight rank := by
  apply Finset.prod_pos
  intro k _
  apply div_pos (hw _)
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (hw i)
  · exact ⟨rank.symm k, by simp, hw _⟩

/-- Independent weighted rankings on the two sides of a matching market.
The first matrix gives men's weights for women; the second gives women's weights for men,
with both matrices indexed by man then woman. -/
noncomputable def profile {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    PMF (StableMarriage.Profile n) :=
  ofWeights fun p ↦ (∏ m, likelihood (P m) (p.manRank m)) *
    ∏ w, likelihood (fun m ↦ Q m w) (p.womanRank w)

/-- The weighted profile distribution has total mass one. -/
theorem profile_univ {n : ℕ} (P Q : Fin n → Fin n → ℝ≥0) :
    (profile P Q).toMeasure Set.univ = 1 := by
  simp

/-- An empty ranking has likelihood one. -/
theorem likelihood_zero (weight : Fin 0 → ℝ≥0) (rank : Equiv.Perm (Fin 0)) :
    likelihood weight rank = 1 := by
  simp [likelihood]

/-- A singleton ranking with positive weight has likelihood one. -/
theorem likelihood_one (weight : Fin 1 → ℝ≥0) (h : weight 0 ≠ 0) :
    likelihood weight (Equiv.refl _) = 1 := by
  simp [likelihood, h]

/-- With weights two and one, the identity ranking has probability two thirds. -/
theorem likelihood_two : likelihood ![2, 1] (Equiv.refl (Fin 2)) = 2 / 3 := by
  change (∏ k : Fin 2, (![2, 1] : Fin 2 → ℝ≥0) k /
    ∑ x : Fin 2 with k ≤ x, (![2, 1] : Fin 2 → ℝ≥0) x) = 2 / 3
  simp only [Fin.prod_univ_two]
  have hs : (∑ x : Fin 2 with (1 : Fin 2) ≤ x, (![2, 1] : Fin 2 → ℝ≥0) x) = 1 := by
    rw [Finset.sum_filter]
    norm_num [Fin.sum_univ_two]
  norm_num [Finset.sum_filter, Fin.sum_univ_two, hs]

/-- With weights two and one, the reverse ranking has probability one third. -/
theorem likelihood_two_swap : likelihood ![2, 1] (Equiv.swap (0 : Fin 2) 1) = 1 / 3 := by
  norm_num [likelihood, Fin.prod_univ_two, Finset.sum_filter, Fin.sum_univ_two]

end RandomRanking
