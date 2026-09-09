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

import FormalConjectures.ErdosProblems.«348»

/-!
# Indexed completeness in Erdős Problem 348

Tests for repeated terms and deletion of sequence positions.

*Reference:* [erdosproblems.com/348](https://www.erdosproblems.com/348)
-/

namespace Erdos348.Tests

theorem ones_complete : IsAddCompleteNatSeq' (fun _ : ℕ ↦ 1) := by
  apply Filter.Eventually.of_forall
  intro n
  exact ⟨Finset.range n, by simp⟩

theorem range_ones_not_complete : ¬ IsAddComplete (Set.range (fun _ : ℕ ↦ 1)) := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨B, hB, hEq⟩ := hN (N + 2) (by omega)
  have hsub : B ⊆ {1} := by
    intro i hi
    obtain ⟨j, rfl⟩ := hB hi
    simp
  have hsum := Finset.sum_le_sum_of_subset (f := id) hsub
  simp only [Finset.sum_singleton, id_eq] at hsum
  omega

theorem ones_complete_after_deletions (s : Finset ℕ) :
    IsAddCompleteNatSeq' (Function.updateFinset (fun _ : ℕ ↦ 1) s 0) := by
  apply Filter.Eventually.of_forall
  intro n
  refine ⟨Finset.Ico (s.sup id + 1) (s.sup id + 1 + n), ?_⟩
  have hsum : (∑ i ∈ Finset.Ico (s.sup id + 1) (s.sup id + 1 + n),
      Function.updateFinset (fun _ : ℕ ↦ 1) s 0 i) =
      ∑ _i ∈ Finset.Ico (s.sup id + 1) (s.sup id + 1 + n), (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hlo := (Finset.mem_Ico.mp hi).1
    have hnot : i ∉ s := by
      intro his
      have hle : i ≤ s.sup id := Finset.le_sup (f := id) his
      omega
    simp [Function.updateFinset, hnot]
  rw [hsum]
  simp

example : Function.updateFinset (fun _ : ℕ ↦ 1) {0} 0 0 = 0 := by
  norm_num [Function.updateFinset]

example : Function.updateFinset (fun _ : ℕ ↦ 1) {0} 0 1 = 1 := by
  norm_num [Function.updateFinset]

theorem complete_with_small_gaps : IsAddCompleteNatSeq' (fun i : ℕ ↦ i + 2) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨2, ?_⟩
  intro n hn
  refine ⟨{n - 2}, ?_⟩
  simp only [Finset.sum_singleton]
  omega

-- Check the conjecture's type without choosing its unknown answer.
example : ∃ S : Set (ℕ × ℕ),
    { (m, n) | (m) (n) (_ : m < n) (a : ℕ → ℕ) (_ : Monotone a)
      (_ : ∀ s, s.card = m → IsAddCompleteNatSeq' (Function.updateFinset a s 0))
      (_ : ∀ t, t.card = n → ¬ IsAddCompleteNatSeq' (Function.updateFinset a t 0)) } = S :=
  ⟨_, erdos_348⟩

end Erdos348.Tests
