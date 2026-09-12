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

import FormalConjecturesUtil

/-!
# Erdős Problem 885

*References:*
- [erdosproblems.com/885](https://www.erdosproblems.com/885)
- [ErRo97] Erdős, P. and Rosenfeld, M., The factor-difference set of integers. (1997)
- [Ji99] Jiménez-Urroz, J., A note on a conjecture of Erdős and {R}osenfeld. (1999)
- [Br19] Bremner, A., On a problem of Erdős related to common factor differences. (2019)
-/

open Nat Set Finset

namespace Erdos885

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/--
For $n \geq 1$ the factor difference set is finite: any factorisation $n = ab$ has
$a, b \leq n$, so every element of $D(n)$ is at most $n$.
-/
@[category API, AMS 11]
theorem factorDifferenceSet_finite {n : ℕ} (hn : 1 ≤ n) :
    (factorDifferenceSet n).Finite := by
  refine (Set.finite_Iic n).subset ?_
  rintro d ⟨a, b, hab, hd⟩
  have ha : a ≤ n := Nat.le_of_dvd (by omega) ⟨b, hab⟩
  have hb : b ≤ n := Nat.le_of_dvd (by omega) ⟨a, hab.trans (Nat.mul_comm a b)⟩
  have hd' : (d : ℤ) ≤ n := by rw [hd]; exact abs_le.mpr ⟨by omega, by omega⟩
  exact Set.mem_Iic.mpr (by exact_mod_cast hd')

/--
Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that
$|\cap_i D(N_i)| \geq k$?
-/
@[category research open, AMS 11]
theorem erdos_885 : answer(sorry) ↔ ∀ k ≥ 1,
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k := by
  sorry

/--
Erdős and Rosenfeld [ErRo97] proved this is true for $k=2$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{12, 42}, by decide, by decide, ?_⟩
  have hsub : ({1, 11} : Set ℕ) ⊆
      ⋂ n ∈ ({12, 42} : Finset ℕ), factorDifferenceSet n := by
    simp only [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iInter,
      Finset.mem_insert, Finset.mem_singleton]
    rintro d (rfl | rfl) n (rfl | rfl)
    · exact ⟨3, 4, by norm_num, by norm_num⟩
    · exact ⟨6, 7, by norm_num, by norm_num⟩
    · exact ⟨1, 12, by norm_num, by norm_num⟩
    · exact ⟨3, 14, by norm_num, by norm_num⟩
  have hfin : (⋂ n ∈ ({12, 42} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num)).subset (Set.iInter₂_subset 12 (by simp))
  have h2 : ({1, 11} : Set ℕ).ncard = 2 := Set.ncard_pair (by norm_num)
  exact h2 ▸ Set.ncard_le_ncard hsub hfin

/--
Jiménez-Urroz [Ji99] proved this for $k=3$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{1936, 4900, 32400}, by decide, by decide, ?_⟩
  have hsub : ({0, 105, 480} : Set ℕ) ⊆
      ⋂ n ∈ ({1936, 4900, 32400} : Finset ℕ), factorDifferenceSet n := by
    simp only [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_iInter,
      Finset.mem_insert, Finset.mem_singleton]
    rintro d (rfl | rfl | rfl) n (rfl | rfl | rfl)
    · exact ⟨44, 44, by norm_num, by norm_num⟩
    · exact ⟨70, 70, by norm_num, by norm_num⟩
    · exact ⟨180, 180, by norm_num, by norm_num⟩
    · exact ⟨16, 121, by norm_num, by norm_num⟩
    · exact ⟨35, 140, by norm_num, by norm_num⟩
    · exact ⟨135, 240, by norm_num, by norm_num⟩
    · exact ⟨4, 484, by norm_num, by norm_num⟩
    · exact ⟨10, 490, by norm_num, by norm_num⟩
    · exact ⟨60, 540, by norm_num, by norm_num⟩
  have hfin : (⋂ n ∈ ({1936, 4900, 32400} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num)).subset (Set.iInter₂_subset 1936 (by simp))
  have h3 : ({0, 105, 480} : Set ℕ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, 105, 480, by norm_num, by norm_num, by norm_num, rfl⟩
  exact h3 ▸ Set.ncard_le_ncard hsub hfin

/--
Bremner [Br19] proved this for $k=4$.
-/
@[category research solved, AMS 11]
theorem erdos_885.variants.k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 4 := by
  sorry

end Erdos885
