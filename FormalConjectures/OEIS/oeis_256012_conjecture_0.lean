/-
Copyright 2026 Google LLC

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

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option maxHeartbeats 200000




open Nat Finset

/--
A256012: Number of partitions of $n$ into distinct parts that are not squarefree.
This is the number of finite subsets of positive integers $P$ such that $\sum_{k \in P} k = n$ and every element $k \in P$ is not squarefree.
-/
def A256012 (n : ℕ) : ℕ :=
  -- The parts must be $\le n$ to sum to $n$.
  -- This is $\{1, 2, \dots, n\}$
  let potential_parts : Finset ℕ := range (n + 1) \ {0}

  -- We count all subsets P of potential_parts that satisfy the sum and the property.
  card <| filter (fun P : Finset ℕ =>
    P.sum id = n ∧
    (∀ k ∈ P, ¬ Squarefree k)
  ) (powerset potential_parts)

open MeasureTheory

open Polynomial

open scoped BigOperators

open scoped Classical

open scoped ENNReal

open scoped EuclideanGeometry

open scoped InnerProductSpace

open scoped intervalIntegral

open scoped List

open scoped Matrix

open scoped Nat

open scoped NNReal

open scoped Pointwise

open scoped ProbabilityTheory

open scoped Real

open scoped symmDiff

open scoped Topology

-- EVOLVE-BLOCK-START
lemma not_squarefree_of_dvd_sq (k x : ℕ) (hx : x > 1) (h : x * x ∣ k) : ¬ Squarefree k := by
  intro hsq
  have h_unit := hsq x h
  have h_eq_one : x = 1 := Nat.isUnit_iff.mp h_unit
  omega

lemma not_squarefree_of_mod_4_eq_0 (k : ℕ) (h : k % 4 = 0) : ¬ Squarefree k := by
  apply not_squarefree_of_dvd_sq k 2 (by omega)
  exact Nat.dvd_of_mod_eq_zero h

lemma not_sq_9 : ¬ Squarefree 9 := by
  apply not_squarefree_of_dvd_sq 9 3 (by omega)
  norm_num

lemma not_sq_18 : ¬ Squarefree 18 := by
  apply not_squarefree_of_dvd_sq 18 3 (by omega)
  norm_num

lemma not_sq_27 : ¬ Squarefree 27 := by
  apply not_squarefree_of_dvd_sq 27 3 (by omega)
  norm_num
-- EVOLVE-BLOCK-END


theorem target_theorem_0
  (n : ℕ) (hn : n > 23) : A256012 n > 0 := by
  -- EVOLVE-BLOCK-START
  rw [A256012]
  apply Finset.card_pos.mpr
  have h_cases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h_cases with h0 | h1 | h2 | h3
  · use {n}
    simp only [mem_filter, mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [mem_singleton] at hx
      subst hx
      simp [mem_sdiff, mem_range]
      omega
    · simp only [sum_singleton, id_eq]
    · intro k hk
      simp only [mem_singleton] at hk
      subst hk
      exact not_squarefree_of_mod_4_eq_0 k h0
  · use {9, n - 9}
    simp only [mem_filter, mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [mem_sdiff, mem_range]
        omega
      · simp [mem_sdiff, mem_range]
        omega
    · have h_distinct : 9 ∉ ({n - 9} : Finset ℕ) := by
        simp only [mem_singleton]
        intro h
        omega
      rw [sum_insert h_distinct, sum_singleton]
      simp only [id_eq]
      omega
    · intro k hk
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact not_sq_9
      · apply not_squarefree_of_mod_4_eq_0
        omega
  · use {18, n - 18}
    simp only [mem_filter, mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [mem_sdiff, mem_range]
        omega
      · simp [mem_sdiff, mem_range]
        omega
    · have h_distinct : 18 ∉ ({n - 18} : Finset ℕ) := by
        simp only [mem_singleton]
        intro h
        omega
      rw [sum_insert h_distinct, sum_singleton]
      simp only [id_eq]
      omega
    · intro k hk
      simp only [mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact not_sq_18
      · apply not_squarefree_of_mod_4_eq_0
        omega
  · by_cases hn27 : n = 27
    · use {27}
      simp only [mem_filter, mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [mem_singleton] at hx
        subst hx
        simp [mem_sdiff, mem_range]
        omega
      · simp only [sum_singleton, id_eq]
        omega
      · intro k hk
        simp only [mem_singleton] at hk
        subst hk
        exact not_sq_27
    · use {27, n - 27}
      simp only [mem_filter, mem_powerset]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [mem_sdiff, mem_range]
          omega
        · simp [mem_sdiff, mem_range]
          omega
      · have h_distinct : 27 ∉ ({n - 27} : Finset ℕ) := by
          simp only [mem_singleton]
          intro h
          omega
        rw [sum_insert h_distinct, sum_singleton]
        simp only [id_eq]
        omega
      · intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact not_sq_27
        · apply not_squarefree_of_mod_4_eq_0
          omega
  -- EVOLVE-BLOCK-END
