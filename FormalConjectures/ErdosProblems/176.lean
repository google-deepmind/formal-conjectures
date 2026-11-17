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
module

public import FormalConjecturesUtil


/-!
# Erdős Problem 176

*References:*
- [erdosproblems.com/176](https://www.erdosproblems.com/176)
-/

@[expose] public section

open Nat
open BigOperators

namespace Erdos176


-- Check wether a k-term arithmetic progression with first term `a` and common difference `d` is contained in the set `{1, 2, ..., N}`.
def IsProgressionInNSet (a d k N : ℕ) : Prop :=
  0 < d ∧
  ∀ i ∈ Finset.range k, 1 ≤ a + i * d ∧ a + i * d ≤ N

-- Check wether a function `f : ℕ → {-1, 1}` satisfies the property of Erdős Problem 176 for given parameters `k`, `l`, and `N`. Subproblems are formulated as special cases of l (see a few below), some of which are solved but far from all.
def Erdos176Property (k l N : ℕ) : Prop :=
  1 ≤ N ∧
  ∀ f : ℕ → ℤ,
    (∀ n, 1 ≤ n → n ≤ N → f n = -1 ∨ f n = 1) →
      ∃ a d : ℕ,
        IsProgressionInNSet a d k N ∧ |∑ i ∈ Finset.range k, f (a + i * d)| ≥ l

-- Note that such an N does not necessarily exist for all k and l. For l > k, |∑ i in Finset.range k, f (a + i * d)| can never be greater than k, so the property is false for all N in that case. Therefore we restrict to l ≤ k
lemma Erdos176Property_N_existence (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
  ∃ N, Erdos176Property k l N :=
  by
  sorry

-- Define the minimal N (for given k and l) for which the property above holds (provided such an N exists by the lemma above).
noncomputable def N (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) : ℕ := by
  classical exact Nat.find (Erdos176Property_N_existence k l hl hlk)

-- Minimum exists and has the property
lemma N_spec (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
  Erdos176Property k l (N k l hl hlk) := by
  classical exact Nat.find_spec (Erdos176Property_N_existence k l hl hlk)

-- If m satisfies the property, then N is less than or equal to m
lemma N_min (k l m : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k)
  (hm : Erdos176Property k l m) :
  N k l hl hlk ≤ m := by
  classical exact Nat.find_min' (Erdos176Property_N_existence k l hl hlk) hm


-- Exponential upper bound for N(k, 2) (for k ≥ 2)
@[category research open, question, AMS 11]
theorem erdos_176_l_equals_2 : ∃ C : ℕ, 1 < C ∧ ∀ k, (hk : 2 ≤ k) →
  N k 2 (by norm_num) hk
  ≤ C ^ k := by
  sorry

-- Exponential upper bound for N(k, √k) (for k ≥ 1)
@[category research open, question, AMS 11]
theorem erdos_176_l_equals_sqrtk : ∃ C : ℕ, 1 < C ∧ ∀ k, (hk : 1 ≤ k) →
  N k (Nat.sqrt k)
    (by
      rw [Nat.le_sqrt]
      omega)
    (by exact Nat.sqrt_le_self k)
    ≤ C ^ k := by
  sorry

end Erdos176

end
