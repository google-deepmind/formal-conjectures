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
# Erdős Problem 156

*References:*
- [erdosproblems.com/156](https://www.erdosproblems.com/156)
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
  Theory (1994), 329-347.
- [Ru98b] Ruzsa, Imre Z., A small maximal Sidon set. Ramanujan J. (1998), 55-58.
-/

open Finset Filter
open scoped Classical

namespace Erdos156
/--
The size of the smallest maximal Sidon set in $\{1, \dots, N\}$.
-/
noncomputable def minMaximalSidonSet (N : ℕ) : ℕ :=
  sInf (((Icc 1 N).powerset.filter fun (A : Finset ℕ) ↦
    Set.IsMaximalSidonSetIn (A : Set ℕ) N).image card : Set ℕ)

/--
Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?

A question of Erdős, Sárközy, and Sós [ESS94].
-/
@[category research open, AMS 5]
theorem erdos_156 :
    answer(sorry) ↔
      (fun N ↦ (minMaximalSidonSet N : ℝ)) =O[atTop] (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) := by
  sorry

@[category test, AMS 5]
theorem greedySidonSet_isSidon (n : ℕ) : IsSidon (Finset.greedySidonBelow n : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ eq
  have subset : Finset.greedySidonBelow n ⊆ (Finset.greedySidon.aux n).1 := Finset.filter_subset _ _
  exact (Finset.greedySidon.aux n).1.2 i₁ (subset hi₁) j₁ (subset hj₁) i₂ (subset hi₂) j₂ (subset hj₂) eq

/--
It is easy to prove that the greedy construction of a maximal Sidon set in $\{1,\ldots,N\}$ has size
$\gg N^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_156.variants.greedy_lower_bound :
    (fun N ↦ ((Finset.greedySidonBelow N).card : ℝ)) ≫ (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) := by
  sorry

/--
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N\log N)^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_156.variants.ruzsa_upper_bound :
    (fun N ↦ (minMaximalSidonSet N : ℝ)) ≪
      (fun N ↦ ((N : ℝ) * Real.log N) ^ (1 / 3 : ℝ)) := by
  sorry

end Erdos156
