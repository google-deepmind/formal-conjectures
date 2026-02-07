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
import Mathlib.Combinatorics.SimpleGraph.Basic
import FormalConjecturesForMathlib.Data.Finset.Card

open Finset

namespace SimpleGraph
variable {n k : ℕ}

/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k - 1$.
-/
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm s t h := by simpa [inter_comm]
  loopless := by simp +contextual [Irreflexive]

scoped notation "J(" n ", " k ")" => johnson n k

lemma johnson_adj_iff_ge {s t : {s : Finset (Fin n) // #s = k}} :
    J(n, k).Adj s t ↔ s ≠ t ∧ k ≤ #(s.val ∩ t.val) + 1 := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only [johnson_adj, le_antisymm_iff (α := ℕ), ne_eq, Subtype.mk.injEq, and_congr_left_iff]
  rintro h
  constructor
  · rintro hst rfl
    simp at hst
    omega
  · rintro hst
    rw [Nat.add_one_le_iff, ← hs, card_lt_card_iff_of_subset inter_subset_left]
    simp only [ne_eq, inter_eq_left]
    contrapose! hst
    exact eq_of_subset_of_card_le hst (by simp [*])

lemma not_johnson_adj_iff_lt {s t : {s : Finset (Fin n) // #s = k}} :
    ¬ J(n, k).Adj s t ↔ s = t ∨ #(s.val ∩ t.val) + 1 < k := by simp [johnson_adj_iff_ge]; tauto

end SimpleGraph
