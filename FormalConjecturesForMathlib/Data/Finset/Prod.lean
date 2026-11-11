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

public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Finset.Prod

/-!
# Counting strictly ordered pairs in a finset
-/

@[expose] public section

namespace Finset

/-- Twice the number of pairs `(a, b) ∈ A ×ˢ A` with `a < b` is `|A| * (|A| - 1)`. -/
theorem two_mul_card_product_filter_lt {β : Type*} [LinearOrder β] (A : Finset β) :
    2 * #{p ∈ A ×ˢ A | p.1 < p.2} = #A * (#A - 1) := by
  have h_swap : #{p ∈ A ×ˢ A | p.2 < p.1} = #{p ∈ A ×ˢ A | p.1 < p.2} :=
    card_equiv (.prodComm ..) (by simp [and_comm])
  have h_union : A.offDiag = {p ∈ A ×ˢ A | p.1 < p.2} ∪ {p ∈ A ×ˢ A | p.2 < p.1} := by
    ext ⟨a, b⟩
    simp only [mem_offDiag, mem_union, mem_filter, mem_product, ne_iff_lt_or_gt]
    tauto
  have h_disj : Disjoint {p ∈ A ×ˢ A | p.1 < p.2} {p ∈ A ×ˢ A | p.2 < p.1} :=
    disjoint_filter.2 fun _ _ h₁ h₂ ↦ absurd h₂ h₁.not_gt
  rw [Nat.mul_sub_one, ← A.offDiag_card, h_union, card_union_of_disjoint h_disj, h_swap, two_mul]

/-- Twice the number of pairs `(a, b) ∈ A ×ˢ A` with `b < a` is `|A| * (|A| - 1)`. -/
theorem two_mul_card_product_filter_gt {β : Type*} [LinearOrder β] (A : Finset β) :
    2 * #{p ∈ A ×ˢ A | p.2 < p.1} = #A * (#A - 1) := by
  rw [← two_mul_card_product_filter_lt]
  congr 1
  exact card_equiv (.prodComm ..) (by simp [and_comm])

end Finset
