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

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

@[expose] public section

namespace Nat

def partitionNumber : ℕ → ℕ := fun n ↦ Fintype.card (Nat.Partition n)

theorem partitionNumber_zero : partitionNumber 0 = 1 := by decide

theorem partitionNumber_one : partitionNumber 1 = 1 := by decide

-- TODO: shorter/faster proofs
/-- The only partitions of `2` are `2` and `1 + 1`. -/
lemma Partition.partition_two_parts (p : Partition 2) : p.parts = {2} ∨ p.parts = {1, 1} := by
  obtain ⟨s, hpos, hsum⟩ := p
  induction s using Multiset.induction_on with
  | empty => simp at hsum
  | cons a s _ =>
    have hs : ∀ {i}, i ∈ s → 0 < i := fun hi ↦ hpos (Multiset.mem_cons_of_mem hi)
    have ha : 0 < a := hpos (Multiset.mem_cons_self a s)
    rw [Multiset.sum_cons] at hsum
    obtain rfl | rfl : a = 1 ∨ a = 2 := by omega
    · obtain rfl : s = {1} := partition_one_parts ⟨s, hs, by omega⟩
      exact .inr rfl
    · obtain rfl : s = 0 := partition_zero_parts ⟨s, hs, by omega⟩
      exact .inl rfl

theorem partitionNumber_two : partitionNumber 2 = 2 := by
  rw [partitionNumber, Fintype.card, Finset.card_eq_two]
  refine ⟨⟨{2}, by simp, rfl⟩, ⟨{1, 1}, by simp, rfl⟩, by simp [Partition.ext_iff], ?_⟩
  ext p
  simpa [Partition.ext_iff] using p.partition_two_parts

end Nat
