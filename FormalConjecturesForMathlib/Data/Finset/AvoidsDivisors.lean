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

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Divisibility.Basic

@[expose] public section

namespace Finset

/-- The integers in `{1, …, x}` not divisible by any element of `A`. -/
def avoidsDivisors (A : Finset ℕ) (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun m => ∀ a ∈ A, ¬ a ∣ m)

@[simp]
lemma mem_avoidsDivisors {A : Finset ℕ} {x m : ℕ} :
    m ∈ avoidsDivisors A x ↔ m ∈ Icc 1 x ∧ ∀ a ∈ A, ¬ a ∣ m := by
  simp [avoidsDivisors]

lemma avoidsDivisors_empty (x : ℕ) :
    avoidsDivisors ∅ x = Icc 1 x := by
  simp [avoidsDivisors]

/-- Enlarging the divisor set can only shrink the set of unsieved integers. -/
lemma avoidsDivisors_mono {A B : Finset ℕ} (h : A ⊆ B) (x : ℕ) :
    avoidsDivisors B x ⊆ avoidsDivisors A x := by
  intro m hm
  simp only [mem_avoidsDivisors] at hm ⊢
  exact ⟨hm.1, fun a ha ↦ hm.2 a (h ha)⟩

/-- If `1 ∈ A`, then every `m` is divisible by an element of `A`, so nothing survives. -/
lemma avoidsDivisors_eq_empty_of_one_mem {A : Finset ℕ} (h : 1 ∈ A) (x : ℕ) :
    avoidsDivisors A x = ∅ := by
  refine eq_empty_of_forall_notMem fun m hm ↦ ?_
  have hA : ∀ a ∈ A, ¬a ∣ m := (mem_avoidsDivisors.mp hm).2
  exact hA 1 h (one_dvd m)

/-- The unsieved set is a subset of `{1, …, x}`, so its cardinality is at most `x`. -/
lemma card_avoidsDivisors_le (A : Finset ℕ) (x : ℕ) :
    (avoidsDivisors A x).card ≤ x := by
  have hsub : avoidsDivisors A x ⊆ Icc 1 x := filter_subset _ _
  exact (card_le_card hsub).trans (by simp [Nat.card_Icc])

/-- Sieving by a union is the intersection of the two sifted sets. -/
lemma avoidsDivisors_union (A B : Finset ℕ) (x : ℕ) :
    avoidsDivisors (A ∪ B) x = avoidsDivisors A x ∩ avoidsDivisors B x := by
  ext m
  simp only [mem_avoidsDivisors, mem_union, mem_inter, or_imp, forall_and]
  tauto

/-- With an empty sieve, every integer in `{1, …, x}` survives. -/
@[simp]
lemma card_avoidsDivisors_empty (x : ℕ) : (avoidsDivisors ∅ x).card = x := by
  simp [avoidsDivisors_empty, Nat.card_Icc]

end Finset
