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

import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import FormalConjectures.ForMathlib.Order.Filter.Cofinite

open Filter

open scoped Pointwise

namespace Set

variable {α} [CommMonoid α]

section MulBasis

/--
A set `A : Set α` is a multiplicative basis of order `n` if for any element
`a : α`, it can be expressed as a product of `n` elements lying in `A`.
-/
@[to_additive
/--
A set `A : Set α` is an additive basis of order `n` if for any element
`a : α`, it can be expressed as a sum of `n` elements lying in `A`.
-/]
abbrev IsMulBasisOfOrder (A : Set α) (n : ℕ) : Prop :=
    ∀ a, a ∈ A ^ n

/--
A multiplicative basis of some order.
-/
@[to_additive
/--
An additive basis of some order.
-/]
abbrev IsMulBasis (A : Set α) : Prop :=
    ∃ n, A.IsMulBasisOfOrder n

@[to_additive]
theorem IsMulBasisOfOrder.toMulBasis {A : Set α} {n : ℕ} (hA : A.IsMulBasisOfOrder n) :
    A.IsMulBasis := ⟨n, hA⟩

@[to_additive]
theorem isMulBasisOfOrder_iff (A : Set α) (n : ℕ) : A.IsMulBasisOfOrder n ↔
    ∀ a, ∃ (f : Fin n → α) (_ : ∀ i, f i ∈ A), ∏ i, f i = a := by
  have := Set.mem_finset_prod (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsMulBasisOfOrder]

/-- A set `A : Set α` is a multiplicative basis of order `2` if every `a : α` belongs to `A + A`. -/
@[to_additive
/--
A set `A : Set α` is an additive basis of order `2` if every `a : α` belongs to `A + A`.
-/]
theorem isMulBasisOfOrder_two_iff (A : Set α) :
    A.IsMulBasisOfOrder 2 ↔ ∀ a, a ∈ A * A := by
  simp [IsMulBasisOfOrder, pow_two]

/-- No set is a multiplicative basis of order `0`. -/
@[to_additive
/--
No set is an additive basis of order `0`.
-/]
theorem not_isMulBasisOfOrder_zero [Nontrivial α] [DecidableEq α] (A : Set α) :
    ¬A.IsMulBasisOfOrder 0 := by
  simp [isMulBasisOfOrder_iff, eq_comm]
  apply Decidable.exists_ne

@[to_additive]
theorem isMulBasisOfOrder_one_iff (A : Set α) :
    A.IsMulBasisOfOrder 1 ↔ A = univ := by
  simp [IsMulBasisOfOrder, eq_univ_iff_forall]

end MulBasis

section AsymptoticMulBasis

/--
A set `A : Set α` is an asymptotic multiplicative basis of order `n` if the elements that can
be expressed as a product of `n` elements lying in `A` is cofinite.
-/
@[to_additive
/--
A set `A : Set α` is an asymptotic additive basis of order `n` if the elements that
can be expressed as a sum of `n` elements lying in `A` is cofinite.
-/]
abbrev IsAsymptoticMulBasisOfOrder (A : Set α) (n : ℕ) : Prop :=
    ∀ᶠ a in cofinite, a ∈ A ^ n

/--
An asymptotic multiplicative basis of some order.
-/
@[to_additive
/--
An asymptotic additive basis of some order.
-/]
abbrev IsAsymptoticMulBasis (A : Set α) : Prop :=
    ∃ n, A.IsAsymptoticMulBasisOfOrder n

@[to_additive]
theorem IsAsymptoticMulBasisOfOrder.toIsAsymptoticMulBasis {A : Set α} {n : ℕ}
    (hA : A.IsAsymptoticMulBasisOfOrder n) : A.IsAsymptoticMulBasis :=
  ⟨n, hA⟩

@[to_additive]
theorem IsMulBasisOfOrder.toIsAsymptoticMulBasisOfOrder {A : Set α} {n : ℕ}
    (hA : IsMulBasisOfOrder A n) : A.IsAsymptoticMulBasisOfOrder n :=
  Eventually.of_forall hA

@[to_additive]
theorem IsMulBasis.toIsAsymptoticMulBasis {A : Set α} (hA : IsMulBasis A) :
    A.IsAsymptoticMulBasis := by
  obtain ⟨n, hn⟩ := hA
  exact ⟨n, Eventually.of_forall hn⟩

/--
A set `A : Set α` is an asymptotic multiplicative basis of order `n` if a cofinite set of
`a : α` can be written as `a = a₁ * ... * aₙ`, where each `aᵢ ∈ A`.
-/
@[to_additive
/--A set `A : Set α` is an asymptotic additive basis of order `n` if a cofinite set of
`a : α` can be written as `a = a₁ + ... + aₙ`, where each `aᵢ ∈ A`.
-/]
theorem isAsymptoticMulBasisOfOrder_iff_prod (A : Set α) (n : ℕ) :
    IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in cofinite, ∃ (f : Fin n → α) (_ : ∀ i, f i ∈ A),
      ∏ i, f i = a := by
  have := Set.mem_finset_prod (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsAsymptoticMulBasisOfOrder]

/--
A set `A : Set α` is an asymptotic multiplicative basis of order `2` if a cofinite set of
`a : α` belongs to `A * A`.
-/
@[to_additive
/--
A set `A : Set α` is an asymptotic additive basis of order `2` if a cofinite set of
`a : α` belongs to `A + A`.
-/]
theorem isAsymptoticMulBasisOfOrder_two_iff (A : Set α) :
    IsAsymptoticMulBasisOfOrder A 2 ↔ ∀ᶠ a in cofinite, a ∈ A * A := by
  simp [pow_two]

/-- If `α` is infinite, then no set `A` is an asymptotic multiplicative basis of order `0`. -/
@[to_additive
/--
If `α` is infinite, then no set `A` is an asymptotic additive basis of order `0`.
-/]
theorem not_isAsymptoticMulBasisOfOrder_zero [Infinite α] (A : Set α) :
    ¬IsAsymptoticMulBasisOfOrder A 0 := by
  simp only [eventually_cofinite, pow_zero, mem_one, ← not_infinite, not_not]
  apply Set.infinite_of_finite_compl
  simp


/-- `A : Set α` is an asymptotic basis of order one iff it is cofinite. -/
@[to_additive /--`A : Set α` is an asymptotic basis of order one iff it is cofinite.-/]
theorem isAsymptoticMulBasisOfOrder_one_iff (A : Set α) :
    IsAsymptoticMulBasisOfOrder A 1 ↔ Aᶜ.Finite := by
  simp only [eventually_cofinite, pow_one]
  rfl

/--
For `α` equipped with a directed order, a set is an asymptotic multiplicative basis of order `1`
if it contains an infinite tail of elements.
-/
@[to_additive
/--
For `α` equipped with a directed order, a set is an asymptotic additive basis of order `1`
if it contains an infinite tail of consecutive naturals.
-/]
theorem isAsymptoticMulBasisOfOrder_one_iff_Ioi [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    (A : Set α) : IsAsymptoticMulBasisOfOrder A 1 ↔ ∃ a, Set.Ioi a ⊆ A := by
  simp [Filter.HasBasis.eventually_iff cofinite_hasBasis_Ioi, Set.subset_def]

/-- For `α` equipped with a directed order, a set is an asymptotic multiplicative basis of order `1`
if it contains an infinite tail of elements.
-/
@[to_additive
/--
For `α` equipped with a directed order, a set is an asymptotic additive basis of order `1`
if it contains an infinite tail of consecutive naturals.
-/]
theorem isAsymptoticMulBasisOfOrder_one_iff_Ici [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    [SuccOrder α] [NoMaxOrder α] (A : Set α) :
      IsAsymptoticMulBasisOfOrder A 1 ↔ ∃ a, Set.Ici a ⊆ A := by
  simp [Filter.HasBasis.eventually_iff cofinite_hasBasis_Ici, Set.subset_def]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_atTop [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    [SuccOrder α] [NoMaxOrder α] (A : Set α) (n : ℕ) :
      IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in atTop, a ∈ A ^ n := by
  rw [IsAsymptoticMulBasisOfOrder, cofinite_eq_atTop]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_prod_atTop [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    [SuccOrder α] [NoMaxOrder α] (A : Set α) (n : ℕ) :
      IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in atTop, ∃ (f : Fin n → α) (_ : ∀ i, f i ∈ A),
        ∏ i, f i = a := by
  rw [isAsymptoticMulBasisOfOrder_iff_prod, cofinite_eq_atTop]

end AsymptoticMulBasis

end Set
