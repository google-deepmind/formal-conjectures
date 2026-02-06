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
import FormalConjecturesForMathlib.Order.Filter.Cofinite
import FormalConjecturesForMathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

open Filter
open scoped Pointwise

namespace Set
variable {M : Type*} [CommMonoid M] {A : Set M} {m n : ℕ}

/-- A set `A : Set M` is a multiplicative basis of order `n` if any element `a : M`
can be expressed as a product of `n` elements lying in `A`. -/
@[to_additive
/-- A set `A : Set M` is an additive basis of order `n` if for any element
`a : M`, it can be expressed as a sum of `n` elements lying in `A`. -/]
def IsMulBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, a ∈ A ^ n

/-- A multiplicative basis of some order. -/
@[to_additive /-- An additive basis of some order. -/]
def IsMulBasis (A : Set M) : Prop := ∃ n, A.IsMulBasisOfOrder n

@[to_additive]
lemma IsMulBasisOfOrder.isMulBasis (hA : A.IsMulBasisOfOrder n) : A.IsMulBasis := ⟨n, hA⟩

@[to_additive]
lemma isMulBasisOfOrder_iff :
    A.IsMulBasisOfOrder n ↔ ∀ a, ∃ (f : Fin n → M) (_ : ∀ i, f i ∈ A), ∏ i, f i = a := by
  have := Set.mem_finset_prod (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsMulBasisOfOrder]

/-- No set is a multiplicative basis of order `0`. -/
@[to_additive (attr := simp) /-- No set is an additive basis of order `0`. -/]
lemma not_isMulBasisOfOrder_zero [Nontrivial M] : ¬A.IsMulBasisOfOrder 0 := by
  simp [isMulBasisOfOrder_iff, eq_comm, exists_ne]

@[to_additive (attr := simp)]
lemma isMulBasisOfOrder_one_iff : A.IsMulBasisOfOrder 1 ↔ A = univ := by
  simp [IsMulBasisOfOrder, eq_univ_iff_forall]

/-- A set `A : Set M` is a multiplicative basis of order `2` if every `a : M` belongs to `A * A`. -/
@[to_additive
/-- A set `A : Set M` is an additive basis of order `2` if every `a : M` belongs to `A + A`. -/]
lemma isMulBasisOfOrder_two_iff : A.IsMulBasisOfOrder 2 ↔ ∀ a, a ∈ A * A := by
  simp [IsMulBasisOfOrder, pow_two]

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if the elements that can
be expressed as a product of `n` elements lying in `A` is cofinite. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if the elements that
can be expressed as a sum of `n` elements lying in `A` is cofinite. -/]
def IsAsymptoticMulBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ᶠ a in cofinite, a ∈ A ^ n

/-- An asymptotic multiplicative basis of some order. -/
@[to_additive /-- An asymptotic additive basis of some order. -/]
def IsAsymptoticMulBasis (A : Set M) : Prop := ∃ n, A.IsAsymptoticMulBasisOfOrder n

@[to_additive]
lemma IsAsymptoticMulBasisOfOrder.isAsymptoticMulBasis (hA : A.IsAsymptoticMulBasisOfOrder n) :
    A.IsAsymptoticMulBasis := ⟨n, hA⟩

@[to_additive]
lemma IsMulBasisOfOrder.isAsymptoticMulBasisOfOrder (hA : IsMulBasisOfOrder A n) :
    A.IsAsymptoticMulBasisOfOrder n := .of_forall hA

@[to_additive]
lemma IsMulBasis.isAsymptoticMulBasis (hA : IsMulBasis A) : A.IsAsymptoticMulBasis := by
  obtain ⟨n, hn⟩ := hA; exact ⟨n, hn.isAsymptoticMulBasisOfOrder⟩

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if a cofinite set of
`a : M` can be written as `a = a₁ * ... * aₙ`, where each `aᵢ ∈ A`. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if a cofinite set of
`a : M` can be written as `a = a₁ + ... + aₙ`, where each `aᵢ ∈ A`. -/]
lemma isAsymptoticMulBasisOfOrder_iff_prod :
    IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in cofinite, ∃ (f : Fin n → M) (_ : ∀ i, f i ∈ A),
      ∏ i, f i = a := by
  have := Set.mem_finset_prod (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsAsymptoticMulBasisOfOrder]

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `2` if a cofinite set of
`a : M` belongs to `A * A`. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `2` if a cofinite set of
`a : M` belongs to `A + A`. -/]
lemma isAsymptoticMulBasisOfOrder_two_iff :
    IsAsymptoticMulBasisOfOrder A 2 ↔ ∀ᶠ a in cofinite, a ∈ A * A := by
  simp [IsAsymptoticMulBasisOfOrder, pow_two]

@[to_additive (attr := simp)]
protected lemma IsAsymptoticMulBasisOfOrder.of_finite [Finite M] :
    IsAsymptoticMulBasisOfOrder A n := by simp [IsAsymptoticMulBasisOfOrder]

/-- If `M` is infinite, then no set `A` is an asymptotic multiplicative basis of order `0`. -/
@[to_additive (attr := simp)
/-- If `M` is infinite, then no set `A` is an asymptotic additive basis of order `0`. -/]
lemma not_isAsymptoticMulBasisOfOrder_zero [Infinite M] : ¬IsAsymptoticMulBasisOfOrder A 0 := by
  simpa [IsAsymptoticMulBasisOfOrder, ← not_infinite] using Set.infinite_of_finite_compl (by simp)

@[to_additive]
protected lemma IsAsymptoticMulBasisOfOrder.ne_zero [Infinite M]
    (hA : IsAsymptoticMulBasisOfOrder A n) : n ≠ 0 := by rintro rfl; simp at hA

@[to_additive]
protected lemma IsAsymptoticMulBasisOfOrder.nonempty [Infinite M]
    (hA : A.IsAsymptoticMulBasisOfOrder n) : A.Nonempty := by
  by_contra!
  simp [this, IsAsymptoticMulBasisOfOrder, hA.ne_zero, finite_univ_iff,
    _root_.Infinite.not_finite] at hA

/-- `A : Set M` is an asymptotic basis of order one iff it is cofinite. -/
@[to_additive (attr := simp)
/--`A : Set M` is an asymptotic basis of order one iff it is cofinite. -/]
lemma isAsymptoticMulBasisOfOrder_one_iff : IsAsymptoticMulBasisOfOrder A 1 ↔ Aᶜ.Finite := by
  simp [IsAsymptoticMulBasisOfOrder, compl_def]

variable [LinearOrder M] [LocallyFiniteOrder M] [OrderBot M]

@[to_additive]
lemma IsAsymptoticMulBasisOfOrder.mono [CanonicallyOrderedMul M] [IsCancelMul M] (hmn : m ≤ n)
    (hA : A.IsAsymptoticMulBasisOfOrder m) : A.IsAsymptoticMulBasisOfOrder n := by
  cases finite_or_infinite M
  · simp
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hmn
  refine ((hA.smul_set (a := a ^ n)).union <| finite_Iio <| a ^ n).subset ?_
  have : a ^ n • (A ^ m)ᶜ = (a ^ n • A ^ m)ᶜ \ Iio (a ^ n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa
    · simp only [mem_diff, mem_compl_iff, mem_smul_set, smul_eq_mul, not_exists, not_and, mem_Iio,
        not_lt, le_iff_exists_mul, and_imp, forall_exists_index]
      rintro hx y rfl
      exact ⟨y, fun hy ↦ hx _ hy rfl, rfl⟩
  simp only [m.add_comm, pow_add, setOf_mem_eq, this, diff_union_self, subset_def, mem_compl_iff,
    mem_union, mem_Iio]
  rintro b hb
  contrapose! hb
  exact smul_set_subset_mul (pow_mem_pow ha) hb.1

/-- For `M` equipped with a directed order, a set is an asymptotic multiplicative basis of order `1`
if it contains an infinite tail of elements. -/
@[to_additive
/-- For `M` equipped with a directed order, a set is an asymptotic additive basis of order `1`
if it contains an infinite tail of consecutive naturals. -/]
lemma isAsymptoticMulBasisOfOrder_one_iff_Ioi :
    IsAsymptoticMulBasisOfOrder A 1 ↔ ∃ a, .Ioi a ⊆ A := by
  simp [IsAsymptoticMulBasisOfOrder, cofinite_hasBasis_Ioi.eventually_iff, Set.subset_def]

variable [SuccOrder M] [NoMaxOrder M]

/-- For `M` equipped with a directed order, a set is an asymptotic multiplicative basis of order `1`
if it contains an infinite tail of elements. -/
@[to_additive
/-- For `M` equipped with a directed order, a set is an asymptotic additive basis of order `1`
if it contains an infinite tail of consecutive naturals. -/]
lemma isAsymptoticMulBasisOfOrder_one_iff_Ici :
      IsAsymptoticMulBasisOfOrder A 1 ↔ ∃ a, .Ici a ⊆ A := by
  simp [IsAsymptoticMulBasisOfOrder, cofinite_hasBasis_Ici.eventually_iff, Set.subset_def]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_atTop :
      IsAsymptoticMulBasisOfOrder A n ↔ ∀ᶠ a in atTop, a ∈ A ^ n := by
  rw [IsAsymptoticMulBasisOfOrder, cofinite_eq_atTop]

@[to_additive]
lemma isAsymptoticMulBasisOfOrder_iff_prod_atTop :
    IsAsymptoticMulBasisOfOrder A n ↔
      ∀ᶠ a in atTop, ∃ f : Fin n → M, (∀ i, f i ∈ A) ∧ ∏ i, f i = a := by
  simp [isAsymptoticMulBasisOfOrder_iff_prod, cofinite_eq_atTop]

end Set
