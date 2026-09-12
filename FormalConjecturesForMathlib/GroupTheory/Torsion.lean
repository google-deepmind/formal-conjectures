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

public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

/-!
# Torsion-free monoids

This file defines `Monoid.IsTorsionFree G`, the predicate saying that `1` is the only element of
finite order in `G`.

Mathlib's `IsMulTorsionFree G` asks instead that `a ↦ a ^ n` be injective for every `n ≠ 0`
(uniqueness of roots). The two notions agree for commutative groups
(`isMulTorsionFree_iff_not_isOfFinOrder`), but for noncommutative groups `IsMulTorsionFree` is
strictly stronger: the Klein bottle group `⟨a, b | b⁻¹ab = a⁻¹⟩` is torsion-free, yet
`(ab)² = b²` with `ab ≠ b`. Statements about torsion-free groups in the literature, such as
Kaplansky's conjectures on group rings, use the weaker notion defined here.

TODO(mo271): refactor after https://github.com/leanprover-community/mathlib4/pull/43727 lands
-/

variable {G : Type*}

/-- A predicate on a monoid saying that only `1` has finite order. -/
@[to_additive /-- A predicate on an additive monoid saying that only `0` has finite order. -/]
def Monoid.IsTorsionFree (G : Type*) [Monoid G] : Prop :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g

namespace Monoid.IsTorsionFree

variable [Monoid G]

@[to_additive]
theorem eq_one_of_isOfFinOrder (hG : Monoid.IsTorsionFree G) {g : G} (hg : IsOfFinOrder g) :
    g = 1 :=
  by_contra fun h ↦ hG g h hg

@[to_additive]
theorem isOfFinOrder_iff_eq_one (hG : Monoid.IsTorsionFree G) {g : G} :
    IsOfFinOrder g ↔ g = 1 :=
  ⟨hG.eq_one_of_isOfFinOrder, fun h ↦ h ▸ IsOfFinOrder.one⟩

end Monoid.IsTorsionFree

@[to_additive]
theorem Monoid.isTorsionFree_iff_forall_isOfFinOrder_imp_eq_one [Monoid G] :
    Monoid.IsTorsionFree G ↔ ∀ g : G, IsOfFinOrder g → g = 1 :=
  ⟨fun hG _ ↦ hG.eq_one_of_isOfFinOrder, fun h g hg hfin ↦ hg (h g hfin)⟩

/-- Uniqueness of roots implies torsion-freeness. -/
@[to_additive /-- Uniqueness of roots implies torsion-freeness. -/]
theorem Monoid.IsTorsionFree.of_isMulTorsionFree [Monoid G] [IsMulTorsionFree G] :
    Monoid.IsTorsionFree G :=
  fun _ hg ↦ not_isOfFinOrder_of_isMulTorsionFree hg

/-- For commutative groups, torsion-freeness is equivalent to uniqueness of roots. -/
@[to_additive /-- For additive commutative groups, torsion-freeness is equivalent to uniqueness
of roots. -/]
theorem Monoid.isTorsionFree_iff_isMulTorsionFree [CommGroup G] :
    Monoid.IsTorsionFree G ↔ IsMulTorsionFree G :=
  isMulTorsionFree_iff_not_isOfFinOrder.symm
