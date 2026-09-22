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

public import Mathlib.ModelTheory.Definability
public import Mathlib.ModelTheory.Order

/-!
# O-minimal structures

A structure `M` in a language `L` containing the order symbol `≤` is *o-minimal* if `≤` is
interpreted as a linear order on `M` and every subset of `M` definable with parameters is a
finite union of points and open intervals with endpoints in `M ∪ {-∞, +∞}`.

*References:*
- A. Pillay, C. Steinhorn, *Definable sets in ordered structures. I*,
  Trans. Amer. Math. Soc. 295 (1986), 565–592.
- L. van den Dries, *Tame topology and o-minimal structures*, London Mathematical Society
  Lecture Note Series 248, Cambridge University Press, 1998.

## Main declarations

- `Set.IsPointOrOpenInterval`: a subset of a preorder is a singleton or an open interval,
  possibly unbounded.
- `FirstOrder.Language.IsOMinimal`: o-minimal structures.
- `FirstOrder.Language.IsOMinimal.exists_finite_ordConnected`: in an o-minimal structure, every
  definable subset is a finite union of order-connected sets.

## Implementation notes

Finite unions are expressed through `Set.Finite` on a set of subsets, rather than a `Finset`, so
that no decidable equality on `Set M` is needed to write one down. The order is not required to
be dense or to have no endpoints, following Pillay and Steinhorn.
-/

@[expose] public section

namespace Set

variable {M : Type*} [Preorder M]

/-- A subset `s` of a preorder is a *point or an open interval* if it is a singleton `{a}` or one
of the open intervals `Ioo a b`, `Iio b`, `Ioi a` and `univ`. -/
def IsPointOrOpenInterval (s : Set M) : Prop :=
  (∃ a, s = {a}) ∨ (∃ a b, s = Ioo a b) ∨ (∃ b, s = Iio b) ∨ (∃ a, s = Ioi a) ∨ s = univ

theorem isPointOrOpenInterval_singleton (a : M) : ({a} : Set M).IsPointOrOpenInterval :=
  Or.inl ⟨a, rfl⟩

theorem isPointOrOpenInterval_Ioo (a b : M) : (Ioo a b).IsPointOrOpenInterval :=
  Or.inr (Or.inl ⟨a, b, rfl⟩)

theorem isPointOrOpenInterval_Iio (b : M) : (Iio b).IsPointOrOpenInterval :=
  Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))

theorem isPointOrOpenInterval_Ioi (a : M) : (Ioi a).IsPointOrOpenInterval :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨a, rfl⟩)))

theorem isPointOrOpenInterval_univ : (univ : Set M).IsPointOrOpenInterval :=
  Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- In a partial order, a point or an open interval is order-connected. -/
theorem IsPointOrOpenInterval.ordConnected {M : Type*} [PartialOrder M] {s : Set M}
    (hs : s.IsPointOrOpenInterval) : s.OrdConnected := by
  rcases hs with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩ | rfl <;> infer_instance

-- A closed ray is a finite union of points and open intervals, as o-minimality requires of every
-- definable set.
example {M : Type*} [PartialOrder M] (a : M) :
    ∃ F : Set (Set M), F.Finite ∧ (∀ t ∈ F, t.IsPointOrOpenInterval) ∧ Ici a = ⋃₀ F := by
  refine ⟨{{a}, Ioi a}, Set.toFinite _, ?_, ?_⟩
  · simp [isPointOrOpenInterval_singleton, isPointOrOpenInterval_Ioi]
  · rw [Set.sUnion_insert, Set.sUnion_singleton, Set.singleton_union, Set.Ioi_insert]

end Set

namespace FirstOrder.Language

/-- An `L`-structure `M` on a linearly ordered set, where `L` contains the symbol `≤`, is
*o-minimal* if `≤` is interpreted as the order of `M` and every subset of `M` definable with
parameters is a finite union of points and open intervals.

We do not require the order to be dense or to have no endpoints. -/
class IsOMinimal (L : Language) (M : Type*) [LinearOrder M] [L.IsOrdered] [L.Structure M] :
    Prop extends L.OrderedStructure M where
  exists_finite_of_definable : ∀ s : Set M, (Set.univ : Set M).Definable₁ L s →
    ∃ F : Set (Set M), F.Finite ∧ (∀ t ∈ F, t.IsPointOrOpenInterval) ∧ s = ⋃₀ F

variable {L : Language} {M : Type*} [LinearOrder M] [L.IsOrdered] [L.Structure M]

/-- In an o-minimal structure, every definable subset is a finite union of order-connected
sets. -/
theorem IsOMinimal.exists_finite_ordConnected [L.IsOMinimal M] {s : Set M}
    (hs : (Set.univ : Set M).Definable₁ L s) :
    ∃ F : Set (Set M), F.Finite ∧ (∀ t ∈ F, t.OrdConnected) ∧ s = ⋃₀ F := by
  obtain ⟨F, hF, hF', rfl⟩ := IsOMinimal.exists_finite_of_definable s hs
  exact ⟨F, hF, fun t ht => (hF' t ht).ordConnected, rfl⟩

end FirstOrder.Language
