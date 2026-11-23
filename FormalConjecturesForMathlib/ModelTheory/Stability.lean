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

public import Mathlib.ModelTheory.Algebra.Ring.Basic

/-!
# Model-theoretic stability of structures and rings

In Shelah's classification program, stability of a complete theory `T` forbids partitioned
formulas `φ(x; y)` from exhibiting Shelah's *order property* across models of `T`, meaning no
model contains infinite sequences `(aᵢ)` and `(bⱼ)` realizing `φ(aᵢ; bⱼ)` precisely when `i ≤ j`.
For any fixed finite length `n` and finite tuple arities `m, k`, the existence of
`a : Fin n → Fin m → M` and `b : Fin n → Fin k → M` satisfying `φ(aᵢ; bⱼ) ↔ i ≤ j` is expressible
as a single first-order sentence of `L`. For nonempty `M`, compactness therefore makes absence of
infinite half-graphs in models of `L.completeTheory M` equivalent to every partitioned formula
`φ : L.Formula (Fin m ⊕ Fin k)` admitting a finite length bound `n` inside `M` itself.

## Main declarations

- `FirstOrder.Language.Formula.IsStableIn`: bounded half-graph ladder property of a partitioned
  formula `φ : L.Formula (α ⊕ β)` in an `L`-structure `M`.
- `FirstOrder.Language.IsStableStructure`: every finitely partitioned `L`-formula is stable in `M`.
- `FirstOrder.Ring.IsStableRing`: stability of a ring `R` in `FirstOrder.Language.ring`.

## References

- S. Shelah, *Classification Theory and the Number of Non-Isomorphic Models*, 2nd ed.,
  North-Holland, Amsterdam, 1990.
- K. Tent and M. Ziegler, *A Course in Model Theory*, Lecture Notes in Logic 40, Cambridge
  University Press, 2012, §8.2.
-/

@[expose] public section

namespace FirstOrder

namespace Language

/-- A partitioned formula `φ : L.Formula (α ⊕ β)` is *stable* in an `L`-structure `M` if there is
a finite bound `n` such that `M` contains no `n`-element half-graph defined by `φ`. -/
def Formula.IsStableIn {L : Language} {α β : Type*} (φ : L.Formula (α ⊕ β))
    (M : Type*) [L.Structure M] : Prop :=
  ∃ n : ℕ, ¬ ∃ (a : Fin n → α → M) (b : Fin n → β → M),
    ∀ i j : Fin n, φ.Realize (Sum.elim (a i) (b j)) ↔ i ≤ j

/-- An `L`-structure `M` is *model-theoretically stable* if every finitely partitioned formula
`φ : L.Formula (Fin m ⊕ Fin k)` is stable in `M`. For nonempty `M`, compactness implies that this
holds if and only if `L.completeTheory M` admits no formula with Shelah's order property. -/
def IsStableStructure (L : Language) (M : Type*) [L.Structure M] : Prop :=
  ∀ (m k : ℕ) (φ : L.Formula (Fin m ⊕ Fin k)), φ.IsStableIn M

open scoped Classical in
/-- Over a finite carrier `M` and finite tuple index `α`, every partitioned formula `φ` is stable
in `M` by the pigeonhole principle on `α → M`. -/
theorem Formula.IsStableIn.of_finite {L : Language} {α β : Type*} [Finite α]
    (φ : L.Formula (α ⊕ β)) (M : Type*) [L.Structure M] [Finite M] :
    φ.IsStableIn M := by
  cases nonempty_fintype α
  cases nonempty_fintype M
  refine ⟨Fintype.card (α → M) + 1, ?_⟩
  rintro ⟨a, b, hab⟩
  have hnotinj : ¬ Function.Injective a := by
    intro hinj
    have hle := Fintype.card_le_of_injective a hinj
    simp only [Fintype.card_fin] at hle
    omega
  rw [Function.Injective] at hnotinj
  simp only [not_forall] at hnotinj
  obtain ⟨i₁, i₂, haeq, hne⟩ := hnotinj
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : φ.Realize (Sum.elim (a i₁) (b i₁)) := (hab i₁ i₁).mpr (le_refl i₁)
    rw [haeq] at h1
    exact not_le_of_gt hlt ((hab i₂ i₁).mp h1)
  · have h2 : φ.Realize (Sum.elim (a i₂) (b i₂)) := (hab i₂ i₂).mpr (le_refl i₂)
    rw [← haeq] at h2
    exact not_le_of_gt hlt ((hab i₁ i₂).mp h2)

/-- Every finite `L`-structure is model-theoretically stable. -/
theorem isStableStructure_of_finite (L : Language) (M : Type*) [L.Structure M] [Finite M] :
    L.IsStableStructure M :=
  fun _ _ φ => Formula.IsStableIn.of_finite φ M

/-- Stability of a partitioned formula is preserved along `L`-isomorphisms. -/
theorem Equiv.isStableIn_imp {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]
    (g : M ≃[L] N) {α β : Type*} {φ : L.Formula (α ⊕ β)} (hM : φ.IsStableIn M) :
    φ.IsStableIn N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  rintro ⟨a, b, hab⟩
  refine hn ⟨fun i => g.symm ∘ a i, fun j => g.symm ∘ b j, fun i j => ?_⟩
  have hcomp : Sum.elim (g.symm ∘ a i) (g.symm ∘ b j) = g.symm ∘ Sum.elim (a i) (b j) := by
    ext x
    cases x <;> rfl
  rw [hcomp, StrongHomClass.realize_formula g.symm]
  exact hab i j

/-- Stability of a partitioned formula is invariant under `L`-isomorphism. -/
theorem Equiv.isStableIn_iff {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]
    (g : M ≃[L] N) {α β : Type*} (φ : L.Formula (α ⊕ β)) :
    φ.IsStableIn M ↔ φ.IsStableIn N :=
  ⟨g.isStableIn_imp, g.symm.isStableIn_imp⟩

/-- Stability of an `L`-structure is invariant under `L`-isomorphism. -/
theorem Equiv.isStableStructure_iff {L : Language} {M N : Type*} [L.Structure M] [L.Structure N]
    (g : M ≃[L] N) :
    L.IsStableStructure M ↔ L.IsStableStructure N :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun φ => g.isStableIn_iff φ

end Language

namespace Ring

/-- A ring `R` is *model-theoretically stable* if its structure in `Language.ring` (via
`compatibleRingOfRing R`) is stable. -/
def IsStableRing (R : Type*) [Ring R] : Prop :=
  let _ := compatibleRingOfRing R
  Language.ring.IsStableStructure R

/-- Every finite ring is model-theoretically stable in `Language.ring`. -/
theorem isStableRing_of_finite (R : Type*) [Ring R] [Finite R] : IsStableRing R := by
  let _ := compatibleRingOfRing R
  exact Language.isStableStructure_of_finite Language.ring R

/-- `IsStableRing` is preserved along any ring isomorphism `R ≃+* S`. -/
theorem isStableRing_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    (hR : IsStableRing R) : IsStableRing S := by
  let _ := compatibleRingOfRing R
  let _ := compatibleRingOfRing S
  exact (Language.Equiv.isStableStructure_iff
    (languageEquivEquivRingEquiv.symm e)).mp hR

/-- `IsStableRing` is invariant under ring isomorphism. -/
theorem isStableRing_iff_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    IsStableRing R ↔ IsStableRing S :=
  ⟨isStableRing_of_ringEquiv e, isStableRing_of_ringEquiv e.symm⟩

end Ring

end FirstOrder
