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

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Rational Hodge structures

This file defines a pure rational Hodge structure on a rational vector space. Its complexification
is the actual scalar extension `ℂ ⊗[ℚ] V`. Complex conjugation acts on the first tensor
factor, so the rational lattice and the conjugation symmetry are not additional data.

The Hodge pieces are the only data in a `PureHodgeStructure`. They must form a direct-sum
decomposition, vanish off the prescribed weight, and be exchanged by the constructed conjugation.
Hodge classes are then a derived preimage of the middle piece.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

/-- The canonical map from a `K`-vector space to its complexification. -/
def ofBase (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V] :
    V →ₗ[K] ℂ ⊗[K] V :=
  TensorProduct.mk K ℂ V 1

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on a complexified rational vector space. It conjugates the scalar factor
and fixes every rational vector. -/
def conjugate : ℂ ⊗[ℚ] V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.map (Complex.conjAe.restrictScalars ℚ).toLinearMap LinearMap.id

/-- A pure rational Hodge structure of weight `n` on `V`.

The pieces are indexed by pairs `(p,q)`. They form an internal direct sum, only pieces with
`p + q = n` can be nonzero, and complex conjugation exchanges the `(p,q)` and `(q,p)` pieces. -/
structure Pure (n : ℕ) where
  /-- The Hodge piece `V^{p,q}` inside `V_ℂ`. -/
  piece : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Hodge pieces off the prescribed weight are zero. -/
  piece_eq_bot_of_add_ne : ∀ p q, p + q ≠ n → piece p q = ⊥
  /-- Every complexified vector has a unique finite decomposition into Hodge pieces. -/
  isInternal : DirectSum.IsInternal (fun pq : ℕ × ℕ ↦ piece pq.1 pq.2)
  /-- The constructed complex conjugation exchanges bidegrees. -/
  conjugate_mem_iff : ∀ p q x, conjugate V x ∈ piece p q ↔ x ∈ piece q p

namespace Pure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- The Hodge filtration `F^p V_ℂ`, constructed as the sum of pieces whose first index is at
least `p`. -/
def filtration (H : Pure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ a : ℕ, ⨆ (_ : p ≤ a), ⨆ b : ℕ, H.piece a b

/-- Rational Hodge classes of codimension `p`: rational vectors whose complexifications lie in
the middle Hodge piece `V^{p,p}`. -/
def hodgeClasses (p : ℕ) (H : Pure V (2 * p)) : Submodule ℚ V :=
  Submodule.comap (ofBase ℚ V) ((H.piece p p).restrictScalars ℚ)

/-- The direct-sum coordinates of a pure Hodge structure. -/
noncomputable def decomposition (H : Pure V n) :
    ℂ ⊗[ℚ] V ≃ₗ[ℂ] (⨁ pq : ℕ × ℕ, H.piece pq.1 pq.2) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun pq : ℕ × ℕ ↦ H.piece pq.1 pq.2)
    H.isInternal).symm

/-- Sum of the Hodge pieces indexed by a set of bidegrees. -/
noncomputable def pieceSum (H : Pure V n) (s : Set (ℕ × ℕ)) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ pq, ⨆ (_ : pq ∈ s), H.piece pq.1 pq.2

/-- The conjugate filtration, written as the sum of pieces whose second index is large. -/
noncomputable def conjugateFiltration (H : Pure V n) (p : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) := H.pieceSum {pq | p ≤ pq.2}

end Pure

end HodgeStructure
