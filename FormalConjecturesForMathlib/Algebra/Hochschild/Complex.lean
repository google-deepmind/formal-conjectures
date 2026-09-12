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

public import FormalConjecturesForMathlib.Algebra.Hochschild.FaceIdentities
public import FormalConjecturesForMathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The Hochschild chain complex

This file adapts the concrete Hochschild face maps to the generic alternating-face construction.
The proved face identities imply that the concrete Hochschild boundary squares to zero in
every degree.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology.AlternatingFaceMapComplex

noncomputable section

namespace Hochschild

universe u

variable (k A : Type u) [CommRing k] [NonUnitalRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- The concrete Hochschild tensors and faces, packaged as generic face data. -/
def faceData : FaceData (C := ModuleCat k) where
  X n := ModuleCat.of k (Chains k A n)
  face n i := ModuleCat.ofHom (face k A n i)
  face_comp_face n i j H := by
    apply ModuleCat.hom_ext
    exact face_comp_face (A := A) k n i j H

/-- The generic alternating differential is the concrete Hochschild boundary. -/
theorem faceData_d_eq_boundary (n : ℕ) :
    (faceData k A).d n = ModuleCat.ofHom (boundary k A n) := by
  apply ModuleCat.hom_ext
  ext x
  change Chains k A (n + 1) at x
  dsimp [FaceData.d, boundary, faceData]
  let f := fun i : Fin (n + 2) ↦
    ((-1 : ℤ) ^ i.val) • ModuleCat.ofHom (face k A n i)
  have hsum := ModuleCat.hom_sum f Finset.univ
  calc
    _ = (∑ i : Fin (n + 2), (f i).hom) x := LinearMap.congr_fun hsum x
    _ = (∑ i : Fin (n + 2), (-1 : k) ^ i.val • face k A n i) x := by
      simp only [f, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Int.cast_smul_eq_zsmul k ((-1 : ℤ) ^ i.val)]
      simp

/-- The concrete Hochschild boundary squares to zero in every degree. -/
theorem boundary_comp_boundary (n : ℕ) :
    (boundary k A n).comp (boundary k A (n + 1)) = 0 := by
  have hd := (faceData k A).d_squared n
  rw [faceData_d_eq_boundary, faceData_d_eq_boundary] at hd
  have hd' := congrArg ModuleCat.Hom.hom hd
  dsimp [faceData] at hd'
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hd' x
  change (boundary k A n).comp (boundary k A (n + 1)) x = 0
  change (boundary k A n).comp (boundary k A (n + 1)) x =
    (ModuleCat.Hom.hom
      (0 : (faceData k A).X (n + 2) ⟶ (faceData k A).X n)) x at hx
  exact hx

/-- The chain complex with the concrete Hochschild tensor powers and boundaries. -/
@[implicit_reducible]
def chainComplex : ChainComplex (ModuleCat k) ℕ :=
  (faceData k A).chainComplex

@[simp] theorem chainComplex_X (n : ℕ) :
    (chainComplex k A).X n = ModuleCat.of k (Chains k A n) := rfl

@[simp] theorem chainComplex_d (n : ℕ) :
    (chainComplex k A).d (n + 1) n = ModuleCat.ofHom (boundary k A n) := by
  change (faceData k A).chainComplex.d (n + 1) n = _
  rw [FaceData.chainComplex_d, faceData_d_eq_boundary]

end Hochschild
