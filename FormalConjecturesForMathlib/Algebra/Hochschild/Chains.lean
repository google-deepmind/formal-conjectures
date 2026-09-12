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

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Hochschild tensor chains in all degrees

This file defines Hochschild chains of a nonunital algebra using algebraic tensor powers.
Multiplication of adjacent factors and cyclic reindexing give the standard faces, whose
alternating sum is the Hochschild boundary. The face formulas, face identities, and resulting
chain complex are developed in the companion modules.
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct

namespace Hochschild

variable (k A : Type*) [CommRing k] [NonUnitalRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- Degree-`n` Hochschild chains of `A/k`, namely `A ^ {⊗ (n+1)}`. -/
abbrev Chains (n : ℕ) := TensorPower k (n + 1) A

/-- Multiplication of a two-fold tensor power. -/
noncomputable def pairMul : TensorPower k 2 A →ₗ[k] A :=
  LinearMap.mul' k A ∘ₗ
    TensorProduct.map
      (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 ↦ A) 0).toLinearMap
      (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 ↦ A) 0).toLinearMap ∘ₗ
    (TensorPower.mulEquiv (R := k) (M := A) (n := 1) (m := 1)).symm.toLinearMap

@[simp]
theorem pairMul_tprod (x : Fin 2 → A) :
    pairMul k A (PiTensorProduct.tprod k x) = x 0 * x 1 := by
  simp [pairMul, TensorPower.mulEquiv, finSumFinEquiv]

/-- Multiply the first two factors of an `(n+2)`-fold tensor power. -/
noncomputable def headFace (n : ℕ) : TensorPower k (n + 2) A →ₗ[k] TensorPower k (n + 1) A :=
  (TensorPower.cast k A (Nat.add_comm 1 n)).toLinearMap ∘ₗ
    (TensorPower.mulEquiv (R := k) (M := A) (n := 1) (m := n)).toLinearMap ∘ₗ
    TensorProduct.map
      (PiTensorProduct.subsingletonEquiv
        (R := k) (s := fun _ : Fin 1 ↦ A) 0).symm.toLinearMap LinearMap.id ∘ₗ
    TensorProduct.map (pairMul k A) LinearMap.id ∘ₗ
    (TensorPower.mulEquiv (R := k) (M := A) (n := 2) (m := n)).symm.toLinearMap ∘ₗ
    (TensorPower.cast k A (Nat.add_comm n 2)).toLinearMap

@[simp]
theorem headFace_tprod (n : ℕ) (x : Fin (n + 2) → A) :
    headFace k A n (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (Fin.cons (x 0 * x 1) (fun i ↦ x i.succ.succ)) := by
  simp [headFace, TensorPower.cast_tprod, TensorPower.mulEquiv, pairMul, Function.comp_def]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  rw [Fin.cons_succ]
  have h : Fin.cast (Nat.add_comm n 1) j.succ = Fin.natAdd 1 j := by
    ext
    simp [Fin.natAdd, Nat.add_comm]
  rw [h, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Cyclically rotate all factors of a tensor power. -/
noncomputable def rotate (m : ℕ) : TensorPower k m A ≃ₗ[k] TensorPower k m A :=
  PiTensorProduct.reindex k (fun _ : Fin m ↦ A) (finRotate m)

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp]
theorem rotate_tprod (m : ℕ) (x : Fin m → A) :
    rotate k A m (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i ↦ x ((finRotate m).symm i)) :=
  PiTensorProduct.reindex_tprod _ _

/-- Multiply the first two factors after `r` cyclic rotations.  These concrete maps are the
building blocks for all Hochschild faces, including the cyclic last face. -/
noncomputable def rotatedHeadFace (n r : ℕ) :
    TensorPower k (n + 2) A →ₗ[k] TensorPower k (n + 1) A :=
  headFace k A n ∘ₗ ((rotate k A (n + 2)) ^ r).toLinearMap

/-- The `i`th Hochschild face from degree `n+1` to degree `n`.  For an ordinary face, cyclically
move factors `i,i+1` to the front, multiply them, and move the result back.  The last face moves
the last and first factors to the front and leaves their product first. -/
noncomputable def face (n : ℕ) (i : Fin (n + 2)) :
    Chains k A (n + 1) →ₗ[k] Chains k A n :=
  if _h : i = Fin.last (n + 1) then
    headFace k A n ∘ₗ (rotate k A (n + 2)).toLinearMap
  else
    (((rotate k A (n + 1)) ^ i.val).toLinearMap) ∘ₗ headFace k A n ∘ₗ
      (((rotate k A (n + 2)).symm ^ i.val).toLinearMap)

/-- The Hochschild differential in every positive degree, as the alternating sum of the concrete
faces on tensor powers. -/
noncomputable def boundary (n : ℕ) : Chains k A (n + 1) →ₗ[k] Chains k A n :=
  ∑ i : Fin (n + 2), (-1 : k) ^ i.val • face k A n i

theorem boundary_apply (n : ℕ) (x : Chains k A (n + 1)) :
    boundary k A n x = ∑ i : Fin (n + 2), (-1 : k) ^ i.val • face k A n i x := by
  simp [boundary]

/-- The canonical identification of degree-zero chains with the algebra. -/
noncomputable def chains0Equiv : Chains k A 0 ≃ₗ[k] A :=
  PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 ↦ A) 0

/-- The all-degree construction specializes in degree one to the commutator boundary. -/
theorem chains0Equiv_boundary_zero_tprod (x : Fin 2 → A) :
    chains0Equiv k A (boundary k A 0 (PiTensorProduct.tprod k x)) =
      x 0 * x 1 - x 1 * x 0 := by
  simp [chains0Equiv, boundary, face, headFace_tprod, rotate, pow_succ,
    PiTensorProduct.reindex_tprod]
  rw [show (-1 : Fin 2) = 1 by decide]
  rw [sub_eq_add_neg]

end Hochschild
