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

public import FormalConjecturesForMathlib.Algebra.Hochschild.Chains

/-!
# Formulas for Hochschild faces

This file evaluates the rotation-based Hochschild faces on pure tensors.  These formulas verify
that the abstract tensor-power construction uses the standard cyclic convention.
-/

@[expose] public section

open scoped TensorProduct

namespace Hochschild

variable (k A : Type*) [CommRing k] [NonUnitalRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- A power of the basic cyclic rotation is addition by the exponent. -/
@[simp] theorem finRotate_pow_eq_finCycle {m : ℕ} (i : Fin m) :
    finRotate m ^ i.val = finCycle i := by
  apply Equiv.ext
  intro x
  rw [Equiv.Perm.coe_pow]
  exact congrFun (@finCycle_eq_finRotate_iterate m i).symm x

/-- A power of the inverse cyclic rotation is subtraction by the exponent. -/
@[simp] theorem finRotate_symm_pow_eq_finCycle_symm {m : ℕ} (i : Fin m) :
    (finRotate m).symm ^ i.val = (finCycle i).symm := by
  change (finRotate m)⁻¹ ^ i.val = (finCycle i)⁻¹
  rw [inv_pow, finRotate_pow_eq_finCycle]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem rotate_symm_tprod (m : ℕ) (x : Fin m → A) :
    (rotate k A m).symm (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i ↦ x (finRotate m i)) := by
  simp [rotate, PiTensorProduct.reindex_symm]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem rotate_symm_pow_tprod (m r : ℕ) (x : Fin m → A) :
    ((rotate k A m).symm ^ r) (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i ↦ x (((finRotate m).symm ^ r).symm i)) := by
  induction r with
  | zero =>
    apply congrArg (PiTensorProduct.tprod k)
    funext i
    rfl
  | succ r ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, rotate_symm_tprod]
    rfl

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem rotate_pow_tprod (m r : ℕ) (x : Fin m → A) :
    (rotate k A m ^ r) (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (fun i ↦ x (((finRotate m) ^ r).symm i)) := by
  induction r with
  | zero =>
    apply congrArg (PiTensorProduct.tprod k)
    funext i
    rfl
  | succ r ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, rotate_tprod]
    rfl

/-- The tuple obtained by applying the `i`th Hochschild face to a pure tensor. -/
def faceTuple (n : ℕ) (i : Fin (n + 2)) (x : Fin (n + 2) → A) : Fin (n + 1) → A :=
  if i = Fin.last (n + 1) then
    Fin.cons (x ((finRotate (n + 2)).symm 0) * x ((finRotate (n + 2)).symm 1))
      (fun j ↦ x ((finRotate (n + 2)).symm j.succ.succ))
  else
    let y : Fin (n + 2) → A :=
      fun q ↦ x (((finRotate (n + 2)).symm ^ i.val).symm q)
    let z : Fin (n + 1) → A := Fin.cons (y 0 * y 1) (fun j ↦ y j.succ.succ)
    fun q ↦ z (((finRotate (n + 1) ^ i.val).symm q))

/-- The usual coordinate description of a Hochschild face. -/
def standardFaceTuple (n : ℕ) (i : Fin (n + 2)) (x : Fin (n + 2) → A) :
    Fin (n + 1) → A :=
  if h : i = Fin.last (n + 1) then
    Fin.cons (x i * x 0) (fun q ↦ x q.castSucc.succ)
  else fun q ↦
    if q < i.castPred h then x q.castSucc
    else if q = i.castPred h then x i * x (i.castPred h).succ
    else x q.succ

/-- Rotating an ordinary adjacent pair to the front, multiplying it, and rotating back gives
the standard piecewise adjacent-product formula. -/
theorem ordinary_rotated_tuple {A : Type*} [Mul A] (n : ℕ) (i q : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    Fin.cons (α := fun _ : Fin (n + 1) ↦ A) (x i.castSucc * x i.succ)
      (fun j : Fin n ↦ x (j.succ.succ + i.castSucc)) (q - i) =
      if q < i then x q.castSucc else if q = i then x i.castSucc * x i.succ
      else x q.succ := by
  by_cases heq : q = i
  · subst q
    simp
  have hne : q - i ≠ 0 := sub_ne_zero.mpr heq
  rw [← Fin.succ_pred (q - i) hne, Fin.cons_succ]
  have hv := Fin.intCast_val_sub_eq_sub_add_ite q i
  have hp : ((q - i).pred hne).val + 1 = (q - i).val := by
    have hh := congrArg Fin.val (Fin.succ_pred (q - i) hne)
    exact hh
  by_cases hlt : q < i
  · rw [if_pos hlt]
    apply congrArg x
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_succ, Fin.val_castSucc]
    have hs : ((q - i).pred hne).val + 1 + 1 + i.val = q.val + (n + 2) := by
      simp only [not_le.mpr hlt, if_false] at hv
      omega
    rw [hs, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q.val < n + 2)]
  · rw [if_neg hlt, if_neg heq]
    apply congrArg x
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_succ, Fin.val_castSucc]
    have hs : ((q - i).pred hne).val + 1 + 1 + i.val = q.val + 1 := by
      simp only [le_of_not_gt hlt, if_true] at hv
      omega
    rw [hs, Nat.mod_eq_of_lt (by omega : q.val + 1 < n + 2)]

/-- The rotation construction agrees with the standard coordinate formula. -/
theorem faceTuple_eq_standardFaceTuple (n : ℕ) (i : Fin (n + 2))
    (x : Fin (n + 2) → A) : faceTuple A n i x = standardFaceTuple A n i x := by
  funext q
  by_cases h : i = Fin.last (n + 1)
  · subst i
    simp only [faceTuple, standardFaceTuple, if_pos, finRotate_symm_apply]
    refine Fin.cases ?_ (fun j ↦ ?_) q
    · simp only [Fin.cons_zero]
      congr 1 <;> apply congrArg x <;> apply Fin.ext <;> simp
    · apply congrArg x
      apply Fin.ext
      rw [Fin.sub_val_of_le]
      · simp
      · rw [Fin.le_iff_val_le_val]
        simp
  · rw [faceTuple, standardFaceTuple, if_neg h, dif_neg h]
    let i' := i.castPred h
    have hin : (((finRotate (n + 2)).symm ^ i.val).symm) = finCycle i := by
      change ((finRotate (n + 2))⁻¹ ^ i.val)⁻¹ = finCycle i
      rw [inv_pow, inv_inv, finRotate_pow_eq_finCycle]
    have hout : (finRotate (n + 1) ^ i.val).symm = (finCycle i').symm := by
      rw [show i.val = i'.val by rfl, finRotate_pow_eq_finCycle]
    rw [hin, hout]
    simp only [finCycle_apply, finCycle_symm_apply]
    have hone : (1 + i : Fin (n + 2)) = i'.succ := by
      apply Fin.ext
      have hi_lt := Fin.lt_last_iff_ne_last.mpr h
      change (1 + i.val) % (n + 2) = i.val + 1
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hone]
    simpa [i'] using ordinary_rotated_tuple n i' q x

/-- Every Hochschild face sends a pure tensor to the pure tensor given by `faceTuple`. -/
@[simp]
theorem face_tprod (n : ℕ) (i : Fin (n + 2)) (x : Fin (n + 2) → A) :
    face k A n i (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (faceTuple A n i x) := by
  by_cases h : i = Fin.last (n + 1)
  · simp [face, faceTuple, h, headFace_tprod]
  · simp [face, faceTuple, h, headFace_tprod]

/-- Every Hochschild face has the standard adjacent-product formula on pure tensors. -/
@[simp]
theorem face_tprod_standard (n : ℕ) (i : Fin (n + 2)) (x : Fin (n + 2) → A) :
    face k A n i (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (standardFaceTuple A n i x) := by
  rw [face_tprod, faceTuple_eq_standardFaceTuple]

/-- In degree two, the all-degree boundary is
`a₀a₁ ⊗ a₂ - a₀ ⊗ a₁a₂ + a₂a₀ ⊗ a₁`. -/
theorem boundary_one_tprod (x : Fin 3 → A) :
    boundary k A 1 (PiTensorProduct.tprod k x) =
      PiTensorProduct.tprod k (Fin.cons (x 0 * x 1) (fun _ ↦ x 2)) -
      PiTensorProduct.tprod k (Fin.cons (x 0) (fun _ ↦ x 1 * x 2)) +
      PiTensorProduct.tprod k (Fin.cons (x 2 * x 0) (fun _ ↦ x 1)) := by
  have h0 : faceTuple A 1 (0 : Fin 3) x = Fin.cons (x 0 * x 1) (fun _ ↦ x 2) := by
    funext q
    fin_cases q <;> rfl
  have h1 : faceTuple A 1 (1 : Fin 3) x = Fin.cons (x 0) (fun _ ↦ x 1 * x 2) := by
    funext q
    fin_cases q <;> rfl
  have h2 : faceTuple A 1 (2 : Fin 3) x = Fin.cons (x 2 * x 0) (fun _ ↦ x 1) := by
    funext q
    fin_cases q <;> rfl
  rw [boundary_apply, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [face_tprod, h0, h1, h2, sub_eq_add_neg, add_assoc]

/-- The all-degree Hochschild construction squares to zero in the first possible degree. -/
theorem boundary_zero_comp_boundary_one : boundary k A 0 ∘ₗ boundary k A 1 = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  apply (chains0Equiv k A).injective
  change chains0Equiv k A (boundary k A 0 (boundary k A 1
    (PiTensorProduct.tprod k x))) = chains0Equiv k A 0
  rw [boundary_one_tprod]
  simp [chains0Equiv_boundary_zero_tprod, mul_assoc]

end Hochschild
