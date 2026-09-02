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

public import FormalConjecturesForMathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Right ideals

This file gives the basic API for right ideals.
-/

@[expose] public section

universe u

namespace RightIdeal

section Semiring

variable {R : Type u} [Semiring R]

@[ext]
theorem ext {I J : RightIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h

/-- A right ideal is closed under multiplication on the right. -/
theorem mul_mem_right (I : RightIdeal R) {a : R} (b : R) (ha : a ∈ I) : a * b ∈ I :=
  I.smul_mem (MulOpposite.op b) ha

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- A right ideal in a commutative semiring, regarded as an ideal. -/
def toIdeal (I : RightIdeal R) : Ideal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [smul_eq_mul, mul_comm]
    exact I.mul_mem_right r hx

@[simp]
theorem mem_toIdeal {I : RightIdeal R} {x : R} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

/-- An ideal in a commutative semiring, regarded as a right ideal. -/
def _root_.Ideal.toRightIdeal (I : Ideal R) : RightIdeal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [MulOpposite.smul_eq_mul_unop, mul_comm]
    exact I.mul_mem_left r.unop hx

@[simp]
theorem _root_.Ideal.mem_toRightIdeal {I : Ideal R} {x : R} :
    x ∈ I.toRightIdeal ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem toIdeal_toRightIdeal (I : RightIdeal R) : I.toIdeal.toRightIdeal = I :=
  rfl

@[simp]
theorem _root_.Ideal.toRightIdeal_toIdeal (I : Ideal R) : I.toRightIdeal.toIdeal = I :=
  rfl

/-- Over a commutative semiring, right ideals and ideals are order isomorphic. -/
def orderIsoIdeal (R : Type u) [CommSemiring R] : RightIdeal R ≃o Ideal R where
  toFun := toIdeal
  invFun := Ideal.toRightIdeal
  left_inv := toIdeal_toRightIdeal
  right_inv := Ideal.toRightIdeal_toIdeal
  map_rel_iff' := Iff.rfl

end CommSemiring

end RightIdeal
