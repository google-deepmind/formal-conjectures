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

import FormalConjecturesUtil

/-!
# Jacobian conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Jacobian_conjecture)
-/

namespace JacobianConjecture

section Conjecture

open MvPolynomial RegularFunction

variable (k : Type*)

name_poly_vars X, Y, Z over k

/-- Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `-2` which is not injective. -/
noncomputable abbrev F [CommRing k] : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + X * Y)^3 * Z + Y ^ 2 * (1 + X * Y) * (4 + 3 * X * Y),
    Y + 3 * X * (1 + X * Y) ^ 2 * Z + 3 * X * Y ^ 2 * (4 + 3 * X * Y),
    2 * X - 3 * X ^ 2 * Y - X ^ 3 * Z]

/-- A variant of Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `1` which is not injective. -/
noncomputable abbrev G [CommRing k] : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + 2 * X * Y) ^ 3 * Z + 4 * Y ^ 2 * (1 + 2 * X * Y) * (2 + 3 * (X * Y)),
    Y + 3 * X * (1 + 2 * X * Y) ^ 2 * Z + 12 * X * Y ^ 2 * (2 + 3 * (X * Y)),
    -X + 3 * X ^ 2 * Y + X ^ 3 * Z]


@[category API, AMS 14]
lemma det_jacobian_F [CommRing k] : (F k).Jacobian.det = -2 := by
  simp only [Jacobian, F, Fin.isValue, ← map_ofNat (C : k →+* MvPolynomial (Fin 3) k),
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, map_add, Derivation.leibniz,
    pderiv_X, ne_eq, Fin.reduceEq, not_false_eq_true, Pi.single_eq_of_ne, smul_eq_mul, mul_zero,
    Derivation.leibniz_pow, Nat.add_one_sub_one, Derivation.map_one_eq_zero, one_ne_zero,
    Pi.single_eq_same, mul_one, zero_add, nsmul_eq_mul, Nat.cast_ofNat, derivation_C, add_zero,
    pow_one,  Matrix.cons_val_one, zero_ne_one, Matrix.cons_val_two, Nat.succ_eq_add_one,
    Nat.reduceAdd, Matrix.tail_cons, Matrix.head_cons, map_sub, sub_self, zero_sub, mul_neg,
    sub_zero, neg_mul, sub_neg_eq_add]
  simp only [map_ofNat]
  ring

@[category API, AMS 14]
lemma det_jacobian_G [CommRing k] : (G k).Jacobian.det = 1 := by
  simp only [G, Jacobian, ← map_ofNat (C : k →+* MvPolynomial (Fin 3) k), Matrix.det_fin_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_neg, Derivation.map_one_eq_zero, pderiv_mul,
    pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_ofNat]
  ring

/-- `F` identifies the two distinct points `(0, 0, -1/4)` and `(1, -3/2, 13/2)`. -/
@[category API, AMS 14]
lemma aeval_F_eq [Field k] [CharZero k] :
    (F k).aeval ![(0 : k), 0, -1/4] = (F k).aeval ![(1 : k), -3/2, 13/2]  := by
  funext i
  fin_cases i <;> simp [RegularFunction.aeval] <;> grind

/-- `G` identifies the two distinct points `(1, 0, 1)` and `(0, 3, -71)`. -/
@[category API, AMS 14]
lemma aeval_G_eq [CommRing k] :
    (G k).aeval ![1, 0, (1 : k)] = (G k).aeval ![0, 3, -71] := by
  funext i
  fin_cases i <;> simp [RegularFunction.aeval]; grind

/-- The predicate that the Jacobian conjecture holds for a given field and variable index type
(i.e. number of variables). -/
def JacobianConjectureProp (k σ : Type*) [CommRing k] [Fintype σ] [DecidableEq σ] : Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

set_option linter.style.answer_attribute false in
/-- The **Jacobian Conjecture**: any regular function
(i.e. vector valued polynomial function from) `kⁿ → kᵐ`
whose Jacobian is a non-zero constant has an inverse that
is given by a regular function, where `k` is a field of characteristic `0`.

This is false: `F` has Jacobian determinant `1` but identifies
two distinct points, so it admits no inverse. This counterexample works in all characteristics. -/
@[category research solved, AMS 14]
theorem jacobian_conjecture {k : Type} [CommRing k] [Nontrivial k] :
    answer(False) ↔ ∀ {σ : Type} [Fintype σ] [DecidableEq σ], JacobianConjectureProp k σ := by
  rw [false_iff]
  intro h
  obtain ⟨H, -, hGH⟩ := h (G k) (det_jacobian_G k ▸ isUnit_one)
  have hleft : Function.LeftInverse (H.aeval (S₁ := k)) ((G k).aeval) := fun a => by
    rw [← RegularFunction.comp_aeval, hGH]
    funext t
    simp [RegularFunction.aeval, RegularFunction.id]
  have h1 : (1 : k) = 0 := congrFun (hleft.injective (aeval_G_eq k)) 0
  norm_num at h1

/-- Does the Jacobian conjecture hold in the two variable case? -/
@[category research open, AMS 14]
theorem jacobian_conjecture_two_variables :
    answer(sorry) ↔ ∀ {k : Type} [Field k] [CharZero k], JacobianConjectureProp k (Fin 2) := by
  sorry

end Conjecture

section Tests

open MvPolynomial RegularFunction

variable {k σ : Type} [Fintype σ] [DecidableEq σ] [Field k]

-- Let's check that we've stated the "invertible Jacobian" condition correctly
-- by proving an equivalence
@[category API, AMS 14]
lemma sanity_check_condition_1 (F : RegularFunction k σ σ) :
    IsUnit F.Jacobian.det ↔ (∃ (c : k), c ≠ 0 ∧ F.Jacobian.det = .C c) := by
  simp [MvPolynomial.isUnit_iff_eq_C_of_isReduced, isUnit_iff_ne_zero]

-- Let's apply the conjecture to a trivial case to make sure things
-- are working as expected.
@[category test, AMS 14]
theorem jacobian_conjecture_identity (H : JacobianConjectureProp k σ) :
    ∃ (G : RegularFunction k σ σ), G.comp (id k σ) = id k σ ∧
    (id k σ).comp G = id k σ := by
  apply H
  suffices (RegularFunction.id k σ).Jacobian = 1 by simp [this, isUnit_one, Matrix.det_one]
  ext i j
  simp [RegularFunction.Jacobian, RegularFunction.id, Matrix.one_eq_pi_single]

end Tests

end JacobianConjecture
