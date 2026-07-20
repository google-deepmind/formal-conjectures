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

section Prelims

variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}

variable (k σ τ) in

/-- Implicitly use `σ` as an index set and `k` as coefficient ring. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- The Jacobian of a vector valued polynomial function, viewed as a polynomial. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)

/-- The composition of two vector valued polynomial functions. -/
noncomputable def comp
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)

variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

/-- The evaluation of a regular function `f` over `k` at some point `a`
with coordinates in some algebra over `k`-/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

/--`aeval` is compatible with composition of regular functions. -/
@[category API, AMS 14]
lemma comp_aeval
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction

end Prelims

section Conjecture

open RegularFunction MvPolynomial

def JacobianConjectureProp (k σ : Type) [CommRing k] [Fintype σ] [DecidableEq σ] :
    Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

variable (k : Type) [Field k]

name_poly_vars X, Y, Z over k

/-- Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `1` which is not injective. -/
noncomputable def F : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + 2 * X * Y) ^ 3 * Z + 4 * Y ^ 2 * (1 + 2 * X * Y) * (2 + 3 * (X * Y)),
    Y + 3 * X * (1 + 2 * X * Y) ^ 2 * Z + 12 * X * Y ^ 2 * (2 + 3 * (X * Y)),
    -X + 3 * X ^ 2 * Y + X ^ 3 * Z]

@[category API, AMS 14]
lemma det_jacobian_F : (F k).Jacobian.det = 1 := by
  simp only [F, Jacobian, ← map_ofNat (C : k →+* MvPolynomial (Fin 3) k), Matrix.det_fin_three,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_neg, Derivation.map_one_eq_zero, pderiv_mul,
    pderiv_pow, pderiv_C, pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  simp only [map_ofNat]
  ring

/-- `F` identifies the two distinct points `(1, -3/4, 13/4)` and `(-1, 3/4, 13/4)`. -/
@[category API, AMS 14]
lemma aeval_F_eq [CharZero k] :
    (F k).aeval ![1, -(3 / 4), (13 / 4 : k)] = (F k).aeval ![-1, 3 / 4, 13 / 4] := by
  funext i
  fin_cases i <;> simp [RegularFunction.aeval, F] <;> field_simp <;> ring

set_option linter.style.answer_attribute false in
/-- The **Jacobian Conjecture**: any regular function
(i.e. vector valued polynomial function from) `kⁿ → kᵐ`
whose Jacobian is a non-zero constant has an inverse that
is given by a regular function, where `k` is a field of characteristic `0`.

This is false: `F` has Jacobian determinant `1` but identifies
two distinct points, so it admits no inverse. -/
@[category research solved, AMS 14]
theorem jacobian_conjecture {k : Type} [Field k] [CharZero k] :
    answer(False) ↔ ∀ {σ : Type} [Fintype σ] [DecidableEq σ],
      JacobianConjectureProp k σ := by
  rw [false_iff]
  intro h
  obtain ⟨G, -, hFG⟩ := h (F k) (det_jacobian_F k ▸ isUnit_one)
  have hleft : Function.LeftInverse (G.aeval (S₁ := k)) ((F k).aeval) := fun a => by
    rw [← RegularFunction.comp_aeval, hFG]
    funext t
    simp [RegularFunction.aeval, RegularFunction.id]
  have h1 : (1 : k) = -1 := congrFun (hleft.injective (aeval_F_eq k)) 0
  norm_num at h1

set_option linter.style.answer_attribute false in
/-- Does the Jacobian conjecture hold in the two variable case? -/
@[category research open, AMS 14]
theorem jacobian_conjecture_two_variables {k : Type} [Field k] [CharZero k] :
    answer(sorry) ↔ JacobianConjectureProp k (Fin 2) := by
  sorry

end Conjecture

section Tests

open RegularFunction

variable {k σ τ ι : Type} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] [Field k]

-- Let's check that we've stated the "invertible Jacobian" condition correctly
-- by proving an equivalence
@[category API, AMS 14]
lemma sanity_check_condition_1 (F : RegularFunction k σ σ) :
    IsUnit F.Jacobian.det ↔ (∃ (c : k), c ≠ 0 ∧
        F.Jacobian.det = .C c) := by
  simp [MvPolynomial.isUnit_iff_eq_C_of_isReduced, isUnit_iff_ne_zero]


-- Let's apply the conjecture to a trivial case to make sure things
-- are working as expected.
@[category test, AMS 14]
theorem jacobian_conjecture_identity (H : JacobianConjectureProp k σ) :
    ∃ (G : RegularFunction k σ σ), G.comp (id k σ) = id k σ ∧
    (id k σ).comp G = id k σ := by
  apply H
  suffices (RegularFunction.id k σ).Jacobian = 1 by simp only [this, isUnit_one, Matrix.det_one]
  ext i j
  simp only [RegularFunction.Jacobian, RegularFunction.id, MvPolynomial.pderiv_X,
    Matrix.of_apply, Matrix.one_eq_pi_single]

end Tests

end JacobianConjecture
