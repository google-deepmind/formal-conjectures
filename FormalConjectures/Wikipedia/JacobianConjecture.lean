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

open Classical

section Prelims

variable {k : Type*} [CommRing k]
variable {σ τ ι : Type*}

variable (k σ τ) in

/-- The type of regular functions from $k^σ$ to $k^τ$. -/
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

variable (k : Type*) [Field k]

name_poly_vars X, Y, Z over k

/-- Alpöge/Fable's counterexample: a polynomial self-map of `k³` with Jacobian
determinant `-2` which is not injective. -/
noncomputable abbrev F : RegularFunction k (Fin 3) (Fin 3) :=
  ![(1 + X * Y)^3 * Z + Y ^ 2 * (1 + X * Y) * (4 + 3 * X * Y),
    Y + 3 * X * (1 + X * Y) ^ 2 * Z + 3 * X * Y ^ 2 * (4 + 3 * X * Y),
    2 * X - 3 * X ^ 2 * Y - X ^ 3 * Z]

@[category API, AMS 14]
lemma det_jacobian_F : (F k).Jacobian.det = -2 := by
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

variable [CharZero k]

/-- `F` identifies the two distinct points `(0, 0, -1/4)` and `(1, -3/2, 13/2)`. -/
@[category API, AMS 14]
lemma aeval_F_eq :
    (F k).aeval ![(0 : k), 0, -1/4] = (F k).aeval ![(1 : k), -3/2, 13/2]  := by
  funext i
  fin_cases i <;> simp [RegularFunction.aeval] <;> grind

/-- The **Jacobian Conjecture**: any regular function
(i.e. vector valued polynomial function from) `kⁿ → kᵐ`
whose Jacobian is a non-zero constant has an inverse that
is given by a regular function, where `k` is a field of characteristic `0`.

This is false: `F` has Jacobian determinant `-2` but identifies
two distinct points, so it admits no inverse. -/
@[category research solved, AMS 14]
theorem jacobian_conjecture  :
    ¬ ∀ {σ : Type} [Fintype σ] (F : RegularFunction k σ σ)
    (_H : IsUnit F.Jacobian.det),
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ := by
  intro h
  have : IsUnit (F k).Jacobian.det := by
    rw [det_jacobian_F k, MvPolynomial.isUnit_iff_eq_C_of_isReduced]
    use -2, by simp
    rw [C_neg, neg_inj, _root_.map_ofNat]
  obtain ⟨G, -, hFG⟩ := h (F k) (by convert this)
  have hleft : Function.LeftInverse (G.aeval (S₁ := k)) ((F k).aeval) := fun a => by
    rw [← RegularFunction.comp_aeval, hFG]
    funext t
    simp [RegularFunction.aeval, RegularFunction.id]
  have h1 : (0 : k) = 1 := congrFun (hleft.injective (aeval_F_eq k)) 0
  norm_num at h1

end Conjecture

section Tests

open RegularFunction

variable {k σ : Type} [Fintype σ] [DecidableEq σ] [Field k]

-- Let's check that we've stated the "invertible Jacobian" condition correctly
-- by proving an equivalence
@[category API, AMS 14]
lemma sanity_check_condition_1 (F : RegularFunction k σ σ) :
    IsUnit F.Jacobian.det ↔ (∃ (c : k), c ≠ 0 ∧ F.Jacobian.det = .C c) := by
  simp [MvPolynomial.isUnit_iff_eq_C_of_isReduced, isUnit_iff_ne_zero]

end Tests

end JacobianConjecture
