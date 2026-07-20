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
noncomputable def aeval {σ τ : Type*} [Fintype σ] {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

/--`aeval` is compatible with composition of regular functions. -/
@[category API, AMS 14]
lemma comp_aeval
    {σ τ ι : Type*} [Fintype σ] [Fintype τ]
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction

end Prelims

variable {k : Type*} [Field k] [CharZero k]

section Conjecture

open RegularFunction

def JacobianConjectureProp (k σ : Type) [CommRing k] [Fintype σ] [DecidableEq σ] :
    Prop :=
  ∀ (F : RegularFunction k σ σ), IsUnit F.Jacobian.det →
    ∃ (G : RegularFunction k σ σ), G.comp F = id k σ ∧
    F.comp G = id k σ

set_option linter.style.answer_attribute false in
set_option maxHeartbeats 0 in
/-- The **Jacobian Conjecture**: any regular function
(i.e. vector valued polynomial function from) `kⁿ → kᵐ`
whose Jacobian is a non-zero constant has an inverse that
is given by a regular function, where `k` is a field of characteristic `0`-/
@[category research open, AMS 14]
theorem jacobian_conjecture {k : Type} [Field k] [CharZero k] :
    answer(False) ↔ ∀ {σ : Type} [Fintype σ] [DecidableEq σ],
      JacobianConjectureProp k σ := by
  simp
  use Fin 3
  set x := MvPolynomial.X (R := k) (0 : Fin 3) with hx
  set y := MvPolynomial.X (R := k) (1 : Fin 3) with hy
  set z := MvPolynomial.X (R := k) (2 : Fin 3) with hz

  let F : RegularFunction k (Fin 3) (Fin 3) :=
      ![(MvPolynomial.C 1 + x * y)^3 * z + y ^ 2 * (MvPolynomial.C  1 + x * y) * (MvPolynomial.C 4 + MvPolynomial.C 3 * x * y),
        y + MvPolynomial.C 3 * x * (MvPolynomial.C 1 + x * y) ^ 2 * z + MvPolynomial.C 3 * x * y ^ 2 * (MvPolynomial.C 4 + MvPolynomial.C 3 * x * y),
        MvPolynomial.C 2 * x - MvPolynomial.C 3 * x ^ 2 * y - x ^ 3 * z]

  have F_det : F.Jacobian.det = .C (- 2) := by
    unfold RegularFunction.Jacobian
    unfold F
    rw [Matrix.det_fin_three]
    simp [hx, hy, hz]
    sorry
  suffices ¬ (Function.Injective (RegularFunction.aeval (S₁ := k) F)) by
    use inferInstance, inferInstance
    unfold JacobianConjectureProp
    push ¬ _
    use F
    constructor
    · rw [F_det, MvPolynomial.isUnit_iff_eq_C_of_isReduced]
      use -2
      simp
    · intro x hx HxF
      apply this
      intro a b hab
      calc
        a = aeval (RegularFunction.id k (Fin 3)) a := by
          unfold aeval RegularFunction.id
          simp
        _ = aeval (F.comp x) a := by
          rw [HxF]
        _ = aeval x (aeval F a) := by
          rw [comp_aeval]
        _ = aeval x (aeval F b) := by
          rw [hab]
        _ = aeval (F.comp x) b := by
          rw [comp_aeval]
        _ = b := by
          rw [HxF]
          unfold aeval RegularFunction.id
          simp
  simp [F]
  rw [Function.not_injective_iff]
  use ![0, 0, -1/4], ![1, -3/2, 13/2]
  unfold RegularFunction.aeval
  simp
  ext t
  fin_cases t
  all_goals
    simp [MvPolynomial.eval_X, hx, hy, hz]
    grind

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
  -- TODO(lezeau): this is a little annoying to prove since this depends on a general statement that
  -- seems to be something missing from Mathlib
  sorry


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
