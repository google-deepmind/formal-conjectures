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

  have F_det : F.Jacobian.det = .C (-2) := by
    have hC2 : MvPolynomial.C (σ := Fin 3) (2 : k) =
        (2 : MvPolynomial (Fin 3) k) := by
      simpa using map_ofNat (MvPolynomial.C : k →+* MvPolynomial (Fin 3) k) 2
    have hC3 : MvPolynomial.C (σ := Fin 3) (3 : k) =
        (3 : MvPolynomial (Fin 3) k) := by
      simpa using map_ofNat (MvPolynomial.C : k →+* MvPolynomial (Fin 3) k) 3
    have hC4 : MvPolynomial.C (σ := Fin 3) (4 : k) =
        (4 : MvPolynomial (Fin 3) k) := by
      simpa using map_ofNat (MvPolynomial.C : k →+* MvPolynomial (Fin 3) k) 4
    have hCneg2 :
        MvPolynomial.C (σ := Fin 3) (-2 : k) = (-2 : MvPolynomial (Fin 3) k) := by
      rw [map_neg]
      exact congrArg Neg.neg hC2
    let t := 1 + x * y
    let h := t ^ 2 * z + y ^ 2 * (4 + 3 * x * y)
    let r := 2 * x - 3 * x ^ 2 * y - x ^ 3 * z
    let G : RegularFunction k (Fin 3) (Fin 3) :=
      ![t * h, y + 3 * x * h, r]
    have hF : F = G := by
      funext i
      fin_cases i <;> simp [F, G, t, h, r, hC2, hC3, hC4] <;> ring
    rw [hF]
    rw [hCneg2]

    let a := MvPolynomial.pderiv (0 : Fin 3) h
    let b := MvPolynomial.pderiv (1 : Fin 3) h
    let rx := 2 - 6 * x * y - 3 * x ^ 2 * z
    have hx_x : MvPolynomial.pderiv (0 : Fin 3) x = 1 := by simp [hx]
    have hx_y : MvPolynomial.pderiv (1 : Fin 3) x = 0 := by simp [hx]
    have hx_z : MvPolynomial.pderiv (2 : Fin 3) x = 0 := by simp [hx]
    have hy_x : MvPolynomial.pderiv (0 : Fin 3) y = 0 := by simp [hy]
    have hy_y : MvPolynomial.pderiv (1 : Fin 3) y = 1 := by simp [hy]
    have hy_z : MvPolynomial.pderiv (2 : Fin 3) y = 0 := by simp [hy]
    have hz_x : MvPolynomial.pderiv (0 : Fin 3) z = 0 := by simp [hz]
    have hz_y : MvPolynomial.pderiv (1 : Fin 3) z = 0 := by simp [hz]
    have hpderiv2 (i : Fin 3) :
        MvPolynomial.pderiv i (2 : MvPolynomial (Fin 3) k) = 0 := by
      rw [← hC2, MvPolynomial.pderiv_C]
    have hpderiv3 (i : Fin 3) :
        MvPolynomial.pderiv i (3 : MvPolynomial (Fin 3) k) = 0 := by
      rw [← hC3, MvPolynomial.pderiv_C]
    have hpderiv4 (i : Fin 3) :
        MvPolynomial.pderiv i (4 : MvPolynomial (Fin 3) k) = 0 := by
      rw [← hC4, MvPolynomial.pderiv_C]
    have ht_x : MvPolynomial.pderiv (0 : Fin 3) t = y := by
      simp [t, hx, hy]
    have ht_y : MvPolynomial.pderiv (1 : Fin 3) t = x := by
      simp [t, hx, hy]
    have ht_z : MvPolynomial.pderiv (2 : Fin 3) t = 0 := by
      simp [t, hx, hy]
    have hz_h_left : MvPolynomial.pderiv (2 : Fin 3) (t ^ 2 * z) = t ^ 2 := by
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, ht_z, hz]
      simp
    have hz_h_right : MvPolynomial.pderiv (2 : Fin 3)
        (y ^ 2 * (4 + 3 * x * y)) = 0 := by
      rw [hx, hy]
      simp [hpderiv3, hpderiv4]
    have hz_h : MvPolynomial.pderiv (2 : Fin 3) h = t ^ 2 := by
      dsimp only [h]
      rw [map_add, hz_h_left, hz_h_right, add_zero]

    have hf_x : MvPolynomial.pderiv (0 : Fin 3) (t * h) = y * h + t * a := by
      dsimp only [a]
      rw [MvPolynomial.pderiv_mul, ht_x]
    have hf_y : MvPolynomial.pderiv (1 : Fin 3) (t * h) = x * h + t * b := by
      dsimp only [b]
      rw [MvPolynomial.pderiv_mul, ht_y]
    have hf_z : MvPolynomial.pderiv (2 : Fin 3) (t * h) = t ^ 3 := by
      rw [MvPolynomial.pderiv_mul, ht_z, hz_h]
      ring
    have hg_x : MvPolynomial.pderiv (0 : Fin 3)
        (y + 3 * x * h) = 3 * h + 3 * x * a := by
      dsimp only [a]
      rw [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        hy_x, hpderiv3, hx_x]
      ring
    have hg_y : MvPolynomial.pderiv (1 : Fin 3)
        (y + 3 * x * h) = 1 + 3 * x * b := by
      dsimp only [b]
      rw [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        hy_y, hpderiv3, hx_y]
      ring
    have hg_z : MvPolynomial.pderiv (2 : Fin 3)
        (y + 3 * x * h) = 3 * x * t ^ 2 := by
      rw [map_add, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
        hy_z, hpderiv3, hx_z, hz_h]
      ring
    have hr_x : MvPolynomial.pderiv (0 : Fin 3) r = rx := by
      simp [r, rx, hx, hy, hz, hpderiv2, hpderiv3]
      ring
    have hr_y : MvPolynomial.pderiv (1 : Fin 3) r = -3 * x ^ 2 := by
      simp [r, hx, hy, hz, hpderiv2, hpderiv3]
    have hr_z : MvPolynomial.pderiv (2 : Fin 3) r = -x ^ 3 := by
      simp [r, hx, hy, hz, hpderiv2, hpderiv3]
    have hJac : G.Jacobian =
        !![y * h + t * a, 3 * h + 3 * x * a, rx;
           x * h + t * b, 1 + 3 * x * b, -3 * x ^ 2;
           t ^ 3, 3 * x * t ^ 2, -x ^ 3] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [RegularFunction.Jacobian, Matrix.of_apply, G, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two]
      all_goals assumption
    rw [hJac]
    rw [Matrix.det_fin_three]
    simp

    have ha : x ^ 3 * a =
        2 * t - 2 * t * y * r - t ^ 2 * rx - 3 * x ^ 2 * h := by
      dsimp only [a, h]
      simp [ht_x, hx_x, hy_x, hz_x, hpderiv3, hpderiv4, r, rx]
      ring
    have hb : x ^ 3 * b =
        x ^ 2 - 2 * t * x * r + 3 * t ^ 2 * x ^ 2 := by
      dsimp only [b, h]
      simp [ht_y, hx_y, hy_y, hz_y, hpderiv3, hpderiv4, r]
      ring
    have hr : t ^ 2 * r + x ^ 3 * h = x * (t + 1) := by
      simp [t, h, r]
      ring
    have hr' : t ^ 2 * r = x * (t + 1) - x ^ 3 * h := by
      rw [eq_sub_iff_add_eq]
      exact hr

    calc
      _ = (3 * x ^ 2 * h - t) * (x ^ 3 * a) +
            3 * h * (x ^ 3 * b) + x ^ 3 * y * h * (-1 + 9 * t ^ 2) +
            3 * x ^ 4 * h ^ 2 - 9 * x ^ 2 * h * t ^ 3 +
            rx * t ^ 2 * (3 * x ^ 2 * h - t) := by ring
      _ = -2 * t ^ 2 + (8 * t + 4) * x ^ 2 * h - 6 * x ^ 4 * h ^ 2 -
            6 * t ^ 2 * x * h * r + 2 * t ^ 2 * y * r := by
          rw [ha, hb]
          dsimp only [t]
          ring
      _ = -2 * t ^ 2 + (8 * t + 4) * x ^ 2 * h - 6 * x ^ 4 * h ^ 2 +
            (-6 * x * h + 2 * y) * (t ^ 2 * r) := by ring
      _ = -2 := by
          rw [hr']
          dsimp only [t]
          ring
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
