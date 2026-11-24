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

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Formal differentiation on rational function fields

Given a field `K`, this file constructs the formal quotient-rule operator `d/dX` on `RatFunc K` as a
`K`-linear `Derivation K (RatFunc K) (RatFunc K)` extending `Polynomial.derivative`, together with
algebraicity of `RatFunc K` over `Polynomial K`.

## Main definitions and results

* `RatFunc.isAlgebraic`: algebraicity of `RatFunc K` over `Polynomial K`.
* `RatFunc.derivation`: the `K`-derivation `d/dX` on `RatFunc K`.
* `RatFunc.derivation_div`: quotient rule for `RatFunc.derivation` on polynomial fractions.
* `RatFunc.derivation_algebraMap`, `RatFunc.derivation_X`: compatibility with
  `Polynomial.derivative`.
-/

@[expose] public section

namespace RatFunc

/-- Every element of `RatFunc K` satisfies a nonzero linear polynomial over `Polynomial K`, making
`RatFunc K` algebraic over `Polynomial K`. -/
theorem isAlgebraic (K : Type*) [Field K] : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
  ⟨fun x ↦ ⟨Polynomial.C x.denom * Polynomial.X - Polynomial.C x.num,
    fun h0 ↦ RatFunc.denom_ne_zero x (by simpa using congrArg (fun P ↦ P.coeff 1) h0), by
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      have hqdR : algebraMap (Polynomial K) (RatFunc K) x.denom ≠ 0 :=
        (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero x)
      linear_combination -(div_eq_iff hqdR).mp (RatFunc.num_div_denom x)⟩⟩

/-- Underlying quotient-rule formal derivative on `RatFunc K`. -/
noncomputable def derivAux (K : Type*) [Field K] (x : RatFunc K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (x.num.derivative * x.denom - x.num * x.denom.derivative) /
    algebraMap (Polynomial K) (RatFunc K) (x.denom ^ 2)

/-- Quotient rule for `RatFunc.derivAux` on arbitrary fractions `a / b` with `b ≠ 0`. -/
theorem derivAux_div {K : Type*} [Field K] (a b : Polynomial K) (hb : b ≠ 0) :
    derivAux K
        (algebraMap (Polynomial K) (RatFunc K) a / algebraMap (Polynomial K) (RatFunc K) b) =
      algebraMap (Polynomial K) (RatFunc K) (a.derivative * b - a * b.derivative) /
        algebraMap (Polynomial K) (RatFunc K) (b ^ 2) := by
  set x := algebraMap (Polynomial K) (RatFunc K) a / algebraMap (Polynomial K) (RatFunc K) b
  have hqd : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hbR : algebraMap (Polynomial K) (RatFunc K) b ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hb
  have hqdR : algebraMap (Polynomial K) (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hqd
  have heq : a * x.denom = x.num * b := RatFunc.algebraMap_injective K <| by
    simp only [map_mul]
    have hnd := (div_eq_iff hqdR).mp (RatFunc.num_div_denom x)
    have hx : x * algebraMap (Polynomial K) (RatFunc K) b =
        algebraMap (Polynomial K) (RatFunc K) a := div_mul_cancel₀ _ hbR
    rw [← hx, hnd]; ring
  have hder := congrArg Polynomial.derivative heq
  simp only [Polynomial.derivative_mul] at hder
  have hcross : (x.num.derivative * x.denom - x.num * x.denom.derivative) * b ^ 2 =
      (a.derivative * b - a * b.derivative) * x.denom ^ 2 := by
    linear_combination x.denom * b * hder.symm +
      (x.denom * b.derivative + b * x.denom.derivative) * heq
  dsimp [derivAux]
  rw [map_pow, map_pow, div_eq_div_iff (pow_ne_zero 2 hqdR) (pow_ne_zero 2 hbR)]
  simpa only [map_mul, map_pow] using congrArg (algebraMap (Polynomial K) (RatFunc K)) hcross

theorem derivAux_algebraMap {K : Type*} [Field K] (p : Polynomial K) :
    derivAux K (algebraMap (Polynomial K) (RatFunc K) p) =
      algebraMap (Polynomial K) (RatFunc K) p.derivative := by
  have hp : algebraMap (Polynomial K) (RatFunc K) p =
      algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) 1 := by
    rw [map_one, div_one]
  rw [hp, derivAux_div p 1 one_ne_zero]
  simp

theorem derivAux_add {K : Type*} [Field K] (x y : RatFunc K) :
    derivAux K (x + y) = derivAux K x + derivAux K y := by
  have hx := (RatFunc.num_div_denom x).symm
  have hy := (RatFunc.num_div_denom y).symm
  have hx0 : algebraMap (Polynomial K) (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero x)
  have hy0 : algebraMap (Polynomial K) (RatFunc K) y.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero y)
  conv_lhs => rw [hx, hy, div_add_div _ _ hx0 hy0]
  simp_rw [← map_mul, ← map_add]
  rw [derivAux_div _ _ (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))]
  conv_rhs =>
    rw [hx, derivAux_div _ _ (RatFunc.denom_ne_zero x),
      hy, derivAux_div _ _ (RatFunc.denom_ne_zero y)]
  simp only [Polynomial.derivative_mul, map_add, map_sub, map_mul, map_pow]
  field_simp [hx0, hy0]; ring

theorem derivAux_mul {K : Type*} [Field K] (x y : RatFunc K) :
    derivAux K (x * y) = x * derivAux K y + y * derivAux K x := by
  have hx := (RatFunc.num_div_denom x).symm
  have hy := (RatFunc.num_div_denom y).symm
  have hx0 : algebraMap (Polynomial K) (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero x)
  have hy0 : algebraMap (Polynomial K) (RatFunc K) y.denom ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (RatFunc.denom_ne_zero y)
  conv_lhs => rw [hx, hy, div_mul_div_comm]
  simp_rw [← map_mul]
  rw [derivAux_div _ _ (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y))]
  conv_rhs =>
    rw [hx, derivAux_div _ _ (RatFunc.denom_ne_zero x),
      hy, derivAux_div _ _ (RatFunc.denom_ne_zero y)]
  simp only [Polynomial.derivative_mul, map_add, map_sub, map_mul, map_pow]
  field_simp [hx0, hy0]; ring

/-- The formal differentiation operator `d/dX` on `RatFunc K` as a `K`-derivation. -/
noncomputable def derivation (K : Type*) [Field K] : Derivation K (RatFunc K) (RatFunc K) :=
  Derivation.mk'
    { toFun := derivAux K
      map_add' := derivAux_add
      map_smul' := fun r x ↦ by
        have hr : derivAux K (algebraMap K (RatFunc K) r) = 0 := by
          rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) r,
            Polynomial.algebraMap_eq, derivAux_algebraMap, Polynomial.derivative_C, map_zero]
        simp only [RingHom.id_apply, Algebra.smul_def, derivAux_mul, hr, mul_zero, add_zero] }
    fun x y ↦ by simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, derivAux_mul]

/-- Quotient rule for `RatFunc.derivation` on fractions `a / b` with `b ≠ 0`. -/
theorem derivation_div {K : Type*} [Field K] (a b : Polynomial K) (hb : b ≠ 0) :
    derivation K
        (algebraMap (Polynomial K) (RatFunc K) a / algebraMap (Polynomial K) (RatFunc K) b) =
      algebraMap (Polynomial K) (RatFunc K) (a.derivative * b - a * b.derivative) /
        algebraMap (Polynomial K) (RatFunc K) (b ^ 2) :=
  derivAux_div a b hb

@[simp]
theorem derivation_algebraMap {K : Type*} [Field K] (p : Polynomial K) :
    derivation K (algebraMap (Polynomial K) (RatFunc K) p) =
      algebraMap (Polynomial K) (RatFunc K) p.derivative :=
  derivAux_algebraMap p

@[simp]
theorem derivation_X {K : Type*} [Field K] : derivation K RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X, derivation_algebraMap, Polynomial.derivative_X, map_one]

end RatFunc
