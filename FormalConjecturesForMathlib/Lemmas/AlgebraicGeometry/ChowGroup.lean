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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ChowGroup

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.OrderOfVanishing
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Chow groups of schemes

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ChowGroup`.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace CodimensionCycle

variable {X : Scheme.{u}} {p : ℕ}

end CodimensionCycle

namespace PrincipalDivisor

variable {X : Scheme.{u}} {p : ℕ} (D : PrincipalDivisor X p)

@[simp]
lemma divisor_apply (x : D.carrier) : D.divisor x = D.orderFunction x := rfl

end PrincipalDivisor

lemma mem_rationalEquivalenceSubgroup_iff {X : Scheme.{u}} {p : ℕ}
    (c : CodimensionCycle X p) :
    c ∈ rationalEquivalenceSubgroup X p ↔
      c.1 ∈ principalDivisorSubgroup X p :=
  Iff.rfl

namespace ChowGroup

variable {X : Scheme.{u}} {p : ℕ}

@[simp]
lemma mk_zero : mk (0 : CodimensionCycle X p) = 0 := rfl

@[simp]
lemma mk_add (a b : CodimensionCycle X p) : mk (a + b) = mk a + mk b := rfl

@[simp]
lemma mk_neg (a : CodimensionCycle X p) : mk (-a) = -mk a := rfl

/-- Two cycles have the same Chow class exactly when their difference is rationally equivalent
to zero. -/
lemma mk_eq_mk_iff {a b : CodimensionCycle X p} :
    mk a = mk b ↔ a - b ∈ rationalEquivalenceSubgroup X p :=
  QuotientAddGroup.eq_iff_sub_mem

/-- A cycle represents zero exactly when it is rationally equivalent to zero. -/
@[simp]
lemma mk_eq_zero_iff (a : CodimensionCycle X p) :
    mk a = 0 ↔ a ∈ rationalEquivalenceSubgroup X p :=
  QuotientAddGroup.eq_zero_iff a

/-- Every pure-codimension proper pushforward of a principal divisor is zero in the Chow group. -/
@[simp]
lemma mk_principalDivisor (D : PrincipalDivisor X p)
    (h : ∀ y, D.pushforwardCycle y ≠ 0 → coheight y = p) :
    mk (D.pushforward h) = 0 := by
  rw [mk_eq_zero_iff]
  change D.pushforwardCycle ∈ principalDivisorSubgroup X p
  exact AddSubgroup.subset_closure (Set.mem_range_self D)

/-- Every Chow class on the empty scheme is zero. -/
lemma eq_zero_of_isEmpty [IsEmpty X] (z : ChowGroup X p) : z = 0 :=
  Subsingleton.elim _ _

@[simp]
lemma toRational_apply (z : ChowGroup X p) : toRational z = 1 ⊗ₜ[ℤ] z := rfl

@[simp]
lemma toRational_zero : toRational (0 : ChowGroup X p) = 0 := map_zero _

@[simp]
lemma toRational_add (a b : ChowGroup X p) :
    toRational (a + b) = toRational a + toRational b :=
  map_add _ _ _

/-- Every rational Chow class on the empty scheme is zero. -/
lemma rational_eq_zero_of_isEmpty [IsEmpty X] (z : RationalChowGroup X p) : z = 0 :=
  Subsingleton.elim _ _

/-- The generic-point generator maps to its coefficient under `CH⁰(X) ≃ ℤ`. -/
@[simp] lemma integralEquiv_mk_single (X : Scheme.{u}) [IsIntegral X] (n : ℤ) :
    integralEquiv X
      (mk (CodimensionCycle.single (genericPoint X)
        (Order.IsMax.coheight_eq_zero isMax_top) n)) = n := by
  change CodimensionCycle.single (genericPoint X)
    (Order.IsMax.coheight_eq_zero isMax_top) n (genericPoint X) = n
  exact CodimensionCycle.single_same (genericPoint X) _ _

/-- The rational generic-point generator maps to its coefficient under `CH⁰(X)_ℚ ≃ ℚ`. -/
@[simp] lemma rationalIntegralEquiv_toRational_single
    (X : Scheme.{u}) [IsIntegral X] (n : ℤ) :
    rationalIntegralEquiv X
      (toRational (mk (CodimensionCycle.single (genericPoint X)
        (Order.IsMax.coheight_eq_zero isMax_top) n))) = n := by
  change (integralEquiv X (mk (CodimensionCycle.single (genericPoint X)
    (Order.IsMax.coheight_eq_zero isMax_top) n)) : ℤ) • (1 : ℚ) = n
  rw [integralEquiv_mk_single]
  simp

/-- Every rational codimension-zero Chow class is a rational multiple of the generic-point
generator. -/
lemma rational_eq_smul_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (z : RationalChowGroup X 0) :
    z = rationalIntegralEquiv X z •
      toRational
        (mk (CodimensionCycle.single (genericPoint X)
          (Order.IsMax.coheight_eq_zero isMax_top) 1)) := by
  apply (rationalIntegralEquiv X).injective
  rw [map_smul, rationalIntegralEquiv_toRational_single]
  simp

/-- The generator with coefficient `n` maps to `n` under the calculation
`CH⁰(Spec K) ≃ ℤ`. -/
@[simp]
lemma specFieldEquiv_mk_single (K : Type u) [Field K] (n : ℤ) :
    specFieldEquiv K
      (mk (CodimensionCycle.single default
        (CodimensionCycle.specField_coheight K default) n)) = n := by
  change CodimensionCycle.single default
    (CodimensionCycle.specField_coheight K default) n default = n
  exact CodimensionCycle.single_same default _ _

/-- The same generator maps to `n : ℚ` after extending coefficients. -/
@[simp]
lemma rationalSpecFieldEquiv_toRational_single (K : Type u) [Field K] (n : ℤ) :
    rationalSpecFieldEquiv K
      (toRational (mk (CodimensionCycle.single default
        (CodimensionCycle.specField_coheight K default) n))) = n := by
  change (specFieldEquiv K (mk (CodimensionCycle.single default
    (CodimensionCycle.specField_coheight K default) n)) : ℤ) • (1 : ℚ) = n
  rw [specFieldEquiv_mk_single]
  simp

end ChowGroup

end AlgebraicGeometry
