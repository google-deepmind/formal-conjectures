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

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

import FormalConjecturesForMathlib.AlgebraicGeometry.OrderOfVanishing
import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Chow groups of schemes

This file constructs codimension-`p` cycles and their quotient by rational equivalence. A principal
relation is the proper pushforward of the divisor of a nonzero rational function on an integral
Noetherian closed subscheme of codimension `p - 1`.

The definition uses `Scheme.ord` for orders of vanishing and `AlgebraicCycle.map` for proper
pushforward. Principal divisors first generate a subgroup of all algebraic cycles. Its pullback to
the codimension-`p` cycle group imposes the grading without requiring an extra codimension proof on
each generator.
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The subgroup of algebraic cycles supported at points of codimension `p`. -/
def codimensionCycleSubgroup (X : Scheme.{u}) (p : ℕ) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier c := ∀ x, c x ≠ 0 → coheight x = p
  zero_mem' x hx := (hx rfl).elim
  add_mem' := by
    intro a b ha hb x hx
    by_cases hax : a x = 0
    · exact hb x (by simpa [hax] using hx)
    · exact ha x hax
  neg_mem' := by
    intro a ha x hx
    refine ha x fun h ↦ hx ?_
    change -(a x) = 0
    simp [h]

/-- The additive group of codimension-`p` algebraic cycles on `X`. -/
abbrev CodimensionCycle (X : Scheme.{u}) (p : ℕ) := codimensionCycleSubgroup X p

instance (X : Scheme.{u}) (p : ℕ) : CoeFun (CodimensionCycle X p) (fun _ ↦ X → ℤ) where
  coe c := c.1

namespace CodimensionCycle

variable {X : Scheme.{u}} {p : ℕ}

@[ext]
lemma ext {a b : CodimensionCycle X p} (h : ∀ x, a.1 x = b.1 x) : a = b :=
  Subtype.ext (Function.locallyFinsuppWithin.ext h)

/-- The cycle with coefficient `n` at one point and zero elsewhere. -/
noncomputable def single (x : X) (hx : coheight x = p) (n : ℤ) : CodimensionCycle X p :=
  by
    classical
    exact ⟨Function.locallyFinsuppWithin.single x n, by
      intro y hy
      by_cases h : y = x
      · simpa [h] using hx
      · simp [Function.locallyFinsuppWithin.single_apply, h] at hy⟩

@[simp]
lemma single_apply [DecidableEq X] (x : X) (hx : coheight x = p) (n : ℤ) (y : X) :
    single x hx n y = if y = x then n else 0 := by
  simp [single, Function.locallyFinsuppWithin.single_apply]

@[simp]
lemma single_same (x : X) (hx : coheight x = p) (n : ℤ) : single x hx n x = n := by
  classical
  simp

@[simp]
lemma single_zero (x : X) (hx : coheight x = p) : single x hx 0 = 0 := by
  classical
  ext
  simp

/-- Every point of the spectrum of a field has codimension zero. -/
lemma specField_coheight (K : Type u) [Field K] (x : Spec ↧K) : coheight x = 0 := by
  refine Order.IsMax.coheight_eq_zero fun y _ ↦ ?_
  rw [Subsingleton.elim y x]

/-- A codimension-zero point of an integral scheme is its generic point. -/
lemma eq_genericPoint_of_coheight_zero [IsIntegral X] (x : X) (hx : coheight x = 0) :
    x = genericPoint X := by
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨Order.coheight_eq_zero.mp hx le_top, genericPoint_specializes x⟩

/-- Codimension-zero cycles on an integral scheme are determined by their generic coefficient. -/
noncomputable def integralEquiv [IsIntegral X] : CodimensionCycle X 0 ≃+ ℤ where
  toFun c := c (genericPoint X)
  invFun n := single (genericPoint X) (Order.IsMax.coheight_eq_zero isMax_top) n
  left_inv c := by
    have hgp : coheight (genericPoint X) = (0 : ℕ) :=
      Order.IsMax.coheight_eq_zero isMax_top
    change single (genericPoint X) hgp (c (genericPoint X)) = c
    refine ext fun x ↦ ?_
    classical
    by_cases hx : c x = 0
    · by_cases h : x = genericPoint X
      · subst x
        rw [single_same, hx]
      · rw [single_apply]
        simp [h, hx]
    · have hcodim := c.2 x hx
      rw [eq_genericPoint_of_coheight_zero x hcodim]
      exact single_same (genericPoint X) _ _
  right_inv n := single_same (genericPoint X) _ _
  map_add' _ _ := rfl

/-- Codimension-zero cycles on the spectrum of a field are determined by the coefficient of its
unique point. -/
noncomputable def specFieldEquiv (K : Type u) [Field K] :
    CodimensionCycle (Spec ↧K) 0 ≃+ ℤ where
  toFun c := c default
  invFun n := single default (specField_coheight K default) n
  left_inv c := by
    refine ext fun x ↦ ?_
    rw [Subsingleton.elim x (default : Spec ↧K)]
    exact single_same default _ _
  right_inv n := single_same default _ _
  map_add' _ _ := rfl

end CodimensionCycle

/--
Data defining one generator of rational equivalence in codimension `p`.

The carrier is an integral Noetherian closed subscheme of codimension `p - 1`, expressed by
`genericPoint_codimension`. The divisor of its nonzero rational function is locally finite by
`Scheme.ord_locallyFiniteSupport`.
-/
structure PrincipalDivisor (X : Scheme.{u}) (p : ℕ) where
  /-- The integral closed subscheme on which the rational function lives. -/
  carrier : Scheme.{u}
  /-- Its closed immersion into the ambient scheme. -/
  inclusion : carrier ⟶ X
  [isClosedImmersion : IsClosedImmersion inclusion]
  [isIntegral : IsIntegral carrier]
  [isNoetherian : IsNoetherian carrier]
  /-- A nonzero rational function on the integral subscheme. -/
  rationalFunction : carrier.functionField
  rationalFunction_ne_zero : rationalFunction ≠ 0
  /-- The carrier has codimension `p - 1` in the ambient scheme. -/
  genericPoint_codimension : coheight (inclusion (genericPoint carrier)) + 1 = p

namespace PrincipalDivisor

variable {X : Scheme.{u}} {p : ℕ} (D : PrincipalDivisor X p)

/-- The order-of-vanishing function determined by a principal divisor datum. -/
noncomputable def orderFunction : D.carrier → ℤ := by
  let := D.isIntegral
  let := D.isNoetherian
  exact D.carrier.ord D.rationalFunction

/-- The divisor of the rational function as an algebraic cycle on its carrier. -/
noncomputable def divisor : AlgebraicCycle D.carrier ℤ := by
  let := D.isIntegral
  let := D.isNoetherian
  exact
    { toFun := D.orderFunction
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' := by
        change ∀ x, x ∈ Set.univ → ∃ t ∈ nhds x,
          Set.Finite (t ∩ Function.support (D.carrier.ord D.rationalFunction))
        exact fun x _ ↦ D.carrier.ord_locallyFiniteSupport D.rationalFunction x }

@[simp]
lemma divisor_apply (x : D.carrier) : D.divisor x = D.orderFunction x := rfl

/-- The proper pushforward of a principal divisor to the ambient scheme. -/
noncomputable def pushforwardCycle : AlgebraicCycle X ℤ := by
  let := D.isClosedImmersion
  let := D.isIntegral
  let := D.isNoetherian
  exact AlgebraicCycle.map D.inclusion (fun _ : D.carrier ↦ ()) (fun _ : X ↦ ()) D.divisor

/-- A principal divisor known to be pure of codimension `p`, bundled as a codimension cycle. -/
noncomputable def pushforward
    (h : ∀ y, D.pushforwardCycle y ≠ 0 → coheight y = p) : CodimensionCycle X p :=
  ⟨D.pushforwardCycle, h⟩

end PrincipalDivisor

/-- The subgroup of all algebraic cycles generated by proper pushforwards of principal divisors
whose carriers have codimension `p - 1`. -/
noncomputable def principalDivisorSubgroup (X : Scheme.{u}) (p : ℕ) :
    AddSubgroup (AlgebraicCycle X ℤ) :=
  AddSubgroup.closure (Set.range fun D : PrincipalDivisor X p ↦ D.pushforwardCycle)

/-- The inclusion of pure codimension cycles into all algebraic cycles. -/
def codimensionCycleInclusion (X : Scheme.{u}) (p : ℕ) :
    CodimensionCycle X p →+ AlgebraicCycle X ℤ :=
  (codimensionCycleSubgroup X p).subtype

/-- Rational equivalences among codimension-`p` cycles. This is the intersection of the pure
codimension cycle group with the subgroup generated by all relevant principal divisors. -/
noncomputable def rationalEquivalenceSubgroup (X : Scheme.{u}) (p : ℕ) :
    AddSubgroup (CodimensionCycle X p) :=
  (principalDivisorSubgroup X p).comap (codimensionCycleInclusion X p)

lemma mem_rationalEquivalenceSubgroup_iff {X : Scheme.{u}} {p : ℕ}
    (c : CodimensionCycle X p) :
    c ∈ rationalEquivalenceSubgroup X p ↔
      c.1 ∈ principalDivisorSubgroup X p :=
  Iff.rfl

/-- There are no principal-divisor generators whose carrier has codimension `-1`. -/
@[simp]
lemma principalDivisorSubgroup_zero (X : Scheme.{u}) :
    principalDivisorSubgroup X 0 = ⊥ := by
  rw [eq_bot_iff]
  unfold principalDivisorSubgroup
  rw [AddSubgroup.closure_le]
  rintro _ ⟨D, rfl⟩
  have h := D.genericPoint_codimension
  simp at h

/-- There are no principal-divisor relations in codimension zero. -/
@[simp]
lemma rationalEquivalenceSubgroup_zero (X : Scheme.{u}) :
    rationalEquivalenceSubgroup X 0 = ⊥ := by
  ext c
  simp only [rationalEquivalenceSubgroup, principalDivisorSubgroup_zero,
    AddSubgroup.mem_comap, AddSubgroup.mem_bot]
  constructor
  · exact fun h ↦ Subtype.ext h
  · rintro rfl
    rfl

/-- The codimension-`p` Chow group: cycles modulo rational equivalence. -/
abbrev ChowGroup (X : Scheme.{u}) (p : ℕ) :=
  CodimensionCycle X p ⧸ rationalEquivalenceSubgroup X p

/-- The codimension-`p` Chow group with rational coefficients. The order of the tensor factors
gives this tensor product its canonical `ℚ`-module structure. -/
noncomputable abbrev RationalChowGroup (X : Scheme.{u}) (p : ℕ) :=
  TensorProduct ℤ ℚ (ChowGroup X p)

namespace ChowGroup

variable {X : Scheme.{u}} {p : ℕ}

/-- The class of a codimension-`p` cycle in the Chow group. -/
noncomputable def mk (c : CodimensionCycle X p) : ChowGroup X p :=
  QuotientAddGroup.mk c

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

instance codimensionCycle_subsingleton_of_isEmpty [IsEmpty X] :
    Subsingleton (CodimensionCycle X p) where
  allEq a b := CodimensionCycle.ext (a := a) (b := b) fun x ↦ isEmptyElim x

instance subsingleton_of_isEmpty [IsEmpty X] : Subsingleton (ChowGroup X p) :=
  (QuotientAddGroup.subsingleton_iff).2 <| by
    refine SetLike.ext fun a ↦ ?_
    simp only [AddSubgroup.mem_top, iff_true]
    rw [Subsingleton.elim a (0 : CodimensionCycle X p)]
    exact (rationalEquivalenceSubgroup X p).zero_mem

/-- Every Chow class on the empty scheme is zero. -/
lemma eq_zero_of_isEmpty [IsEmpty X] (z : ChowGroup X p) : z = 0 :=
  Subsingleton.elim _ _

/-- The canonical additive map from integral to rational Chow classes. -/
noncomputable def toRational : ChowGroup X p →+ RationalChowGroup X p :=
  (TensorProduct.mk ℤ ℚ (ChowGroup X p) 1).toAddMonoidHom

@[simp]
lemma toRational_apply (z : ChowGroup X p) : toRational z = 1 ⊗ₜ[ℤ] z := rfl

@[simp]
lemma toRational_zero : toRational (0 : ChowGroup X p) = 0 := map_zero _

@[simp]
lemma toRational_add (a b : ChowGroup X p) :
    toRational (a + b) = toRational a + toRational b :=
  map_add _ _ _

instance rational_subsingleton_of_isEmpty [IsEmpty X] :
    Subsingleton (RationalChowGroup X p) := by
  have key : ∀ w : RationalChowGroup X p, w = 0 := fun w ↦ by
    refine TensorProduct.induction_on w rfl ?_ ?_
    · intro q z
      rw [Subsingleton.elim z 0]
      simp
    · intro x y hx hy
      simp [hx, hy]
  exact ⟨fun a b ↦ (key a).trans (key b).symm⟩

/-- Every rational Chow class on the empty scheme is zero. -/
lemma rational_eq_zero_of_isEmpty [IsEmpty X] (z : RationalChowGroup X p) : z = 0 :=
  Subsingleton.elim _ _

/-- In codimension zero, quotienting cycles by rational equivalence changes nothing. -/
noncomputable def codimensionZeroEquiv (X : Scheme.{u}) :
    ChowGroup X 0 ≃+ CodimensionCycle X 0 :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (rationalEquivalenceSubgroup_zero X)).trans QuotientAddGroup.quotientBot

/-- The codimension-zero Chow group of an integral scheme is `ℤ`. -/
noncomputable def integralEquiv (X : Scheme.{u}) [IsIntegral X] : ChowGroup X 0 ≃+ ℤ :=
  (codimensionZeroEquiv X).trans CodimensionCycle.integralEquiv

/-- The rational codimension-zero Chow group of an integral scheme is `ℚ`. -/
noncomputable def rationalIntegralEquiv (X : Scheme.{u}) [IsIntegral X] :
    RationalChowGroup X 0 ≃ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ) (integralEquiv X).toIntLinearEquiv).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)

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

/-- The codimension-zero Chow group of the spectrum of a field is `ℤ`. -/
noncomputable def specFieldEquiv (K : Type u) [Field K] :
    ChowGroup (Spec ↧K) 0 ≃+ ℤ :=
  (codimensionZeroEquiv (Spec ↧K)).trans (CodimensionCycle.specFieldEquiv K)

/-- With rational coefficients, the codimension-zero Chow group of the spectrum of a field is
`ℚ`. -/
noncomputable def rationalSpecFieldEquiv (K : Type u) [Field K] :
    RationalChowGroup (Spec ↧K) 0 ≃ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ) (specFieldEquiv K).toIntLinearEquiv).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)

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

/-- A concrete boundary computation: every Chow group of `Spec PUnit` is trivial. -/
example (p : ℕ) : Subsingleton (ChowGroup (Spec ↧PUnit) p) := by
  let := spec_punit_isEmpty
  infer_instance

/-- A rational-coefficient version of the same boundary computation. -/
example (p : ℕ) : Subsingleton (RationalChowGroup (Spec ↧PUnit) p) := by
  let := spec_punit_isEmpty
  infer_instance

/-- A nonempty calculation: `CH⁰(Spec ℚ) ≃ ℤ`, including its distinguished generator. -/
example : specFieldEquiv ℚ
    (mk (CodimensionCycle.single default
      (CodimensionCycle.specField_coheight ℚ default) 1)) = 1 := by
  simp

/-- The rational-coefficient calculation sends the same generator to `1 : ℚ`. -/
example : rationalSpecFieldEquiv ℚ
    (toRational (mk (CodimensionCycle.single default
      (CodimensionCycle.specField_coheight ℚ default) 1))) = 1 :=
  rationalSpecFieldEquiv_toRational_single ℚ 1

end ChowGroup

end AlgebraicGeometry
