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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ChowGroup

/-!
# Descending a map on cycles to the Chow group

A map defined on codimension-`p` cycles descends to the Chow group as soon as it vanishes on
rational equivalences, and extends to the rational Chow group by scalar extension. This file
records both steps, and the elementary map on cycles that sends a cycle of a compact scheme to
the combination of the classes of its components.

Nothing here is a cycle-class map yet: the vanishing on rational equivalences is a hypothesis
throughout, supplied by whoever constructs the map on cycles.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- On a compact scheme, regard a locally finite integral algebraic cycle as a finitely supported
function. -/
def compactCycleToFinsupp {X : Scheme.{u}} [CompactSpace X] :
    AlgebraicCycle X ℤ →+ X →₀ ℤ where
  toFun c := Finsupp.ofSupportFinite c
    (by
      simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
        (W := Set.univ) isCompact_univ)
  map_zero' := by
    ext
    rfl
  map_add' _ _ := by
    ext
    rfl

@[simp] lemma compactCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    (c : AlgebraicCycle X ℤ) (x : X) : compactCycleToFinsupp c x = c x :=
  rfl

/-- Extend prescribed classes of irreducible codimension-`p` components additively to integral
codimension-`p` cycles. Values away from codimension `p` are set to zero; the support condition on
a `CodimensionCycle` ensures that this branch is never used by a nonzero coefficient. -/
def cycleClassOnCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    CodimensionCycle X p →+ M := by
  classical
  let componentValue : X → M := fun x ↦
    if hx : coheight x = p then componentClass x hx else 0
  exact (Finsupp.linearCombination ℤ componentValue).toAddMonoidHom.comp
    ((compactCycleToFinsupp (X := X)).comp (codimensionCycleInclusion X p))

/-- The additive extension sends a one-component cycle to its coefficient times the prescribed
component class. -/
@[simp] lemma cycleClassOnCyclesOfComponents_single
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (x : X) (hx : coheight x = p) (n : ℤ) :
    cycleClassOnCyclesOfComponents componentClass
        (CodimensionCycle.single x hx n) =
      n • componentClass x hx := by
  classical
  change (Finsupp.linearCombination ℤ (fun y ↦
      if hy : coheight y = p then componentClass y hy else 0))
    (compactCycleToFinsupp ((codimensionCycleInclusion X p)
      (CodimensionCycle.single x hx n))) = n • componentClass x hx
  have hsingle : compactCycleToFinsupp
      ((codimensionCycleInclusion X p) (CodimensionCycle.single x hx n)) =
      Finsupp.single x n := by
    ext y
    change CodimensionCycle.single x hx n y = Finsupp.single x n y
    rw [CodimensionCycle.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsingle, Finsupp.linearCombination_single, dif_pos hx]

namespace ChowGroup

/-- An additive map on codimension cycles that vanishes on rational equivalences descends to the
Chow group. -/
def liftCycleClass {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) : ChowGroup X p →+ M :=
  QuotientAddGroup.lift (rationalEquivalenceSubgroup X p) f h

/-- Evaluation of a descended additive map on a represented Chow class. -/
@[simp] lemma liftCycleClass_mk {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) (z : CodimensionCycle X p) :
    liftCycleClass f h (mk z) = f z :=
  QuotientAddGroup.lift_mk' _ h z

/-- The bilinear map used to extend an integral Chow-group map over rational coefficients. -/
def rationalExtensionBilinear {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M) :
    ℚ →ₗ[ℚ] ChowGroup X p →ₗ[ℤ] M where
  toFun q := q • f.toIntLinearMap
  map_add' _ _ := by
    ext
    simp [add_smul]
  map_smul' _ _ := by
    ext
    simp [mul_smul]

/-- Extend an additive map on the integral Chow group over rational coefficients. -/
def rationalExtension {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M) :
    RationalChowGroup X p →ₗ[ℚ] M :=
  TensorProduct.AlgebraTensorModule.lift (rationalExtensionBilinear f)

@[simp] lemma rationalExtension_tmul {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M)
    (q : ℚ) (z : ChowGroup X p) :
    rationalExtension f (q ⊗ₜ[ℤ] z) = q • f z :=
  rfl

end ChowGroup

end AlgebraicGeometry
