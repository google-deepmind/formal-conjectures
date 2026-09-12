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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ChowGroup
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

namespace ChowGroup

/-- An additive map on codimension cycles that vanishes on rational equivalences descends to the
Chow group. -/
def liftCycleClass {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) : ChowGroup X p →+ M :=
  QuotientAddGroup.lift (rationalEquivalenceSubgroup X p) f h

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

end ChowGroup

end AlgebraicGeometry
