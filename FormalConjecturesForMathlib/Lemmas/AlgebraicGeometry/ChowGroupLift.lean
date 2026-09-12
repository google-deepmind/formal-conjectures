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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ChowGroupLift

/-!
# Descending a map on cycles to the Chow group

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ChowGroupLift`.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

@[simp] lemma compactCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    (c : AlgebraicCycle X ℤ) (x : X) : compactCycleToFinsupp c x = c x :=
  rfl

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

/-- Evaluation of a descended additive map on a represented Chow class. -/
@[simp] lemma liftCycleClass_mk {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) (z : CodimensionCycle X p) :
    liftCycleClass f h (mk z) = f z :=
  QuotientAddGroup.lift_mk' _ h z

@[simp] lemma rationalExtension_tmul {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M)
    (q : ℚ) (z : ChowGroup X p) :
    rationalExtension f (q ⊗ₜ[ℤ] z) = q • f z :=
  rfl

end ChowGroup

end AlgebraicGeometry
