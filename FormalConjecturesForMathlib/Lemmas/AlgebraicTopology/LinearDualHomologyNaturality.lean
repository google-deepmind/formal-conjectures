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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LinearDualHomologyNaturality

/-!
# LinearDualHomologyNaturality

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LinearDualHomologyNaturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients is the literal evaluation of an actual dual
cycle on an actual cycle. -/
lemma linearDualHomologyEquiv_homologyπ_apply (S : ShortComplex (ModuleCat.{u} R))
    (φ : S.linearDual.cycles) (z : S.cycles) :
    S.linearDualHomologyEquiv (S.linearDual.homologyπ φ) (S.homologyπ z) =
      (show Module.Dual R S.X₂ from S.linearDual.iCycles φ) (S.iCycles z) := by
  change S.dualHomologyComparisonExplicit
    (S.linearDual.moduleCatHomologyIso.hom (S.linearDual.homologyπ φ))
    (S.moduleCatHomologyIso.hom (S.homologyπ z)) = _
  have hφ := ConcreteCategory.congr_hom (π_moduleCatCyclesIso_hom S.linearDual) φ
  have hz := ConcreteCategory.congr_hom (π_moduleCatCyclesIso_hom S) z
  change S.linearDual.moduleCatHomologyIso.hom (S.linearDual.homologyπ φ) =
    Submodule.Quotient.mk (S.linearDual.moduleCatCyclesIso.hom φ) at hφ
  change S.moduleCatHomologyIso.hom (S.homologyπ z) =
    Submodule.Quotient.mk (S.moduleCatCyclesIso.hom z) at hz
  rw [hφ, hz]
  change (show Module.Dual R S.X₂ from (S.linearDual.moduleCatCyclesIso.hom φ).val)
    (S.moduleCatCyclesIso.hom z).val = _
  have hφ' := ConcreteCategory.congr_hom (moduleCatCyclesIso_hom_i S.linearDual) φ
  have hz' := ConcreteCategory.congr_hom (moduleCatCyclesIso_hom_i S) z
  change (S.linearDual.moduleCatCyclesIso.hom φ).val = S.linearDual.iCycles φ at hφ'
  change (S.moduleCatCyclesIso.hom z).val = S.iCycles z at hz'
  rw [hφ', hz']

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degreewise short-complex dual identification preserves actual maps. -/
lemma linearDualCochainComplexScIso_naturality (f : K ⟶ L) (n : ℕ) :
    (shortComplexFunctor (ModuleCat R) (.up ℕ) n).map (linearDualMap f) ≫
      (linearDualCochainComplexScIso K n).hom =
    (linearDualCochainComplexScIso L n).hom ≫
      ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f) := by
  ext <;> cases n <;>
    simp [linearDualCochainComplexScIso, isoSc', linearDualMap,
      ShortComplex.linearDualMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient identification intertwines the actual dual
cochain map with the dual of the actual homology map. -/
lemma linearDualHomologyEquiv_naturality (f : K ⟶ L) (n : ℕ)
    (a : L.linearDualCochainComplex.homology n) (z : K.homology n) :
    linearDualHomologyEquiv K n (homologyMap (linearDualMap f) n a) z =
      linearDualHomologyEquiv L n a (homologyMap f n z) := by
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat R)).map
    (linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have ha := ConcreteCategory.congr_hom h a
  change (K.sc n).linearDualHomologyEquiv
    (ShortComplex.homologyMap (linearDualCochainComplexScIso K n).hom
      (homologyMap (linearDualMap f) n a)) z = _
  rw [show ShortComplex.homologyMap (linearDualCochainComplexScIso K n).hom
      (homologyMap (linearDualMap f) n a) =
    ShortComplex.homologyMap
      (ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f))
      (ShortComplex.homologyMap (linearDualCochainComplexScIso L n).hom a) from ha]
  exact congrArg (fun α => α z) (ShortComplex.linearDualHomologyEquiv_naturality _ _)

end HomologicalComplex
