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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularFlasqueSupportModel
public import FormalConjecturesForMathlib.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationParacompact

/-!
# Supported singular models on smooth projective complex varieties

The generic supported singular/injective comparison is specialized using the
constructed analytic contractible neighborhoods and hereditary paracompactness
of smooth projective analytifications. Only the geometric scheme hypotheses
remain: no purity, fundamental class, or comparison equivalence is an input.
The target is literally the ambient injective complex used by the derived
rational support comparison.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom]

/-- The actual singular-to-injective resolution map, using proved local
contractibility of the analytic space. -/
def complexSingularToAmbientInjective :
    rationalSingularCochainComplex (TopCat.of (ComplexPoint X)) ⟶
      ambientRationalInjectiveComplex X :=
  singularToConstantInjectiveComplex (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X)

instance complexSingularToAmbientInjective_quasiIso :
    QuasiIso (complexSingularToAmbientInjective X) :=
  singularToConstantInjectiveComplex_quasiIso _ _

/-- Its actual supported version for any open complement, not just a smooth support. -/
def complexSupportedSingularToAmbientInjective
    (U : Opens (ComplexPoint X)) :
    supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) U ⟶
      ((TopCat.Sheaf.sheafSectionsSupportedOutside
        (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
          (ambientRationalInjectiveComplex X) :=
  supportedSingularToInjectiveComplex (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X) U

variable [IsProjective X.hom]

/-- The constructed supported comparison is a sheaf quasi-isomorphism under
the usual smooth projective geometry hypotheses alone. -/
instance complexSupportedSingularToAmbientInjective_quasiIso
    (U : Opens (ComplexPoint X)) :
    QuasiIso (complexSupportedSingularToAmbientInjective X U) := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V :=
    openParacompactSpace X
  exact supportedSingularToInjectiveComplex_quasiIso
    (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X) U

/-- The same comparison computes supported cohomology on every actual analytic
open, with no locally supplied comparison or acyclicity input. -/
theorem complexSupportedSingularToAmbientInjective_onOpen_quasiIso
    (U V : Opens (ComplexPoint X)) :
    QuasiIso (((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex (.up ℤ)).map
        (complexSupportedSingularToAmbientInjective X U)) := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W :=
    openParacompactSpace X
  exact supportedSingularToInjectiveComplex_onOpen_quasiIso
    (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X) U V

/-- Local supported singular cohomology and the literal supported injective
model are canonically isomorphic in every integer degree. -/
def complexSupportedSingularInjectiveHomologyIso
    (U V : Opens (ComplexPoint X)) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside
          (TopCat.of (ComplexPoint X)) U).mapHomologicalComplex (.up ℤ)).obj
            (ambientRationalInjectiveComplex X)))).homology n := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W :=
    openParacompactSpace X
  exact supportedSingularInjectiveHomologyIso (TopCat.of (ComplexPoint X))
    (exists_contractibleOpen_le X) U V n

end AlgebraicGeometry.ComplexPoint
