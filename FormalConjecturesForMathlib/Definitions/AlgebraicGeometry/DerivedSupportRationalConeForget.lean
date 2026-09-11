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

public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.HypercohomologyGlobalSectionsShift

/-! # Support-forgetting in the actual rational injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Ordinary rational cohomology computed by the actual ambient rational
injective resolution. This has the ordinary augmentation normalization. -/
def rationalCohomologyAddEquivAmbientInjectiveHomology (n : ℤ) :
    H^n(X; ℚ) ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology n := by
  let e : H^n(X; ℚ) ≃+
      Hypercohomology X (ambientRationalInjectiveComplex X) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (ambientRationalInjectiveAugmentation X)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' α β := (hypercohomologyMap X
        (ambientRationalInjectiveAugmentation X) n).map_add α β }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X _ n)

end AlgebraicGeometry.ComplexPoint
