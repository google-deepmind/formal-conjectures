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

public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.HomComplexPostcompNaturality
public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison

/-! # Naturality of the hypercohomology/global-sections comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L)

end CochainComplex.HomComplex

namespace TopCat.Sheaf

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyNaturalitySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- On a K-injective sheaf complex, derived morphisms from the integer
constant sheaf are computed by actual global sections, with no further
replacement complex. -/
def derivedHomAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)))) (DerivedCategory.Q.obj K) n ≃+
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homology n :=
  (kInjectiveDerivedHomAddEquivCohomologyClass _ K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
          (TopCat.of (ComplexPoint X)) K) n).addCommGroupIsoToAddEquiv)

/-- Hypercohomology of an actual K-injective complex is its global-section
cohomology. This direct form exposes naturality without choosing another
injective resolution. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homology n :=
  (hypercohomologyAddEquivDerived X K n).trans
    ((isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans
      (derivedHomAddEquivGlobalSectionsKInjective X K n))

end AlgebraicGeometry.ComplexPoint
