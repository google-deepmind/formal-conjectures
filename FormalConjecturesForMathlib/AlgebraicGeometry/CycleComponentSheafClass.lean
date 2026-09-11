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

public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentSupportExtension
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSingularCohomologySheafComparison

/-!
# Constructed sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is
transported to the actual supported cohomology sheaf. Lowest-degree purity
and the proved unique extension across the singular boundary then give an
actual supported class on the original ambient variety. Forgetting support
lands in the repository's ordinary rational cohomology.

All comparison maps, purity statements, and extension isomorphisms are
constructed. No fundamental-class, orientation, duality, or vanishing datum
is an argument. The corresponding Borel–Moore fundamental class is obtained
through the previously constructed complex-orientation duality for the actual
ambient chain sheaf. This does not assert intrinsic compactification
independence or rational-equivalence invariance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The actual supported injective cohomology sheaf is the sheaf of local
relative cohomology, by the constructed singular resolution and its literal
restriction-natural comparison. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  exact (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

variable (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

/-- Supported cohomology on the full component is identified with sections
of the local relative-cohomology sheaf on its smooth-locus ambient open.
Each of the three arrows is an actual proved isomorphism. -/
def cycleComponentSupportedClassNormalizationIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.obj
          (op (cycleComponentSmoothSupportAmbientOpen X x)) := by
  refine cycleComponentSupportExtensionIso X x (d := d) hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x (d := d) hx ≪≫ ?_
  let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p))
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  dsimp only [TopCat.Sheaf.supportEvaluation, Functor.comp_obj] at e
  rw [he] at e
  exact e

/-- The actual globally supported class extending the exact complex-normal
coclass. The inverse is that of the proved normalization isomorphism. -/
def cycleComponentSupportedInjectiveClass :
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ)) :=
  (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).inv
    (cycleComponentSmoothSupportCoclassSection X x (d := d) hx)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).hom
      (cycleComponentSupportedInjectiveClass X x (d := d) hx) =
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx :=
  (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).addCommGroupIsoToAddEquiv.apply_symm_apply _

/-- The normalized global extension is unique, by injectivity of the actual
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ)))
    (ha : (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).hom a =
      cycleComponentSmoothSupportCoclassSection X x (d := d) hx) :
    a = cycleComponentSupportedInjectiveClass X x (d := d) hx :=
  (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).addCommGroupIsoToAddEquiv.injective
    (ha.trans (cycleComponentSupportedInjectiveClass_normalization X x (d := d) hx).symm)

/-- The constructed class in the existing support-cone presentation. Its
comparison includes the proved cone sign required by actual support forgetting. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x (d := d) hx)

/-- The unconditional ordinary class of an arbitrary integral component.
This uses the literal inclusion of supported injective sections. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
        (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
      (cycleComponentSupportedInjectiveClass X x (d := d) hx))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary class agrees with the repository's support-forgetting map,
through the constructed, sign-correct support comparison. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x (d := d) hx =
      forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
        (cycleComponentSheafSupportedClass X x (d := d) hx) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [cycleComponentSheafClass, cycleComponentSheafSupportedClass,
    AddEquiv.apply_symm_apply]
  rfl

include X hx in
omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The actual dimension bound needed for the Borel–Moore degree, not an extra input. -/
theorem cycleComponentSheafClass_codimension_le : p ≤ d := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := d) x
  rw [hx] at h
  exact_mod_cast h

/-- The normalized fundamental class in ACTUAL ambient chain-sheaf
Borel–Moore homology, obtained through the constructed orientation shift.
It is not an element of a supplied replacement homology group. -/
def cycleComponentSheafBorelMooreFundamentalClass :
    ComplexAmbientSheafBorelMooreHomology X d (cycleComponentAnalyticClosedSupport X x)
      (2 * ((d - p : ℕ) : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
    (cycleComponentAnalyticClosedSupport X x) p
    (cycleComponentSheafClass_codimension_le X x (d := d) hx)).symm
      (cycleComponentSheafSupportedClass X x (d := d) hx)

/-- The constructed Alexander–Poincaré map sends the fundamental class to
the exact normalized supported class, with no comparison hypothesis. -/
@[simp]
theorem cycleComponentSheafBorelMooreFundamentalClass_duality :
    complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafSupportedClass X x (d := d) hx :=
  AddEquiv.apply_symm_apply _ _

/-- The ordinary class is also exactly the actual ambient Borel–Moore
cycle-class route. The ordinary-target comparison is proved, not an input. -/
theorem cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology :
    complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafClass X x (d := d) hx := by
  change forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx)) = _
  rw [cycleComponentSheafBorelMooreFundamentalClass_duality,
    cycleComponentSheafClass_eq_forgetSupport]

end AlgebraicGeometry.ComplexPoint
