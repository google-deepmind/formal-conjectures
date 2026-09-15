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

public import FormalConjecturesForMathlib.Mathlib.AlgebraicGeometry.Over.Basic
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexEtale
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Local coordinates on smooth complex schemes

Every point of a smooth scheme over `ℂ` has an affine neighborhood with an étale map to a
finite-dimensional affine space. This file constructs such coordinates from algebraic smoothness,
proves that the map is over `Spec ℂ`, and records the resulting continuous complex-valued
coordinate tuple on the corresponding analytic open set.
-/

@[expose] public section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry

open ComplexAlgHom

noncomputable section

attribute [local instance] overSpecAlgebra

@[reassoc]
lemma Scheme.Opens.ι_appTop_topIso_hom {Y : Scheme} (U : Y.Opens) :
    U.ι.appTop ≫ U.topIso.hom =
      Y.presheaf.map (homOfLE (show U ≤ (⊤ : Y.Opens) from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  let a : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (U.ι ''ᵁ ⊤) :=
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ (⊤ : Y.Opens) from le_top)).op
  let b : Opposite.op (U.ι ''ᵁ ⊤) ⟶ Opposite.op U :=
    (eqToHom U.ι_image_top.symm).op
  let c : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op U :=
    (homOfLE (show U ≤ (⊤ : Y.Opens) from le_top)).op
  change Y.presheaf.map a ≫ Y.presheaf.map b = Y.presheaf.map c
  rw [← Y.presheaf.map_comp]
  exact congrArg Y.presheaf.map (Subsingleton.elim (a ≫ b) c)

section SchemeStructure

variable {Y : Scheme} (f : Y ⟶ Spec ↧ℂ)

lemma Smooth.exists_affine_isStandardSmooth [Smooth f] (x : Y) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      (f.appLE ⊤ V (by simp)).hom.IsStandardSmooth := by
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := le_antisymm le_top fun y _ ↦ by
    rw [show y = f x from Subsingleton.elim _ _]
    exact e hxV
  subst U
  exact ⟨V, hV, hxV, hf⟩

variable (X : Over (Spec ↧ℂ))

lemma algebraMap_isStandardSmooth {V : X.left.Opens}
    (h : (X.hom.appLE ⊤ V (by simp)).hom.IsStandardSmooth) :
    (algebraMap ℂ Γ(X.left, V)).IsStandardSmooth := by
  exact RingHom.isStandardSmooth_respectsIso.2 _
    (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv h

lemma SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
    {d : ℕ} [SmoothOfRelativeDimension d f] (x : Y) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      (f.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := f) x
  have hUtop : U = ⊤ := le_antisymm le_top fun y _ ↦ by
    rw [show y = f x from Subsingleton.elim _ _]
    exact e hxV
  subst U
  exact ⟨V, hV, hxV, hf⟩

lemma algebraMap_isStandardSmoothOfRelativeDimension {d : ℕ} {V : X.left.Opens}
    (h : (X.hom.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension d) :
    (algebraMap ℂ Γ(X.left, V)).IsStandardSmoothOfRelativeDimension d := by
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso ↧ℂ).symm.commRingCatIsoToRingEquiv h

end SchemeStructure

variable (X : Over (Spec ↧ℂ))

noncomputable local instance {Y : Over (Spec ↧ℂ)} :
    TopologicalSpace (ComplexPoint Y) := Point.analyticTopology

/-- Étale algebraic coordinates of the specified relative dimension around a point of a smooth
complex scheme. -/
structure LocalEtaleCoordinates (d : ℕ) [SmoothOfRelativeDimension d X.hom] (x : X.left) where
  /-- An affine open neighborhood. -/
  neighborhood : X.left.Opens
  /-- The neighborhood is affine. -/
  isAffine : IsAffineOpen neighborhood
  /-- The chosen point belongs to the neighborhood. -/
  mem : x ∈ neighborhood
  /-- The étale coordinate homomorphism over the complex numbers. -/
  coordinateAlgHom : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, neighborhood)
  /-- The coordinate homomorphism is étale. -/
  etale : coordinateAlgHom.toRingHom.Etale

/-- Smoothness of relative dimension `d` supplies `d` étale algebraic coordinates around every
point. -/
lemma nonempty_localEtaleCoordinates (d : ℕ) [SmoothOfRelativeDimension d X.hom] (x : X.left) :
    Nonempty (LocalEtaleCoordinates X d x) := by
  obtain ⟨V, hV, hxV, hf⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := d) X.hom x
  have hf' := algebraMap_isStandardSmoothOfRelativeDimension (d := d) X hf
  obtain ⟨g, hC, hg⟩ := hf'.exists_etale_mvPolynomial
  let g' : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, V) :=
    { toRingHom := g
      commutes' := fun c ↦ DFunLike.congr_fun hC c }
  exact ⟨⟨V, hV, hxV, g', hg⟩⟩

/-- A choice of the `d` étale algebraic coordinates constructed from relative-dimensional
smoothness. -/
def localEtaleCoordinates (d : ℕ) [SmoothOfRelativeDimension d X.hom] (x : X.left) :
    LocalEtaleCoordinates X d x :=
  Classical.choice (nonempty_localEtaleCoordinates X d x)

namespace LocalEtaleCoordinates

variable {X} {d : ℕ} [SmoothOfRelativeDimension d X.hom] {x : X.left}
  (D : LocalEtaleCoordinates X d x)

/-- The coordinate ring map after identifying sections on an open with its global sections. -/
def coordinateRingHomOnOpen :
    MvPolynomial (Fin d) ℂ →+* Γ(D.neighborhood.toScheme, ⊤) :=
  D.neighborhood.topIso.inv.hom.comp D.coordinateAlgHom.toRingHom

lemma coordinateRingHomOnOpen_etale : D.coordinateRingHomOnOpen.Etale := by
  exact RingHom.Etale.respectsIso.1 D.coordinateAlgHom.toRingHom
    D.neighborhood.topIso.symm.commRingCatIsoToRingEquiv D.etale

lemma C_comp_coordinateRingHomOnOpen :
    CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom D.coordinateRingHomOnOpen =
      (Scheme.ΓSpecIso ↧ℂ).inv ≫ (D.neighborhood.ι ≫ X.hom).appTop := by
  apply (cancel_mono D.neighborhood.topIso.hom).mp
  change (((CommRingCat.ofHom MvPolynomial.C) ≫
      CommRingCat.ofHom D.coordinateAlgHom.toRingHom) ≫ D.neighborhood.topIso.inv) ≫
        D.neighborhood.topIso.hom =
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫
      (D.neighborhood.ι ≫ X.hom).appTop) ≫ D.neighborhood.topIso.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [Scheme.Opens.ι_appTop_topIso_hom]
  change CommRingCat.ofHom (D.coordinateAlgHom.toRingHom.comp MvPolynomial.C) =
    CommRingCat.ofHom (algebraMap ℂ Γ(X.left, D.neighborhood))
  exact congrArg CommRingCat.ofHom D.coordinateAlgHom.comp_algebraMap

/-- The scheme morphism defined by the étale coordinates. -/
def toAffineSpace : D.neighborhood.toScheme ⟶
    ComplexPoint.complexAffineSpace (Fin d) :=
  D.neighborhood.toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen) ≫
      (AffineSpace.SpecIso (Fin d) ↧ℂ).inv

lemma etale_toAffineSpace : Etale D.toAffineSpace := by
  have h₁ : Etale D.neighborhood.toScheme.toSpecΓ := by
    let : IsAffine D.neighborhood.toScheme := D.isAffine
    infer_instance
  have h₂ : Etale (Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen)) :=
    HasRingHomProperty.Spec_iff.mpr D.coordinateRingHomOnOpen_etale
  have h₃ : Etale (AffineSpace.SpecIso (Fin d) ↧ℂ).inv := inferInstance
  exact @Etale.etale_comp _ _ _ _ _ h₁ (@Etale.etale_comp _ _ _ _ _ h₂ h₃)

/-- The étale coordinate morphism respects the structure maps to `Spec ℂ`. -/
lemma toAffineSpace_over :
    D.toAffineSpace ≫
        (ComplexPoint.complexAffineSpace (Fin d) ↘ Spec ↧ℂ) =
      D.neighborhood.ι ≫ X.hom := by
  simp only [toAffineSpace, Category.assoc, AffineSpace.SpecIso_inv_over]
  let φ : ↧ℂ ⟶ Γ(D.neighborhood.toScheme, ⊤) :=
    CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom D.coordinateRingHomOnOpen
  have hSpec : Spec.map (CommRingCat.ofHom D.coordinateRingHomOnOpen) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) = Spec.map φ := by
    rw [← Spec.map_comp]
    rfl
  refine (congrArg (fun q ↦ D.neighborhood.toScheme.toSpecΓ ≫ q) hSpec).trans ?_
  change (ΓSpec.adjunction.homEquiv D.neighborhood.toScheme
    (Opposite.op ↧ℂ)) φ.op = D.neighborhood.ι ≫ X.hom
  apply ext_to_Spec
  exact (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ).trans
    D.C_comp_coordinateRingHomOnOpen

/-- The étale coordinate morphism bundled over the complex base. -/
abbrev toAffineSpaceOver :
    ComplexPoint.openScheme X D.neighborhood ⟶
      Over.mk (ComplexPoint.complexAffineSpace (Fin d) ↘ Spec ↧ℂ) :=
  Over.homMk D.toAffineSpace D.toAffineSpace_over

/-- The map on complex points induced by the étale coordinate morphism. -/
def pointMap :
    ComplexPoint (ComplexPoint.openScheme X D.neighborhood) →
      ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin d) ↘ Spec ↧ℂ)) :=
  Point.map D.toAffineSpaceOver

/-- The étale coordinate morphism is continuous on complex points. -/
lemma continuous_pointMap :
    @Continuous
      (ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
      (ComplexPoint (Over.mk (ComplexPoint.complexAffineSpace (Fin d) ↘ Spec ↧ℂ)))
      Point.analyticTopology Point.analyticTopology D.pointMap :=
  Point.continuous_map D.toAffineSpaceOver

/-- The ordinary complex-valued coordinate tuple on the analytic neighborhood. -/
def analyticCoordinates :
    ComplexPoint (ComplexPoint.openScheme X D.neighborhood) →
      Fin d → ℂ :=
  ComplexPoint.affineSpaceEquiv (Fin d) ∘ D.pointMap

/-- The ordinary complex-valued étale coordinates are continuous. -/
lemma continuous_analyticCoordinates :
    @Continuous
      (ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
      (Fin d → ℂ) Point.analyticTopology inferInstance
      D.analyticCoordinates :=
  (ComplexPoint.continuous_affineSpaceEquiv (Fin d)).comp
    D.continuous_pointMap

/-- Étale coordinates written on the corresponding open subset of the ambient complex points. -/
def ambientAnalyticCoordinates :
    {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood} →
      Fin d → ℂ :=
  D.analyticCoordinates ∘ (ComplexPoint.openEquiv X D.neighborhood).symm

/-- The étale coordinate tuple is continuous on its ambient analytic open set. -/
lemma continuous_ambientAnalyticCoordinates :
    @Continuous
      {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood}
      (Fin d → ℂ)
      (TopologicalSpace.induced Subtype.val Point.analyticTopology) inferInstance
      D.ambientAnalyticCoordinates := by
  exact D.continuous_analyticCoordinates.comp
    (ComplexPoint.continuous_openEquiv_symm X D.neighborhood)

noncomputable local instance coordinateRingAlgebra :
    Algebra (ComplexAlgHom.complexPolynomialRing d)
      Γ(D.neighborhood.toScheme, ⊤) :=
  D.coordinateRingHomOnOpen.toAlgebra

noncomputable local instance coordinateRingComplexAlgebra :
    Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
  (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra

noncomputable local instance coordinateRingScalarTower :
    IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing d)
      Γ(D.neighborhood.toScheme, ⊤) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

noncomputable local instance coordinateRingEtale :
    Algebra.Etale (ComplexAlgHom.complexPolynomialRing d)
      Γ(D.neighborhood.toScheme, ⊤) :=
  RingHom.etale_algebraMap.mp D.coordinateRingHomOnOpen_etale

/-- The canonical map from an affine neighborhood to the spectrum of its global sections respects
the complex structure morphisms. -/
lemma toSpecΓ_over :
    D.neighborhood.toScheme.toSpecΓ ≫
        ComplexPoint.affineSpecStructureMap Γ(D.neighborhood.toScheme, ⊤) =
      D.neighborhood.ι ≫ X.hom := by
  let φ : ↧ℂ ⟶ Γ(D.neighborhood.toScheme, ⊤) :=
    CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom D.coordinateRingHomOnOpen
  change D.neighborhood.toScheme.toSpecΓ ≫ Spec.map φ = D.neighborhood.ι ≫ X.hom
  change (ΓSpec.adjunction.homEquiv D.neighborhood.toScheme
    (Opposite.op ↧ℂ)) φ.op = D.neighborhood.ι ≫ X.hom
  apply ext_to_Spec
  exact (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ).trans
    D.C_comp_coordinateRingHomOnOpen

/-- The affine neighborhood's complex points are homeomorphic to the complex points of the
spectrum of its global sections. -/
def affineSpecPointHomeomorph :
    @Homeomorph
      (ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
      (ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap Γ(D.neighborhood.toScheme, ⊤))))
      Point.analyticTopology Point.analyticTopology := by
  let : IsAffine D.neighborhood.toScheme := D.isAffine
  let e := asIso D.neighborhood.toScheme.toSpecΓ
  have he : e.hom ≫ ComplexPoint.affineSpecStructureMap Γ(D.neighborhood.toScheme, ⊤) =
      D.neighborhood.ι ≫ X.hom := by
    change D.neighborhood.toScheme.toSpecΓ ≫
      ComplexPoint.affineSpecStructureMap Γ(D.neighborhood.toScheme, ⊤) = _
    exact D.toSpecΓ_over
  exact Point.isoMapHomeomorph (Over.isoMk e he)

lemma affineSpecPointHomeomorph_apply
    (z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) :
    D.affineSpecPointHomeomorph z =
      Point.map (Over.homMk D.neighborhood.toScheme.toSpecΓ D.toSpecΓ_over) z := by
  let : IsAffine D.neighborhood.toScheme :=
    show IsAffine D.neighborhood.toScheme from D.isAffine
  rw [affineSpecPointHomeomorph, Point.isoMapHomeomorph_apply]
  rfl

/-- Complex points of an affine neighborhood as complex-valued algebra homomorphisms on its
coordinate ring. -/
def pointAlgHomHomeomorph :
    @Homeomorph
      (ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
      (Γ(D.neighborhood.toScheme, ⊤) →ₐ[ℂ] ℂ)
      Point.analyticTopology
      (ComplexPoint.affineAlgebraHomTopology Γ(D.neighborhood.toScheme, ⊤)) :=
  D.affineSpecPointHomeomorph.trans
    (ComplexPoint.affineSpecHomeomorph Γ(D.neighborhood.toScheme, ⊤))

/-- Evaluation through the affine algebra-homomorphism model agrees with evaluation of the
corresponding global section on the affine neighborhood. -/
lemma pointAlgHomHomeomorph_apply
    (z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood))
    (r : Γ(D.neighborhood.toScheme, ⊤)) :
    D.pointAlgHomHomeomorph z r = Point.evaluate ⊤ r z := by
  rw [pointAlgHomHomeomorph, Homeomorph.trans_apply]
  change ComplexPoint.affineSpecEquiv Γ(D.neighborhood.toScheme, ⊤)
      (D.affineSpecPointHomeomorph z) r = _
  rw [ComplexPoint.affineSpecEquiv_apply, affineSpecPointHomeomorph_apply, Point.evaluate_map]
  change Point.evaluate ⊤
      (D.neighborhood.toScheme.toSpecΓ.appTop
        ((Scheme.ΓSpecIso ↧Γ(D.neighborhood.toScheme, ⊤)).inv r)) z = _
  rw [Scheme.toSpecΓ_appTop]
  change Point.evaluate ⊤
      ((Scheme.ΓSpecIso ↧Γ(D.neighborhood.toScheme, ⊤)).hom
        ((Scheme.ΓSpecIso ↧Γ(D.neighborhood.toScheme, ⊤)).inv r)) z = _
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso ↧Γ(D.neighborhood.toScheme, ⊤)).inv_hom_id) r
  exact congrArg (fun s ↦ Point.evaluate ⊤ s z) h

/-- The analytic coordinate map reconstructed through the affine ring and its étale polynomial
subalgebra. -/
def algebraicCoordinates :
    ComplexPoint (ComplexPoint.openScheme X D.neighborhood) →
      Fin d → ℂ :=
  ComplexAlgHom.mvPolynomialAlgHomHomeomorph d ∘
    ComplexAlgHom.etaleBaseAlgHom Γ(D.neighborhood.toScheme, ⊤) ∘
      D.pointAlgHomHomeomorph

lemma isLocalHomeomorph_algebraicCoordinates :
    IsLocalHomeomorph D.algebraicCoordinates :=
  (ComplexAlgHom.mvPolynomialAlgHomHomeomorph d).isLocalHomeomorph.comp
    ((ComplexAlgHom.isLocalHomeomorph_etaleBaseAlgHom
      Γ(D.neighborhood.toScheme, ⊤)).comp
        D.pointAlgHomHomeomorph.isLocalHomeomorph)

/-- The reconstructed ring-theoretic coordinates agree with the coordinates induced directly by
the scheme morphism to affine space. -/
lemma algebraicCoordinates_eq_analyticCoordinates :
    D.algebraicCoordinates = D.analyticCoordinates := by
  let g : ComplexAlgHom.complexPolynomialRing d →ₐ[ℂ]
      Γ(D.neighborhood.toScheme, ⊤) :=
    IsScalarTower.toAlgHom ℂ (ComplexAlgHom.complexPolynomialRing d)
      Γ(D.neighborhood.toScheme, ⊤)
  funext z
  calc
    D.algebraicCoordinates z =
        ComplexAlgHom.mvPolynomialAlgHomHomeomorph d
          (ComplexPoint.affineSpecEquiv (ComplexAlgHom.complexPolynomialRing d)
            (ComplexPoint.affineSpecComplexPointMap g (D.affineSpecPointHomeomorph z))) := by
      rw [ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap]
      rfl
    _ = ComplexPoint.affineSpaceEquiv (Fin d)
          (ComplexPoint.polynomialSpecToAffineSpacePointMap (n := d)
            (ComplexPoint.affineSpecComplexPointMap g (D.affineSpecPointHomeomorph z))) :=
      (ComplexPoint.affineSpaceEquiv_polynomialSpecToAffineSpacePointMap _).symm
    _ = D.analyticCoordinates z := by
      unfold analyticCoordinates
      congr 1

/-- Each analytic coordinate is evaluation of the corresponding global regular function on the
affine neighborhood. -/
lemma analyticCoordinates_apply_eq_evaluate
    (z : ComplexPoint (ComplexPoint.openScheme X D.neighborhood)) (i : Fin d) :
    D.analyticCoordinates z i =
      Point.evaluate ⊤ (D.coordinateRingHomOnOpen (MvPolynomial.X i)) z := by
  rw [← D.algebraicCoordinates_eq_analyticCoordinates]
  change D.pointAlgHomHomeomorph z
      (D.coordinateRingHomOnOpen (MvPolynomial.X i)) = _
  exact D.pointAlgHomHomeomorph_apply z _

/-- The ambient open on which a chosen coordinate section is naturally expressed. -/
abbrev ambientCoordinateOpen : X.left.Opens := D.neighborhood.ι ''ᵁ (⊤ : D.neighborhood.toScheme.Opens)

/-- A coordinate function transported from the affine open subscheme to an open of the ambient
scheme. -/
def ambientCoordinateSection (i : Fin d) : Γ(X.left, D.ambientCoordinateOpen) :=
  (D.neighborhood.ι.appIso ⊤).inv
    (D.coordinateRingHomOnOpen (MvPolynomial.X i))

/-- An ambient analytic coordinate is evaluation of its transported regular section. -/
lemma ambientAnalyticCoordinates_apply_eq_evaluate
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood}) (i : Fin d) :
    D.ambientAnalyticCoordinates z i =
      Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) z.1 := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm z
  calc
    D.ambientAnalyticCoordinates z i = D.analyticCoordinates z' i := rfl
    _ = Point.evaluate ⊤
        (D.coordinateRingHomOnOpen (MvPolynomial.X i)) z' :=
      D.analyticCoordinates_apply_eq_evaluate z' i
    _ = Point.evaluate D.ambientCoordinateOpen
        (D.ambientCoordinateSection i) (Point.map (ComplexPoint.openInclusion X D.neighborhood) z') :=
      (ComplexPoint.evaluate_openEquiv X D.neighborhood
        (D.coordinateRingHomOnOpen (MvPolynomial.X i)) z').symm
    _ = Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i) z.1 := by
      congr 2
      exact congrArg Subtype.val
        ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply z)

/-- The analytic coordinates supplied by smoothness are local homeomorphisms to complex affine
space. -/
lemma isLocalHomeomorph_analyticCoordinates :
    IsLocalHomeomorph D.analyticCoordinates := by
  rw [← D.algebraicCoordinates_eq_analyticCoordinates]
  exact D.isLocalHomeomorph_algebraicCoordinates

/-- The same coordinates are a local homeomorphism on the corresponding analytic open subset of
the ambient complex-point space. -/
lemma isLocalHomeomorph_ambientAnalyticCoordinates :
    IsLocalHomeomorph D.ambientAnalyticCoordinates := by
  exact D.isLocalHomeomorph_analyticCoordinates.comp
    (ComplexPoint.openHomeomorph X D.neighborhood).symm.isLocalHomeomorph

/-- The explicit analytic projection chart centered at a point of the ambient coordinate
neighborhood. Unlike a chart chosen only from local-homeomorphism existence, its inverse retains
the standard étale construction and its analyticity theorem. -/
noncomputable def ambientProjectionChart
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood}) :
    OpenPartialHomeomorph
      {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood} (Fin d → ℂ) :=
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm z
  let u := D.pointAlgHomHomeomorph z'
  (ComplexPoint.openHomeomorph X D.neighborhood).symm.toOpenPartialHomeomorph |>.trans
    D.pointAlgHomHomeomorph.toOpenPartialHomeomorph |>.trans
      (ComplexAlgHom.etaleAlgHomProjectionChart (n := d) Γ(D.neighborhood.toScheme, ⊤) u)

lemma mem_ambientProjectionChart_source
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood}) :
    z ∈ (D.ambientProjectionChart z).source := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm z
  let u := D.pointAlgHomHomeomorph z'
  rw [ambientProjectionChart, OpenPartialHomeomorph.trans_source]
  constructor
  · rw [OpenPartialHomeomorph.trans_source]
    simp
  · change u ∈
      (ComplexAlgHom.etaleAlgHomProjectionChart (n := d)
        Γ(D.neighborhood.toScheme, ⊤) u).source
    exact ComplexAlgHom.mem_etaleAlgHomProjectionChart_source
      (n := d) Γ(D.neighborhood.toScheme, ⊤) u

lemma ambientProjectionChart_apply_of_mem
    (z y : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood})
    (hy : y ∈ (D.ambientProjectionChart z).source) :
    D.ambientProjectionChart z y = D.ambientAnalyticCoordinates y := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm z
  let u := D.pointAlgHomHomeomorph z'
  rw [ambientProjectionChart, OpenPartialHomeomorph.trans_source] at hy
  have hu := hy.2
  have hu' : D.pointAlgHomHomeomorph
      ((ComplexPoint.openHomeomorph X D.neighborhood).symm y) ∈
        (ComplexAlgHom.etaleAlgHomProjectionChart (n := d)
          Γ(D.neighborhood.toScheme, ⊤) u).source := by
    simpa only [Set.mem_preimage, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply] using hu
  rw [ambientProjectionChart, OpenPartialHomeomorph.trans_apply,
    OpenPartialHomeomorph.trans_apply]
  change ComplexAlgHom.etaleAlgHomProjectionChart (n := d)
      Γ(D.neighborhood.toScheme, ⊤) u
        (D.pointAlgHomHomeomorph
          ((ComplexPoint.openHomeomorph X D.neighborhood).symm y)) = _
  have hcoord := ComplexAlgHom.etaleAlgHomProjectionChart_apply_of_mem (n := d)
    Γ(D.neighborhood.toScheme, ⊤) u
      (D.pointAlgHomHomeomorph
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm y)) hu'
  rw [hcoord]
  change D.algebraicCoordinates
      ((ComplexPoint.openHomeomorph X D.neighborhood).symm y) =
    D.ambientAnalyticCoordinates y
  rw [D.algebraicCoordinates_eq_analyticCoordinates]
  rfl

/-- Evaluation of a regular function is analytic along the inverse of the explicit ambient
projection chart. -/
lemma analyticAt_ambientProjectionChart_symm_pointAlgHom_apply
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood})
    {w : Fin d → ℂ} (hw : w ∈ (D.ambientProjectionChart z).target)
    (r : Γ(D.neighborhood.toScheme, ⊤)) :
    AnalyticAt ℂ
      (fun v ↦ D.pointAlgHomHomeomorph
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm
          ((D.ambientProjectionChart z).symm v)) r) w := by
  let z' := (ComplexPoint.openHomeomorph X D.neighborhood).symm z
  let u := D.pointAlgHomHomeomorph z'
  have hw' : w ∈
      (ComplexAlgHom.etaleAlgHomProjectionChart (n := d)
        Γ(D.neighborhood.toScheme, ⊤) u).target := by
    rw [ambientProjectionChart, OpenPartialHomeomorph.trans_target] at hw
    exact hw.1
  have h := ComplexAlgHom.analyticAt_etaleAlgHomProjectionChart_symm_apply
    (n := d) Γ(D.neighborhood.toScheme, ⊤) u hw' r
  apply h.congr
  filter_upwards with v
  simp only [ambientProjectionChart, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.symm_symm]
  rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]

/-- Evaluation of a global regular function on the affine neighborhood is analytic along the
inverse of its explicit projection chart. -/
lemma analyticAt_ambientProjectionChart_symm_evaluate_top
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood})
    {w : Fin d → ℂ} (hw : w ∈ (D.ambientProjectionChart z).target)
    (r : Γ(D.neighborhood.toScheme, ⊤)) :
    AnalyticAt ℂ
      (fun v ↦ Point.evaluate ⊤ r
        ((ComplexPoint.openHomeomorph X D.neighborhood).symm
          ((D.ambientProjectionChart z).symm v))) w := by
  simpa only [D.pointAlgHomHomeomorph_apply] using
    D.analyticAt_ambientProjectionChart_symm_pointAlgHom_apply z hw r

/-- Evaluation of any regular function defined near the inverse-chart point is analytic there.
The proof shrinks to a principal open in the affine coordinate neighborhood and writes the
restricted section as a quotient of global sections. -/
lemma analyticAt_ambientProjectionChart_symm_evaluate
    (z : {z : ComplexPoint X // z ∈ Point.overOpen D.neighborhood})
    {w : Fin d → ℂ} (hw : w ∈ (D.ambientProjectionChart z).target)
    (V : X.left.Opens) (s : Γ(X.left, V))
    (hV : ((D.ambientProjectionChart z).symm w).1 ∈ Point.overOpen V) :
    AnalyticAt ℂ
      (fun v ↦ Point.evaluate V s ((D.ambientProjectionChart z).symm v).1) w := by
  let Y := D.neighborhood.toScheme
  let W : Y.Opens := D.neighborhood.ι ⁻¹ᵁ V
  let : IsAffine Y :=
    show IsAffine D.neighborhood.toScheme from D.isAffine
  let y : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) :=
    (ComplexPoint.openHomeomorph X D.neighborhood).symm
      ((D.ambientProjectionChart z).symm w)
  have hymap : Point.map (ComplexPoint.openInclusion X D.neighborhood) y =
      ((D.ambientProjectionChart z).symm w).1 := by
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply
        ((D.ambientProjectionChart z).symm w))
  have hyW : y ∈ Point.overOpen W := by
    apply (Point.mem_overOpen_map_iff (ComplexPoint.openInclusion X D.neighborhood) y V).mp
    rwa [hymap]
  obtain ⟨g, hgW, hyg⟩ :=
    (isAffineOpen_top Y).exists_basicOpen_le
      (V := W) ⟨y.underlying, hyW⟩ trivial
  let sY : Γ(Y, W) := D.neighborhood.ι.app V s
  let t : Γ(Y, Y.basicOpen g) := Y.presheaf.map (homOfLE hgW).op sY
  let : IsAffine (ComplexPoint.openScheme X D.neighborhood).left :=
    inferInstanceAs (IsAffine Y)
  obtain ⟨k, a, hquot⟩ :=
    ComplexPoint.exists_evaluate_affine_basicOpen_eq_div
      (X := ComplexPoint.openScheme X D.neighborhood) g t
  have hyg' : y ∈ Point.overOpen (Y.basicOpen g) := hyg
  have hgzero : Point.evaluate ⊤ g y ≠ 0 :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := ComplexPoint.openScheme X D.neighborhood) (U := ⊤) g y trivial).mp hyg'
  have ha := D.analyticAt_ambientProjectionChart_symm_evaluate_top z hw a
  have hg := D.analyticAt_ambientProjectionChart_symm_evaluate_top z hw g
  have hrat : AnalyticAt ℂ
      (fun v ↦ Point.evaluate ⊤ a
          ((ComplexPoint.openHomeomorph X D.neighborhood).symm
            ((D.ambientProjectionChart z).symm v)) /
        Point.evaluate ⊤ g
          ((ComplexPoint.openHomeomorph X D.neighborhood).symm
            ((D.ambientProjectionChart z).symm v)) ^ k) w :=
    ha.div (hg.pow k) (pow_ne_zero k hgzero)
  apply hrat.congr
  have hcontinuous : ContinuousAt
      (fun v ↦ (ComplexPoint.openHomeomorph X D.neighborhood).symm
        ((D.ambientProjectionChart z).symm v)) w :=
    (ComplexPoint.openHomeomorph X D.neighborhood).symm.continuous.continuousAt.comp
      ((D.ambientProjectionChart z).continuousAt_symm hw)
  have heventually :
      (fun v ↦ (ComplexPoint.openHomeomorph X D.neighborhood).symm
        ((D.ambientProjectionChart z).symm v)) ⁻¹'
          Point.overOpen (Y.basicOpen g) ∈ 𝓝 w :=
    hcontinuous ((Point.isOpen_overOpen (X := ComplexPoint.openScheme X D.neighborhood)
      (Y.basicOpen g)).mem_nhds hyg')
  filter_upwards [heventually] with v hv
  let yv : ComplexPoint (ComplexPoint.openScheme X D.neighborhood) :=
    (ComplexPoint.openHomeomorph X D.neighborhood).symm
      ((D.ambientProjectionChart z).symm v)
  have hymapv : Point.map (ComplexPoint.openInclusion X D.neighborhood) yv =
      ((D.ambientProjectionChart z).symm v).1 := by
    exact congrArg Subtype.val
      ((ComplexPoint.openHomeomorph X D.neighborhood).apply_symm_apply
        ((D.ambientProjectionChart z).symm v))
  have hmap := Point.evaluate_map (ComplexPoint.openInclusion X D.neighborhood) V s yv
  rw [hymapv] at hmap
  have hres := Point.evaluate_res (X := ComplexPoint.openScheme X D.neighborhood)
    (U := W) (V := Y.basicOpen g) hgW sY yv hv
  exact ((hmap.trans hres).trans (hquot yv hv)).symm

end LocalEtaleCoordinates

/-- Étale coordinates of the specified relative dimension chosen around the underlying point of a
complex point. -/
def ComplexPoint.localEtaleCoordinates (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) : LocalEtaleCoordinates X d z.underlying :=
  AlgebraicGeometry.localEtaleCoordinates X d z.underlying

@[simp]
lemma ComplexPoint.mem_localEtaleCoordinates (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    z ∈ Point.overOpen ((ComplexPoint.localEtaleCoordinates X d z).neighborhood) :=
  (ComplexPoint.localEtaleCoordinates X d z).mem

end

end AlgebraicGeometry
