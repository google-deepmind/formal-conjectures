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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.HodgeFiltration
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.ShiftedExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Rational cohomology with support

For a subset `Z` of the analytic complex-point space, this file resolves the rational constant
sheaf on the complement injectively and pushes the resolution to the ambient space. This computes
the derived pushforward from the complement. The homotopy fiber of the canonical restriction to
that derived pushforward is represented by the mapping cone shifted by `-1`. Its hypercohomology
is rational constant-sheaf cohomology with support in `Z`.

The connecting morphism of the mapping-cone triangle gives the canonical map that forgets
support. Thus supported and ordinary rational cohomology use exactly the same derived
constant-sheaf model as the Hodge filtration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance analyticSupportHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The analytic complement of a subset of the complex-point space. -/
abbrev AnalyticComplement (Z : Set (ComplexPoint X)) :=
  Zᶜ

/-- The inclusion of the analytic complement into the complex-point space. -/
def analyticComplementInclusion (Z : Set (ComplexPoint X)) :
    TopCat.of (AnalyticComplement X Z) ⟶
      TopCat.of (ComplexPoint X) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Sheaves of additive groups on the analytic complement. -/
abbrev AnalyticComplementAdditiveSheaf (Z : Set (ComplexPoint X)) :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (AnalyticComplement X Z))

/-- The rational constant sheaf on the analytic complement. -/
def complementConstantRationalSheaf (Z : Set (ComplexPoint X)) :
    AnalyticComplementAdditiveSheaf X Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (AnalyticComplement X Z))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℚ)

/-- The rational constant sheaf on the complement, pushed forward to the ambient space. -/
def pushforwardComplementConstantRationalSheaf
    (Z : Set (ComplexPoint X)) : AnalyticAdditiveSheaf X :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).obj
      (complementConstantRationalSheaf X Z)

/-- Constant rational sections restrict canonically to locally constant sections on the
complement. This is the presheaf morphism before sheafifying the source. -/
def rationalRestrictionPresheaf (Z : Set (ComplexPoint X)) :
    (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj
        (AddCommGrpCat.of ℚ) ⟶
      (pushforwardComplementConstantRationalSheaf X Z).obj :=
  let U := TopCat.of (AnalyticComplement X Z)
  let J := Opens.grothendieckTopology U
  Functor.whiskerLeft (Opens.map (analyticComplementInclusion X Z)).op
    ((sheafificationAdjunction J AddCommGrpCat).unit.app
      ((Functor.const (Opens U)ᵒᵖ).obj (AddCommGrpCat.of ℚ)))

/-- The canonical restriction of the rational constant sheaf to the complement. -/
def rationalRestrictionSheaf (Z : Set (ComplexPoint X)) :
    constantFieldSheaf ℚ X ⟶
      pushforwardComplementConstantRationalSheaf X Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  ⟨sheafifyLift J (rationalRestrictionPresheaf X Z)
    (pushforwardComplementConstantRationalSheaf X Z).property⟩

/-- A fixed injective resolution used to compute the derived pushforward from the complement. -/
def complementConstantRationalInjectiveResolution
    (Z : Set (ComplexPoint X)) :
    InjectiveResolution (complementConstantRationalSheaf X Z) :=
  injectiveResolution (complementConstantRationalSheaf X Z)

/-- A complex representing the derived pushforward of the rational constant sheaf on the
complement. -/
def derivedPushforwardComplementConstantRationalComplexNat
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (complementConstantRationalInjectiveResolution X Z).cocomplex

/-- Every additive sheaf on the empty analytic complement is a zero object. -/
private lemma isZero_sheaf_on_complement_univ
    (F : TopCat.Sheaf AddCommGrpCat.{0}
      (TopCat.of (AnalyticComplement X
        (Set.univ : Set (ComplexPoint X))))) :
    IsZero F :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (C := AddCommGrpCat.{0})
    (X := TopCat.of (AnalyticComplement X
      (Set.univ : Set (ComplexPoint X)))) F).2
    fun x ↦ (show False by simpa [AnalyticComplement] using x.property).elim

/-- Every term of the derived pushforward from the empty complement is zero. -/
private lemma isZero_derivedPushforwardComplement_univ_X (n : ℕ) :
    IsZero ((derivedPushforwardComplementConstantRationalComplexNat X
      (Set.univ : Set (ComplexPoint X))).X n) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X
      (Set.univ : Set (ComplexPoint X)))).map_isZero
        (isZero_sheaf_on_complement_univ X _)

/-- The complex representing derived pushforward from the empty complement is itself a zero
object, not merely acyclic. -/
private lemma isZero_derivedPushforwardComplement_univ :
    IsZero (derivedPushforwardComplementConstantRationalComplexNat X
      (Set.univ : Set (ComplexPoint X))) := by
  constructor
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_src _⟩⟩
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_tgt _⟩⟩

/-- The derived pushforward complex, extended by zero to integer degrees. -/
def derivedPushforwardComplementConstantRationalComplexInt
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (derivedPushforwardComplementConstantRationalComplexNat X Z).extend
    ComplexShape.embeddingUpNat

/-- Extending the zero derived pushforward from the empty complement to integer degrees remains a
zero complex. -/
lemma isZero_derivedPushforwardComplement_univ_int :
    IsZero (derivedPushforwardComplementConstantRationalComplexInt X
      (Set.univ : Set (ComplexPoint X))) :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticAdditiveSheaf X)).map_isZero
      (isZero_derivedPushforwardComplement_univ X)

/-- The pushed-forward resolution map from the underived constant sheaf on the complement. -/
def pushforwardComplementResolutionMap
    (Z : Set (ComplexPoint X)) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀
        (AnalyticComplementAdditiveSheaf X Z)).obj
          (complementConstantRationalSheaf X Z)) ⟶
    derivedPushforwardComplementConstantRationalComplexNat X Z :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (complementConstantRationalInjectiveResolution X Z).ι

/-- Restriction from ambient rational constants to a complex representing the derived
pushforward from the complement. -/
def rationalRestrictionComplexNat
    (Z : Set (ComplexPoint X)) :
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        (constantFieldSheaf ℚ X) ⟶
      derivedPushforwardComplementConstantRationalComplexNat X Z :=
  (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (rationalRestrictionSheaf X Z) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticComplementInclusion X Z)) (ComplexShape.up ℕ) 0).inv.app
          (complementConstantRationalSheaf X Z) ≫
    pushforwardComplementResolutionMap X Z

/-- Restriction from the ambient rational constant complex to the derived pushforward from the
complement. -/
def rationalRestrictionComplexInt (Z : Set (ComplexPoint X)) :
    constantFieldSheafComplexInt ℚ X ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z :=
  HomologicalComplex.extendMap (rationalRestrictionComplexNat X Z)
    ComplexShape.embeddingUpNat

/-- For support equal to the whole space, the third morphism of the restriction mapping-cone
triangle is an isomorphism in the homotopy category. This is the precise categorical form of the
fact that cohomology supported on the whole space is ordinary cohomology. -/
noncomputable instance isIso_mappingConeTriangleh_mor₃_univ :
    IsIso ((CochainComplex.mappingCone.triangleh
      (rationalRestrictionComplexInt X
        (Set.univ : Set (ComplexPoint X)))).mor₃) := by
  let f := rationalRestrictionComplexInt X
    (Set.univ : Set (ComplexPoint X))
  have hdist : CochainComplex.mappingCone.triangleh f ∈
      HomotopyCategory.Pretriangulated.distinguishedTriangles
        (AnalyticAdditiveSheaf X) :=
    ⟨_, _, f, ⟨Iso.refl _⟩⟩
  exact (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _ hdist).1
    ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ)).map_isZero
      (isZero_derivedPushforwardComplement_univ_int X))

/-- The same whole-support connecting morphism is an isomorphism in the derived category used by
hypercohomology. -/
noncomputable instance isIso_derivedMappingConeTriangle_mor₃_univ :
    IsIso ((DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle
        (rationalRestrictionComplexInt X
          (Set.univ : Set (ComplexPoint X))))).mor₃) := by
  let f := rationalRestrictionComplexInt X
    (Set.univ : Set (ComplexPoint X))
  exact (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _
    (DerivedCategory.mappingCone_triangle_distinguished f)).1
    (DerivedCategory.Q.map_isZero (isZero_derivedPushforwardComplement_univ_int X))

/-- The mapping-cone model for the homotopy fiber defining rational cohomology with support. -/
abbrev rationalCohomologyWithSupportComplex
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone (rationalRestrictionComplexInt X Z)

/-- Rational constant-sheaf cohomology with support in `Z`. The degree shift realizes the
homotopy fiber of restriction as the mapping cone shifted by `-1`. -/
abbrev RationalCohomologyWithSupport
    (Z : Set (ComplexPoint X)) (n : ℤ) : Type 1 :=
  Hypercohomology X (rationalCohomologyWithSupportComplex X Z) (n - 1)

/-- The degree-one connecting morphism from the mapping cone to the ambient rational constant
complex. -/
def forgetSupportShiftedHom (Z : Set (ComplexPoint X)) :
    Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
      (rationalCohomologyWithSupportComplex X Z)
      (constantFieldSheafComplexInt ℚ X) (1 : ℤ) :=
  Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
    (CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt X Z)).mor₃

/-- Forget support, using the connecting morphism of the mapping-cone triangle. -/
def forgetSupport (Z : Set (ComplexPoint X)) (n : ℤ) :
    RationalCohomologyWithSupport X Z n →+
      H^n(X; ℚ) where
  toFun α := α.comp (forgetSupportShiftedHom X Z) (by lia)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]
  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

section

/-- After passage to the derived category, the morphism which forgets whole-space support is an
isomorphism. -/
instance isIso_forgetSupportShiftedHom_univ_map :
    IsIso ((Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (forgetSupportShiftedHom X
          (Set.univ : Set (ComplexPoint X)))) := by
  unfold forgetSupportShiftedHom
  erw [Localization.SmallShiftedHom.equiv_mk]
  exact isIso_derivedMappingConeTriangle_mor₃_univ X

end

/-- For support equal to the whole space, forgetting support is a canonical equivalence with
ordinary rational cohomology. Its forward map is definitionally the support-forgetting map. -/
noncomputable def forgetSupportEquivUniv (n : ℤ) :
    RationalCohomologyWithSupport X
        (Set.univ : Set (ComplexPoint X)) n ≃
      H^n(X; ℚ) := by
  let eSource : RationalCohomologyWithSupport X
        (Set.univ : Set (ComplexPoint X)) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Set.univ))
        (n - 1) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let eTarget : H^n(X; ℚ) ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let g := (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q)
      (forgetSupportShiftedHom X
        (Set.univ : Set (ComplexPoint X)))
  let eComp : ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Set.univ))
        (n - 1) ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) n :=
    ShiftedHom.postcompEquivOfIsIso
      (X := DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)) g
      (show (1 : ℤ) + (n - 1) = n by lia)
  have hcomp (α : RationalCohomologyWithSupport X
      (Set.univ : Set (ComplexPoint X)) n) :
      eTarget (forgetSupport X Set.univ n α) = eComp (eSource α) := by
    change eTarget
      (α.comp (forgetSupportShiftedHom X Set.univ) (by lia)) = _
    rw [Localization.SmallShiftedHom.equiv_comp]
    exact (ShiftedHom.postcompEquivOfIsIso_apply g
      (show (1 : ℤ) + (n - 1) = n by lia) (eSource α)).symm
  refine
    { toFun := forgetSupport X Set.univ n
      invFun := fun α => eSource.symm (eComp.symm (eTarget α))
      left_inv := ?_
      right_inv := ?_ }
  · refine fun α ↦ eSource.injective ?_
    rw [eSource.apply_symm_apply, hcomp, eComp.symm_apply_apply]
  · refine fun α ↦ eTarget.injective ?_
    rw [hcomp, eSource.apply_symm_apply, eComp.apply_symm_apply]

end AlgebraicGeometry.ComplexPoint
