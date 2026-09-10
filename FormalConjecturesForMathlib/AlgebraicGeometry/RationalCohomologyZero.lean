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

public import FormalConjecturesForMathlib.AlgebraicGeometry.HodgeFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

import FormalConjecturesForMathlib.AlgebraicTopology.ConstantSheafDegreeZero

/-!
# Degree-zero rational constant-sheaf cohomology

This file computes degree-zero rational constant-sheaf cohomology as the ordinary morphism
group from the constant integer sheaf to the constant rational sheaf. The computation first
undoes the extension from natural to integer degrees and then uses the theorem
`Abelian.Ext.homEquiv₀` that degree-zero Ext is ordinary Hom.

The explicit comparison sends the constant cohomology class of `q : ℚ` to the sheafification
of the additive map `n ↦ n q`. Thus later arguments about the cohomological unit can be reduced
to honest statements about the constant-sheaf functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The natural-to-integer cochain embedding sends degree zero to degree zero. -/
lemma embeddingUpNat_zero : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl

/-- The extended integer constant-sheaf complex is the integer constant sheaf in degree zero. -/
def constantIntegerSheafComplexIntIsoSingleZero :
    constantIntegerSheafComplexInt X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantIntegerSheaf X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (constantIntegerSheaf X) 0 0 embeddingUpNat_zero

/-- The extended rational constant-sheaf complex is the rational constant sheaf in degree zero. -/
def constantRationalSheafComplexIntIsoSingleZero :
    constantFieldSheafComplexInt ℚ X ≅
      (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantFieldSheaf ℚ X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (constantFieldSheaf ℚ X) 0 0 embeddingUpNat_zero

/-- The inverse of the integer extension/single comparison is a quasi-isomorphism. -/
lemma constantIntegerSheafComplexIntIsoSingleZero_inv_quasiIso :
    analyticQuasiIsomorphisms X
      (constantIntegerSheafComplexIntIsoSingleZero X).inv := by
  let : IsIso (constantIntegerSheafComplexIntIsoSingleZero X).inv :=
    (constantIntegerSheafComplexIntIsoSingleZero X).isIso_inv
  exact ⟨fun _ ↦ inferInstance⟩

/-- The rational extension/single comparison is a quasi-isomorphism. -/
lemma constantRationalSheafComplexIntIsoSingleZero_hom_quasiIso :
    analyticQuasiIsomorphisms X
      (constantRationalSheafComplexIntIsoSingleZero X).hom := by
  let : IsIso (constantRationalSheafComplexIntIsoSingleZero X).hom :=
    (constantRationalSheafComplexIntIsoSingleZero X).isIso_hom
  exact ⟨fun _ ↦ inferInstance⟩

/-- Degree-zero rational cohomology after replacing both extended complexes by single
complexes. -/
def rationalCohomologyZeroEquivSingle :
    FieldCohomology ℚ X 0 ≃
      Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantIntegerSheaf X))
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)) (0 : ℤ) :=
  (Localization.SmallShiftedHom.precompEquiv
      (constantIntegerSheafComplexIntIsoSingleZero X).inv
      (constantIntegerSheafComplexIntIsoSingleZero_inv_quasiIso X)).trans
    (Localization.SmallShiftedHom.postcompEquiv
      (constantRationalSheafComplexIntIsoSingleZero X).hom
      (constantRationalSheafComplexIntIsoSingleZero_hom_quasiIso X))

/-- The single-complex shifted morphism group is definitionally the corresponding Ext group. -/
def rationalCohomologyZeroSingleEquivExt :
    Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantIntegerSheaf X))
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)) (0 : ℤ) ≃
      Abelian.Ext (constantIntegerSheaf X)
        (constantFieldSheaf ℚ X) 0 :=
  Equiv.refl _

/-- The definitional comparison from shifted Hom to Ext acts as the identity. -/
@[simp] lemma rationalCohomologyZeroSingleEquivExt_apply
    (a : Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantIntegerSheaf X))
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (constantFieldSheaf ℚ X)) (0 : ℤ)) :
    rationalCohomologyZeroSingleEquivExt X a = a := rfl

/-- Degree-zero rational constant-sheaf cohomology is ordinary Hom from integer constants to
rational constants. -/
def rationalCohomologyZeroEquivSheafHom :
    FieldCohomology ℚ X 0 ≃
      (constantIntegerSheaf X ⟶ constantFieldSheaf ℚ X) :=
  ((rationalCohomologyZeroEquivSingle X).trans
    (rationalCohomologyZeroSingleEquivExt X)).trans Abelian.Ext.homEquiv₀

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Replacing the extended complexes by single complexes sends a constant class to the
corresponding single-complex morphism. -/
lemma rationalCohomologyZeroEquivSingle_class (q : ℚ) :
    rationalCohomologyZeroEquivSingle X
        (fieldCohomologyClass ℚ X q) =
      Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          (integerToFieldConstantSheaf ℚ X q)) := by
  simp only [rationalCohomologyZeroEquivSingle, fieldCohomologyClass, Equiv.trans_apply,
    Hypercohomology, Localization.SmallShiftedHom.precompEquiv_apply]
  rw [← smallShiftedHomMkZero_comp X, Localization.SmallShiftedHom.postcompEquiv_apply,
    ← smallShiftedHomMkZero_comp X]
  congr 1
  unfold constantIntegerSheafComplexInt constantFieldSheafComplexInt
    integerToFieldConstantSheafComplexInt
    constantIntegerSheafComplexIntIsoSingleZero
    constantRationalSheafComplexIntIsoSingleZero
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f]
    rw [HomologicalComplex.extendSingleIso_inv_f,
      HomologicalComplex.extendMap_f _ _ embeddingUpNat_zero,
      HomologicalComplex.extendSingleIso_hom_f]
    simp
    exact (HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0
      (integerToFieldConstantSheaf ℚ X q)).symm
  · exact (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 (constantIntegerSheaf X) i hi).eq_of_src _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero comparison sends the constant class of `q` to the constant-sheaf morphism
induced by `n ↦ n q`. -/
@[simp] theorem rationalCohomologyZeroEquivSheafHom_class (q : ℚ) :
    rationalCohomologyZeroEquivSheafHom X
        (fieldCohomologyClass ℚ X q) =
      integerToFieldConstantSheaf ℚ X q := by
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  dsimp only [rationalCohomologyZeroEquivSheafHom, Equiv.trans_apply]
  rw [Abelian.Ext.mk₀_homEquiv₀_apply, rationalCohomologyZeroEquivSingle_class,
    rationalCohomologyZeroSingleEquivExt_apply]
  rfl

/-- If the constant-sheaf functor is faithful, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective_of_constantSheaf_faithful
    [(constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).Faithful] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  intro a b hab
  have hs : integerToFieldConstantSheaf ℚ X a =
      integerToFieldConstantSheaf ℚ X b := by
    rw [← rationalCohomologyZeroEquivSheafHom_class,
      ← rationalCohomologyZeroEquivSheafHom_class, hab]
  unfold integerToFieldConstantSheaf at hs
  have hm := (constantSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).map_injective hs
  simpa using ConcreteCategory.congr_hom hm (1 : ℤ)

/-- On a nonempty analytic complex-point space, distinct rational constants define distinct
degree-zero cohomology classes. -/
theorem rationalCohomologyClass_injective
    [Nonempty (ComplexPoint X)] :
    Function.Injective (fieldCohomologyClass ℚ X) := by
  let : (constantSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).Faithful :=
    TopCat.constantSheaf_faithful_of_nonempty _
  exact rationalCohomologyClass_injective_of_constantSheaf_faithful X

/-- On a connected analytic complex-point space, every degree-zero rational cohomology class is
a constant class. -/
theorem rationalCohomologyClass_surjective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Surjective (fieldCohomologyClass ℚ X) := by
  intro α
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  let F := constantSheaf J AddCommGrpCat
  let ff := TopCat.constantSheafFullyFaithfulOfConnected
    (TopCat.of (ComplexPoint X))
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  let e := rationalCohomologyZeroEquivSheafHom X
  obtain ⟨f, hf⟩ := F.map_surjective (e α)
  let q : ℚ := f (1 : ℤ)
  refine ⟨q, e.injective ?_⟩
  rw [rationalCohomologyZeroEquivSheafHom_class, ← hf]
  unfold integerToFieldConstantSheaf
  change F.map (AddCommGrpCat.ofHom (zmultiplesAddHom ℚ q)) = F.map f
  congr 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun n ↦ ?_)
  change n • q = f n
  rw [show n = n • (1 : ℤ) by simp, map_zsmul]
  simp [q]

/-- Constant rational classes give a bijection onto degree-zero cohomology of a connected
analytic complex-point space. -/
theorem rationalCohomologyClass_bijective
    [ConnectedSpace (ComplexPoint X)] :
    Function.Bijective (fieldCohomologyClass ℚ X) := by
  let : Nonempty (ComplexPoint X) := inferInstance
  exact ⟨rationalCohomologyClass_injective X,
    rationalCohomologyClass_surjective X⟩

/-- On a connected analytic complex-point space, rational constants are linearly equivalent to
degree-zero rational cohomology. -/
def rationalCohomologyClassLinearEquiv
    [ConnectedSpace (ComplexPoint X)] :
    ℚ ≃ₗ[ℚ] FieldCohomology ℚ X 0 :=
  LinearEquiv.ofBijective (fieldCohomologyClassLinear ℚ X)
    (rationalCohomologyClass_bijective X)

/-- On a connected analytic complex-point space, the rational cohomology unit spans all of
degree-zero rational cohomology. -/
theorem span_rationalCohomologyUnit_eq_top
    [ConnectedSpace (ComplexPoint X)] :
    Submodule.span ℚ {fieldCohomologyUnit ℚ X} = ⊤ := by
  apply le_antisymm le_top
  intro α _
  obtain ⟨q, rfl⟩ := rationalCohomologyClass_surjective X α
  have hq : fieldCohomologyClass ℚ X q =
      q • fieldCohomologyUnit ℚ X := by
    simpa [fieldCohomologyUnit] using
      fieldCohomologyClass_mul ℚ X q 1
  rw [hq]
  exact Submodule.smul_mem _ q (Submodule.subset_span (Set.mem_singleton _))

/-- The degree-zero rational cohomology unit is nonzero on a nonempty analytic complex-point
space. -/
theorem rationalCohomologyUnit_ne_zero
    [Nonempty (ComplexPoint X)] :
    fieldCohomologyUnit ℚ X ≠ 0 := by
  intro h
  have h10 : fieldCohomologyClass ℚ X 1 =
      fieldCohomologyClass ℚ X 0 := by
    simpa [fieldCohomologyUnit] using h
  exact one_ne_zero (rationalCohomologyClass_injective X h10)

end AlgebraicGeometry.ComplexPoint
