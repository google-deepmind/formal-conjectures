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

public import FormalConjecturesForMathlib.Algebra.DeRham.Basic
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAnalyticSheaf
public import FormalConjecturesForMathlib.Analysis.Calculus.DifferentialForm.ExactWedge

/-!
# Analytic differential forms

This file constructs analytic differential forms from holomorphic functions and their actual
manifold derivatives. The pointwise algebra of wedges lives in
`FormalConjecturesForMathlib.Analysis.NormedSpace.WedgeCovectors` and
`FormalConjecturesForMathlib.Analysis.Calculus.DifferentialForm.ExactWedge`.

The starting point is `Algebra.DeRham.Form ℂ 𝒪(U) p`, the Kähler differential forms of the
holomorphic functions on `U`, that is `⋀^p Ω[𝒪(U)⁄ℂ]`. In a fixed chart at `z` such a form is
evaluated pointwise as an alternating continuous multilinear map: taking coordinate derivatives
is a `ℂ`-derivation of `𝒪(U)` into covector fields along the coordinate domain, so the universal
property of `Ω[𝒪(U)⁄ℂ]` and then that of the exterior power turn the pointwise wedge of covectors
into `chartEvaluation`. By construction it takes the algebraic exterior derivative to the
analytic one.

Analytic differential forms are then `Algebra.DeRham.Form ℂ 𝒪(U) p` modulo the forms whose
evaluation vanishes in every chart after every restriction. This enforces analytic identities
such as the chain rule, rather than only the algebraic identities of Kähler differentials.

In degrees above the complex dimension the evaluation target is zero, so the resulting forms
vanish.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialForm TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

noncomputable instance holomorphicFunctionPresheafAlgebra
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    Algebra ℂ ((holomorphicFunctionPresheaf X d).obj U) := by
  change Algebra ℂ
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯
  infer_instance

/-- Restriction of holomorphic functions as an algebra homomorphism over the constants. -/
def holomorphicRestrictionAlgHom [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) :
    ((holomorphicFunctionPresheaf X d).obj U : Type) →ₐ[ℂ]
      ((holomorphicFunctionPresheaf X d).obj V : Type) where
  toRingHom := ((holomorphicFunctionSheaf X d).presheaf.map i).hom
  commutes' _ := rfl

@[simp] lemma holomorphicRestrictionAlgHom_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    holomorphicRestrictionAlgHom X d (𝟙 U) = AlgHom.id ℂ _ := by
  ext f
  rfl

@[simp] lemma holomorphicRestrictionAlgHom_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    holomorphicRestrictionAlgHom X d (i ≫ j) =
      (holomorphicRestrictionAlgHom X d j).comp
        (holomorphicRestrictionAlgHom X d i) := by
  ext f
  rfl

abbrev OpenHolomorphicFunctions [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :=
  ((holomorphicFunctionPresheaf X d).obj U : Type)

/-- The part of a fixed chart target whose inverse image belongs to `U`. -/
def chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    Set (Fin d → ℂ) :=
  (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).target ∩
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm ⁻¹'
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X))

lemma isOpen_chartSectionDomain [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    IsOpen (chartSectionDomain X d U z) := by
  simpa [chartSectionDomain, extChartAt_target, extChartAt_coe_symm] using
    (chartAt (Fin d → ℂ) z).isOpen_inter_preimage_symm
      (Opposite.unop U).isOpen

/-- An arbitrary total extension of a section from its open domain. Its values outside the
domain play no role in derivatives taken within that domain. -/
def extendedSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f : OpenHolomorphicFunctions X d U) :
    ComplexPoint X → ℂ :=
  Function.extend Subtype.val f.1 0

lemma extendedSection_contMDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (f : OpenHolomorphicFunctions X d U) {x : ComplexPoint X}
    (hx : x ∈ (Opposite.unop U : Opens (ComplexPoint X))) :
    ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection X d U f)
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X)) x := by
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff
    (U := (Opposite.unop U : Opens (ComplexPoint X)))
    (x := ⟨x, hx⟩)).mp
  simpa only [extendedSection, Subtype.val_injective.extend_apply] using
    (holomorphicFunctionSheaf_section_analytic X d f).contMDiffAt
      (x := ⟨x, hx⟩)

/-- The expression of a holomorphic section in one fixed chart. -/
def chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) : (Fin d → ℂ) → ℂ :=
  extendedSection X d U f ∘
    (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm

lemma chartSection_contDiffWithinAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    ContDiffWithinAt ℂ ω (chartSection X d U z f)
      (chartSectionDomain X d U z) y := by
  have hsymm : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (chartSectionDomain X d U z) y := by
    exact (contMDiffOn_extChartAt_symm
      (I := modelWithCornersSelf ℂ (Fin d → ℂ)) z y hy.1).mono Set.inter_subset_left
  have hext : ContMDiffWithinAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (extendedSection X d U f)
      ((Opposite.unop U : Opens (ComplexPoint X)) :
        Set (ComplexPoint X))
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y) :=
    extendedSection_contMDiffWithinAt X d U f hy.2
  exact (hext.comp y hsymm (fun _ h ↦ h.2)).contDiffWithinAt

lemma chartSection_contDiffOn [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    ContDiffOn ℂ ω (chartSection X d U z f)
      (chartSectionDomain X d U z) :=
  fun _ hy ↦ chartSection_contDiffWithinAt X d U z f hy

@[simp] lemma chartSection_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z f y =
      f.1 ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y, hy.2⟩ := by
  change Function.extend Subtype.val f.1 0
      (Subtype.val ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y,
        hy.2⟩) = _
  rw [Subtype.val_injective.extend_apply]

/-- The derivative of a section in one fixed chart. -/
def chartSectionDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) (y : Fin d → ℂ) :
    (Fin d → ℂ) →L[ℂ] ℂ :=
  fderivWithin ℂ (chartSection X d U z f)
    (chartSectionDomain X d U z) y

lemma chartSectionDifferential_add [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f g : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (f + g) y =
      chartSectionDifferential X d U z f y +
        chartSectionDifferential X d U z g y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (f + g))
      (chartSection X d U z f + chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.add_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_add ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_smul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (c : ℂ)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (c • f) y =
      c • chartSectionDifferential X d U z f y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (c • f))
      (c • chartSection X d U z f) S := by
    intro w hw
    simp only [Pi.smul_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_const_smul_field c
    ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)

lemma chartSectionDifferential_mul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f g : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z (f * g) y =
      chartSection X d U z f y • chartSectionDifferential X d U z g y +
        chartSection X d U z g y •
          chartSectionDifferential X d U z f y := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn (chartSection X d U z (f * g))
      (chartSection X d U z f * chartSection X d U z g) S := by
    intro w hw
    simp only [Pi.mul_apply, chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact fderivWithin_mul ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
    ((chartSection_contDiffWithinAt X d U z f hy).differentiableWithinAt (by simp))
    ((chartSection_contDiffWithinAt X d U z g hy).differentiableWithinAt (by simp))

lemma chartSectionDifferential_algebraMap [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
      (algebraMap ℂ (OpenHolomorphicFunctions X d U) c) y = 0 := by
  let S := chartSectionDomain X d U z
  have hEq : Set.EqOn
      (chartSection X d U z
        (algebraMap ℂ (OpenHolomorphicFunctions X d U) c))
      (fun _ ↦ c) S := by
    intro w hw
    simp only [chartSection_apply_of_mem X d U z _ hw]
    rfl
  rw [chartSectionDifferential, fderivWithin_congr' hEq hy]
  exact congrFun
    (fderivWithin_const (𝕜 := ℂ) (E := Fin d → ℂ) (s := S) c) y

/-! ### Reading holomorphic functions in a fixed chart -/

/-- Expressing holomorphic functions on `U` in a fixed chart, as a homomorphism of `ℂ`-algebras
into functions on the coordinate domain of that chart. -/
def chartSectionAlgHom [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    OpenHolomorphicFunctions X d U →ₐ[ℂ] (↥(chartSectionDomain X d U z) → ℂ) where
  toFun f y := chartSection X d U z f y.1
  map_one' := by funext y; simp only [chartSection_apply_of_mem X d U z _ y.2]; rfl
  map_mul' f g := by
    funext y
    simp only [Pi.mul_apply, chartSection_apply_of_mem X d U z _ y.2]
    rfl
  map_zero' := by funext y; simp only [chartSection_apply_of_mem X d U z _ y.2]; rfl
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, chartSection_apply_of_mem X d U z _ y.2]
    rfl
  commutes' c := by funext y; simp only [chartSection_apply_of_mem X d U z _ y.2]; rfl

@[simp] lemma chartSectionAlgHom_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) (y : ↥(chartSectionDomain X d U z)) :
    chartSectionAlgHom X d U z f y = chartSection X d U z f y.1 := rfl

/-- Functions on the coordinate domain of a fixed chart form a module over the holomorphic
functions on `U`, acting through their expression in that chart. -/
abbrev chartFieldModule [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    Module (OpenHolomorphicFunctions X d U) (↥(chartSectionDomain X d U z) → V) :=
  Module.compHom _ (chartSectionAlgHom X d U z).toRingHom

attribute [local instance] chartFieldModule

lemma chartFieldModule_smul_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V]
    (f : OpenHolomorphicFunctions X d U) (F : ↥(chartSectionDomain X d U z) → V)
    (y : ↥(chartSectionDomain X d U z)) :
    (f • F) y = chartSection X d U z f y.1 • F y := rfl

/-- The scalar actions of `ℂ` and of the holomorphic functions on chart fields are compatible. -/
theorem chartFieldTower [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    IsScalarTower ℂ (OpenHolomorphicFunctions X d U)
      (↥(chartSectionDomain X d U z) → V) := by
  refine ⟨fun c f F => ?_⟩
  funext y
  have h : chartSection X d U z (c • f) y.1 = c * chartSection X d U z f y.1 := by
    simp only [chartSection_apply_of_mem X d U z _ y.2]; rfl
  rw [chartFieldModule_smul_apply, Pi.smul_apply, chartFieldModule_smul_apply, h, mul_smul]

attribute [local instance] chartFieldTower

/-- The coordinate differentials of holomorphic sections form a `ℂ`-derivation into covector
fields along the coordinate domain of a fixed chart. -/
def chartDerivation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) :
    Derivation ℂ (OpenHolomorphicFunctions X d U)
      (↥(chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ)) where
  toFun f y := chartSectionDifferential X d U z f y.1
  map_add' f g := by
    funext y
    exact chartSectionDifferential_add X d U z f g y.2
  map_smul' c f := by
    funext y
    exact chartSectionDifferential_smul X d U z c f y.2
  map_one_eq_zero' := by
    funext y
    show chartSectionDifferential X d U z 1 y.1 = 0
    rw [show (1 : OpenHolomorphicFunctions X d U) =
      algebraMap ℂ (OpenHolomorphicFunctions X d U) 1 by simp]
    exact chartSectionDifferential_algebraMap X d U z 1 y.2
  leibniz' f g := by
    funext y
    exact chartSectionDifferential_mul X d U z f g y.2

@[simp] lemma chartDerivation_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) (y : ↥(chartSectionDomain X d U z)) :
    chartDerivation X d U z f y = chartSectionDifferential X d U z f y.1 := rfl

private lemma update_eval {p : ℕ} {V W : Type*} (L : Fin p → V → W) (i : Fin p)
    (a : V → W) (y : V) :
    (fun j => Function.update L i a j y) = Function.update (fun j => L j y) i (a y) := by
  funext j
  by_cases h : j = i <;> simp [h]

/-- The pointwise wedge of covector fields along a fixed chart. -/
def chartWedge [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ) :
    (↥(chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ))
      [⋀^Fin p]→ₗ[OpenHolomorphicFunctions X d U]
      (↥(chartSectionDomain X d U z) → ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)) where
  toFun L y := ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p fun i => L i y
  map_update_add' := by
    intro instDec L i a b
    obtain rfl : instDec = instDecidableEqFin p := Subsingleton.elim _ _
    funext y
    show ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p (fun j => Function.update L i (a + b) j y) =
      ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p (fun j => Function.update L i a j y) +
        ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p (fun j => Function.update L i b j y)
    rw [update_eval, update_eval, update_eval, Pi.add_apply, ContinuousAlternatingMap.wedgeCovectors_update_add]
  map_update_smul' := by
    intro instDec L i f a
    obtain rfl : instDec = instDecidableEqFin p := Subsingleton.elim _ _
    funext y
    show ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p (fun j => Function.update L i (f • a) j y) =
      chartSection X d U z f y.1 •
        ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p (fun j => Function.update L i a j y)
    rw [update_eval, update_eval, chartFieldModule_smul_apply,
      ContinuousAlternatingMap.wedgeCovectors_update_smul]
  map_eq_zero_of_eq' L i j h hij := by
    funext y
    exact ContinuousAlternatingMap.wedgeCovectors_eq_zero_of_eq (Fin d → ℂ) p _ i j (congrFun h y) hij

@[simp] lemma chartWedge_apply [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (L : Fin p → ↥(chartSectionDomain X d U z) → ((Fin d → ℂ) →L[ℂ] ℂ))
    (y : ↥(chartSectionDomain X d U z)) :
    chartWedge X d U z p L y = ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p fun i => L i y := rfl

/-- Fixed-chart evaluation of differential forms, as a `ℂ`-linear map into alternating-form
fields on the coordinate domain. -/
def chartEvaluationHolo [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p →ₗ[OpenHolomorphicFunctions X d U]
      (↥(chartSectionDomain X d U z) → ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((chartWedge X d U z p).compLinearMap
      (chartDerivation X d U z).liftKaehlerDifferential)

lemma chartEvaluationHolo_mk [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U)
    (y : ↥(chartSectionDomain X d U z)) :
    chartEvaluationHolo X d U z p
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p a₀ v) y =
      chartSection X d U z a₀ y.1 •
        ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p
          fun i => chartSectionDifferential X d U z (v i) y.1 := by
  show chartEvaluationHolo X d U z p
    (a₀ • Algebra.DeRham.exact ℂ (OpenHolomorphicFunctions X d U) p v) y = _
  rw [map_smul, chartFieldModule_smul_apply, chartEvaluationHolo, Algebra.DeRham.exact,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp

/-- Extend a function on the coordinate domain of a fixed chart by zero. -/
def extendByZero [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    {V : Type} [Zero V] (F : ↥(chartSectionDomain X d U z) → V) : (Fin d → ℂ) → V :=
  Function.extend Subtype.val F 0

@[simp] lemma extendByZero_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    {V : Type} [Zero V] (F : ↥(chartSectionDomain X d U z) → V)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    extendByZero X d U z F y = F ⟨y, hy⟩ :=
  Subtype.val_injective.extend_apply F 0 ⟨y, hy⟩

lemma extendByZero_apply_of_notMem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    {V : Type} [Zero V] (F : ↥(chartSectionDomain X d U z) → V)
    {y : Fin d → ℂ} (hy : y ∉ chartSectionDomain X d U z) :
    extendByZero X d U z F y = 0 := by
  rw [extendByZero, Function.extend_apply' _ _ _ ?_]
  · rfl
  · rintro ⟨⟨w, hw⟩, rfl⟩
    exact hy hw

/-- Extension by zero, as a `ℂ`-linear map on chart fields. -/
def extendByZeroLinear [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X)
    (V : Type) [AddCommGroup V] [Module ℂ V] :
    (↥(chartSectionDomain X d U z) → V) →ₗ[ℂ] ((Fin d → ℂ) → V) where
  toFun := extendByZero X d U z
  map_add' F G := by
    funext y
    by_cases hy : y ∈ chartSectionDomain X d U z
    · simp [extendByZero_apply_of_mem X d U z _ hy]
    · simp [extendByZero_apply_of_notMem X d U z _ hy]
  map_smul' c F := by
    funext y
    by_cases hy : y ∈ chartSectionDomain X d U z
    · simp [extendByZero_apply_of_mem X d U z _ hy]
    · simp [extendByZero_apply_of_notMem X d U z _ hy]

/-- Fixed-chart evaluation of a differential form, as a `ℂ`-linear map into alternating-form
fields on the chart target, extended by zero outside the coordinate domain. -/
def chartEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      ((Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :=
  (extendByZeroLinear X d U z _).comp
    ((chartEvaluationHolo X d U z p).restrictScalars ℂ)

lemma chartEvaluation_apply_of_mem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartEvaluation X d U z p θ y = chartEvaluationHolo X d U z p θ ⟨y, hy⟩ :=
  extendByZero_apply_of_mem X d U z _ hy

lemma chartEvaluation_apply_of_notMem [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∉ chartSectionDomain X d U z) :
    chartEvaluation X d U z p θ y = 0 :=
  extendByZero_apply_of_notMem X d U z _ hy

@[simp] lemma chartEvaluation_zero [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ) :
    chartEvaluation X d U z p 0 = 0 :=
  map_zero (chartEvaluation X d U z p)

@[simp] lemma chartEvaluation_add [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a b : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    chartEvaluation X d U z p (a + b) =
      chartEvaluation X d U z p a + chartEvaluation X d U z p b :=
  map_add (chartEvaluation X d U z p) a b

@[simp] lemma chartEvaluation_smul [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ) (c : ℂ)
    (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    chartEvaluation X d U z p (c • a) = c • chartEvaluation X d U z p a :=
  map_smul (chartEvaluation X d U z p) c a

@[simp] lemma chartEvaluation_neg [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    chartEvaluation X d U z p (-a) = -chartEvaluation X d U z p a :=
  map_neg (chartEvaluation X d U z p) a

@[simp] lemma chartEvaluation_sub [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a b : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    chartEvaluation X d U z p (a - b) =
      chartEvaluation X d U z p a - chartEvaluation X d U z p b :=
  map_sub (chartEvaluation X d U z p) a b

/-- Fixed-chart evaluation of the generator `a₀ * d v₀ ∧ ⋯ ∧ d vₚ₋₁`. -/
def chartGeneratorEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U) :
    (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  fun y => chartSection X d U z a₀ y •
    ContinuousAlternatingMap.wedgeCovectors (Fin d → ℂ) p fun i => chartSectionDifferential X d U z (v i) y

lemma chartEvaluation_mk [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartEvaluation X d U z p
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p a₀ v) y =
      chartGeneratorEvaluation X d U z p a₀ v y := by
  rw [chartEvaluation_apply_of_mem X d U z p _ hy, chartEvaluationHolo_mk]
  rfl

lemma chartEvaluation_mk_eqOn [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U) :
    Set.EqOn (chartEvaluation X d U z p
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p a₀ v))
      (chartGeneratorEvaluation X d U z p a₀ v) (chartSectionDomain X d U z) :=
  fun _ hy => chartEvaluation_mk X d U z p a₀ v hy

/-- Exterior differentiation of `a₀ * d v₀ ∧ ⋯ ∧ d vₚ₋₁` inserts the coefficient as the first
differential. -/
lemma extDerivWithin_chartGeneratorEvaluation
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    extDerivWithin (chartGeneratorEvaluation X d U z p a₀ v)
        (chartSectionDomain X d U z) y =
      chartGeneratorEvaluation X d U z (p + 1) 1 (Fin.cons a₀ v) y := by
  have h := extDerivWithin_smul_exactWedgeWithin (Fin d → ℂ) p
    (chartSection X d U z a₀)
    (fun i ↦ chartSection X d U z (v i))
    (chartSectionDomain X d U z) y
    (isOpen_chartSectionDomain X d U z) hy
    (chartSection_contDiffOn X d U z a₀)
    (fun i ↦ chartSection_contDiffOn X d U z (v i))
  rw [show chartGeneratorEvaluation X d U z p a₀ v =
      (fun w ↦ chartSection X d U z a₀ w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection X d U z (v i))
          (chartSectionDomain X d U z) w) from rfl]
  rw [h]
  simp only [chartGeneratorEvaluation, chartSectionDifferential]
  rw [show chartSection X d U z (1 : OpenHolomorphicFunctions X d U) y = 1 by
        simp only [chartSection_apply_of_mem X d U z _ hy]
        rfl, one_smul]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

lemma chartGeneratorEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (chartGeneratorEvaluation X d U z p a₀ v)
      (chartSectionDomain X d U z) y := by
  rw [show chartGeneratorEvaluation X d U z p a₀ v =
      (fun w ↦ chartSection X d U z a₀ w •
        exactWedgeWithin (Fin d → ℂ) p
          (fun i ↦ chartSection X d U z (v i))
          (chartSectionDomain X d U z) w) from rfl]
  exact DifferentiableWithinAt.smul
    ((chartSection_contDiffWithinAt X d U z a₀ hy).differentiableWithinAt (by simp))
    (exactWedgeWithin_differentiableWithinAt (Fin d → ℂ) p
      (fun i ↦ chartSection X d U z (v i))
      (chartSectionDomain X d U z) y
      (isOpen_chartSectionDomain X d U z) hy
      (fun i ↦ chartSection_contDiffOn X d U z (v i)))

lemma chartEvaluation_differentiableWithinAt
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    DifferentiableWithinAt ℂ (chartEvaluation X d U z p θ)
      (chartSectionDomain X d U z) y := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      exact ((chartGeneratorEvaluation_differentiableWithinAt X d U z p a₀ v hy).congr
        (fun w hw => chartEvaluation_mk X d U z p a₀ v hw)
        (chartEvaluation_mk X d U z p a₀ v hy))
  | zero =>
      rw [chartEvaluation_zero]
      exact differentiableWithinAt_const (c := (0 : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ))
  | add a b ha hb => rw [chartEvaluation_add]; exact ha.add hb
  | smul c a ha => rw [chartEvaluation_smul]; exact ha.const_smul c

lemma extDerivWithin_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : ℕ}
    (s : Set E) (x : E) :
    extDerivWithin (0 : E → E [⋀^Fin p]→L[ℂ] ℂ) s x = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply, fderivWithin_zero]

/-- Fixed-chart evaluation intertwines the algebraic and the analytic exterior derivative. -/
lemma chartEvaluation_differential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartEvaluation X d U z (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ) y =
      extDerivWithin (chartEvaluation X d U z p θ)
        (chartSectionDomain X d U z) y := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      rw [Algebra.DeRham.differential_mk, chartEvaluation_mk X d U z (p + 1) _ _ hy,
        extDerivWithin_congr' (chartEvaluation_mk_eqOn X d U z p a₀ v) hy,
        extDerivWithin_chartGeneratorEvaluation X d U z p a₀ v hy]
  | zero => simp [extDerivWithin_zero]
  | add a b ha hb =>
      rw [map_add, chartEvaluation_add, chartEvaluation_add, Pi.add_apply, ha, hb,
        extDerivWithin_add ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)
          (chartEvaluation_differentiableWithinAt X d U z p a hy)
          (chartEvaluation_differentiableWithinAt X d U z p b hy)]
  | smul c a ha =>
      rw [map_smul, chartEvaluation_smul, chartEvaluation_smul, Pi.smul_apply, ha,
        extDerivWithin_smul c _
          ((isOpen_chartSectionDomain X d U z).uniqueDiffWithinAt hy)]

/-- Evaluation at one point of one fixed coordinate chart. -/
def chartEvaluationAt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ) (y : Fin d → ℂ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ :=
  (LinearMap.proj y).comp (chartEvaluation X d U z p)

/-- Differential forms that vanish in every fixed chart at every point of its coordinate
domain. -/
def chartEvaluationKernel [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :=
  ⨅ (z : ComplexPoint X), ⨅ (y : Fin d → ℂ),
    ⨅ (_ : y ∈ chartSectionDomain X d U z),
      LinearMap.ker (chartEvaluationAt X d U z p y)

lemma mem_chartEvaluationKernel_iff [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    θ ∈ chartEvaluationKernel X d U p ↔
      ∀ z y, y ∈ chartSectionDomain X d U z →
        chartEvaluation X d U z p θ y = 0 := by
  simp only [chartEvaluationKernel, Submodule.mem_iInf, LinearMap.mem_ker,
    chartEvaluationAt]
  rfl

/-- Coordinate-zero identities remain coordinate-zero after exterior differentiation. -/
lemma differential_mem_chartEvaluationKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ chartEvaluationKernel X d U p) :
    Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ ∈
      chartEvaluationKernel X d U (p + 1) := by
  have hθ' := (mem_chartEvaluationKernel_iff X d U p θ).1 hθ
  refine (mem_chartEvaluationKernel_iff X d U (p + 1) _).2 fun z y hy ↦ ?_
  have hEq : Set.EqOn (chartEvaluation X d U z p θ) 0
      (chartSectionDomain X d U z) := fun w hw ↦ hθ' z w hw
  rw [chartEvaluation_differential X d U z p θ hy, extDerivWithin_congr' hEq hy,
    extDerivWithin_zero]

lemma chartEvaluationKernel_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : chartEvaluationKernel X d U p = ⊤ := by
  refine top_unique fun θ _ ↦ ?_
  refine (mem_chartEvaluationKernel_iff X d U p θ).2 fun z y hy ↦
    ContinuousAlternatingMap.ext fun v ↦ ?_
  refine (chartEvaluation X d U z p θ y).toAlternatingMap.map_linearDependent _ fun hli ↦ ?_
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcard
  lia

/-- Restriction of differential forms along an inclusion of open sets. -/
def formRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p →ₗ[ℂ]
      Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d V) p :=
  Algebra.DeRham.map ℂ (holomorphicRestrictionAlgHom X d i) p

@[simp] lemma formRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    formRestriction X d (𝟙 U) p = LinearMap.id := by
  rw [formRestriction, holomorphicRestrictionAlgHom_id, Algebra.DeRham.map_id]

@[simp] lemma formRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    formRestriction X d (i ≫ j) p =
      (formRestriction X d j p).comp (formRestriction X d i p) := by
  rw [formRestriction, formRestriction, formRestriction,
    holomorphicRestrictionAlgHom_comp, Algebra.DeRham.map_comp]

@[simp] lemma formRestriction_mk [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (v : Fin p → OpenHolomorphicFunctions X d U) :
    formRestriction X d i p (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p a₀ v) =
      Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d V) p
        (holomorphicRestrictionAlgHom X d i a₀)
        fun k => holomorphicRestrictionAlgHom X d i (v k) :=
  Algebra.DeRham.map_mk ℂ (holomorphicRestrictionAlgHom X d i) p a₀ v

lemma formRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    formRestriction X d i (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ) =
      Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d V) p
        (formRestriction X d i p θ) :=
  Algebra.DeRham.map_differential ℂ (holomorphicRestrictionAlgHom X d i) p θ

/-- Forms whose fixed-chart evaluations vanish after every restriction. -/
def restrictionStableAnalyticKernel [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :=
  ⨅ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ),
    ⨅ (i : U ⟶ V),
      (chartEvaluationKernel X d V p).comap (formRestriction X d i p)

lemma formRestriction_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ restrictionStableAnalyticKernel X d U p) :
    formRestriction X d i p θ ∈ restrictionStableAnalyticKernel X d V p := by
  rw [restrictionStableAnalyticKernel] at hθ ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hθ ⊢
  intro W j
  specialize hθ W (i ≫ j)
  rwa [formRestriction_comp, LinearMap.comp_apply] at hθ

/-- Restriction-stable coordinate identities remain so after exterior differentiation. -/
lemma differential_mem_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ restrictionStableAnalyticKernel X d U p) :
    Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ ∈
      restrictionStableAnalyticKernel X d U (p + 1) := by
  rw [restrictionStableAnalyticKernel] at hθ ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hθ ⊢
  intro V i
  specialize hθ V i
  rw [formRestriction_differential]
  exact differential_mem_chartEvaluationKernel X d V p hθ

/-- Relations for analytic de Rham forms: exactly the restriction-stable identities detected by
actual complex derivatives. -/
def holomorphicFormRelations [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    Submodule ℂ (Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :=
  restrictionStableAnalyticKernel X d U p

lemma holomorphicFormRelations_eq_restrictionStableAnalyticKernel
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRelations X d U p = restrictionStableAnalyticKernel X d U p := rfl

lemma holomorphicFormRelations_eq_top_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) : holomorphicFormRelations X d U p = ⊤ := by
  refine top_unique fun θ _ ↦ ?_
  rw [holomorphicFormRelations, restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  rw [chartEvaluationKernel_eq_top_of_lt X d V hp]
  trivial

lemma differential_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    {θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ holomorphicFormRelations X d U p) :
    Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ ∈
      holomorphicFormRelations X d U (p + 1) :=
  differential_mem_restrictionStableAnalyticKernel X d U p hθ

lemma formRestriction_mem_holomorphicFormRelations
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p}
    (hθ : θ ∈ holomorphicFormRelations X d U p) :
    formRestriction X d i p θ ∈ holomorphicFormRelations X d V p :=
  formRestriction_mem_restrictionStableAnalyticKernel X d i p hθ

/-- Analytic differential forms of degree `p` on `U`: Kähler differential forms of the
holomorphic functions, modulo the identities that actual complex derivatives detect after every
restriction. -/
abbrev HolomorphicForm [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :=
  Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p ⧸
    holomorphicFormRelations X d U p

lemma holomorphicForm_eq_zero_of_lt [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    {p : ℕ} (hp : d < p) (θ : HolomorphicForm X d U p) : θ = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk θ = 0
  rw [Submodule.Quotient.mk_eq_zero, holomorphicFormRelations_eq_top_of_lt X d U hp]
  trivial

/-- A complex constant regarded as an analytic differential zero-form. -/
def holomorphicFormOfConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) :
    ℂ →ₗ[ℂ] HolomorphicForm X d U 0 :=
  (holomorphicFormRelations X d U 0).mkQ.comp
    (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U))

def holomorphicFormDifferential [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d U (p + 1) :=
  (holomorphicFormRelations X d U p).liftQ
    ((holomorphicFormRelations X d U (p + 1)).mkQ.comp
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p)) (by
        intro θ hθ
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact differential_mem_holomorphicFormRelations X d U p hθ)

def holomorphicFormRestriction [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ) :
    HolomorphicForm X d U p →ₗ[ℂ] HolomorphicForm X d V p :=
  (holomorphicFormRelations X d U p).liftQ
    ((holomorphicFormRelations X d V p).mkQ.comp (formRestriction X d i p)) (by
      intro θ hθ
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact formRestriction_mem_holomorphicFormRelations X d i p hθ)

@[simp] lemma holomorphicFormRestriction_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (c : ℂ) :
    holomorphicFormRestriction X d i 0
        (holomorphicFormOfConstant X d U c) =
      holomorphicFormOfConstant X d V c := by
  change Submodule.Quotient.mk
      (formRestriction X d i 0 (Algebra.DeRham.ofConstant ℂ _ c)) = _
  rw [formRestriction, Algebra.DeRham.map_ofConstant]
  rfl

@[simp] lemma holomorphicFormDifferential_ofConstant
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (c : ℂ) :
    holomorphicFormDifferential X d U 0
        (holomorphicFormOfConstant X d U c) = 0 := by
  change Submodule.Quotient.mk
      (Algebra.DeRham.differential ℂ _ 0 (Algebra.DeRham.ofConstant ℂ _ c)) = 0
  rw [Algebra.DeRham.differential_ofConstant]
  exact Submodule.Quotient.mk_zero _

lemma holomorphicFormDifferential_squared [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ)
    (θ : HolomorphicForm X d U p) :
    holomorphicFormDifferential X d U (p + 1)
      (holomorphicFormDifferential X d U p θ) = 0 := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk
    (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) (p + 1)
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ)) = 0
  rw [Algebra.DeRham.differential_squared]
  exact Submodule.Quotient.mk_zero _

lemma holomorphicFormRestriction_differential [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (θ : HolomorphicForm X d U p) :
    holomorphicFormRestriction X d i (p + 1)
        (holomorphicFormDifferential X d U p θ) =
      holomorphicFormDifferential X d V p
        (holomorphicFormRestriction X d i p θ) := by
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk
      (formRestriction X d i (p + 1)
        (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d U) p θ)) =
    Submodule.Quotient.mk
      (Algebra.DeRham.differential ℂ (OpenHolomorphicFunctions X d V) p
        (formRestriction X d i p θ))
  rw [formRestriction_differential]

@[simp] lemma holomorphicFormRestriction_id [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (p : ℕ) :
    holomorphicFormRestriction X d (𝟙 U) p = LinearMap.id := by
  apply LinearMap.ext
  intro θ
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk (formRestriction X d (𝟙 U) p θ) = _
  rw [formRestriction_id]
  rfl

@[simp] lemma holomorphicFormRestriction_comp [SmoothOfRelativeDimension d X.hom]
    {U V W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (p : ℕ) :
    holomorphicFormRestriction X d (i ≫ j) p =
      (holomorphicFormRestriction X d j p).comp
        (holomorphicFormRestriction X d i p) := by
  apply LinearMap.ext
  intro θ
  obtain ⟨θ, rfl⟩ := Submodule.mkQ_surjective (holomorphicFormRelations X d U p) θ
  change Submodule.Quotient.mk (formRestriction X d (i ≫ j) p θ) = _
  rw [formRestriction_comp]
  rfl

end AlgebraicGeometry.ComplexPoint
