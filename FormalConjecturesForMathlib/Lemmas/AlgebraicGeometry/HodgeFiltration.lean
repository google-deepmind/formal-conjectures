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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# The Hodge filtration

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HodgeFiltration`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))

attribute [local instance] hodgeFiltrationTopology

attribute [local instance] analyticHasDerivedCategory

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf :
    fieldToComplexConstantSheaf K X ≫
      complexToFieldConstantSheaf K X = 𝟙 _ := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom =
      𝟙 (AddCommGrpCat.of K) := by
    ext q
    exact complexToFieldLinear_algebraMap K q
  rw [h]
  exact (constantSheaf J AddCommGrpCat).map_id (AddCommGrpCat.of K)

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexToField :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexToFieldConstantSheafComplexInt K X = 𝟙 _ := by
  unfold fieldToComplexConstantSheafComplexInt
    complexToFieldConstantSheafComplexInt constantFieldSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf]
  have hmap : (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (𝟙 (constantFieldSheaf K X)) =
      𝟙 ((CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        (constantFieldSheaf K X)) :=
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map_id _
  rw [hmap]
  exact HomologicalComplex.extendMap_id _ _

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarSheaf_zero : fieldScalarSheaf K X 0 = 0 := by
  unfold fieldScalarSheaf
  rw [fieldScalarAddHom_zero]
  have h : AddCommGrpCat.ofHom (0 : K →+ K) = 0 := AddCommGrpCat.hom_ext rfl
  rw [h, Functor.map_zero]
  rfl

omit [Algebra K ℂ] in
@[simp] lemma fieldScalarComplex_zero : fieldScalarComplex K X 0 = 0 := by
  unfold fieldScalarComplex
  rw [fieldScalarSheaf_zero, Functor.map_zero, HomologicalComplex.extendMap_zero]

/-- Postcomposition by the zero map of complexes is the zero map on hypercohomology. -/
@[simp] lemma hypercohomologyMap_zero
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (0 : K ⟶ L) n = 0 := by
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [AddMonoidHom.zero_apply]
  apply (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  unfold hypercohomologyMap
  simp [Localization.SmallShiftedHom.equiv_comp,
    hypercohomologyEquiv_zero]

/-- Postcomposition by the identity map of complexes is the identity on hypercohomology. -/
@[simp] lemma hypercohomologyMap_id
    {K : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (n : ℤ) :
    hypercohomologyMap X (𝟙 K) n = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun α ↦ ?_
  let eK : Hypercohomology X K n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  change α.comp
      (Localization.SmallShiftedHom.mk₀
        (analyticQuasiIsomorphisms X) 0 rfl (𝟙 K))
      (zero_add n) = α
  apply eK.injective
  rw [Localization.SmallShiftedHom.equiv_comp]
  simp [eK]

lemma complexConstantCohomologyDeRhamEquiv_apply
    [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X)) (n : ℤ)
    (α : ComplexConstantCohomology X n) :
    complexConstantCohomologyDeRhamEquiv X h n α =
      hypercohomologyMap X
        (constantsToHolomorphicDeRhamComplexInt X) n α :=
  rfl

/-- The rational-to-complex cohomology map has the displayed cohomological left inverse. -/
lemma complexToFieldCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToFieldCohomology K X n)
      (fieldToComplexCohomology K X n) := by
  intro α
  unfold complexToFieldCohomology fieldToComplexCohomology
  rw [← hypercohomologyMap_comp_apply X,
    fieldToComplexConstantSheafComplexInt_comp_complexToField,
    hypercohomologyMap_id]
  rfl

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma fieldToComplexCohomology_injective (n : ℤ) :
    Function.Injective (fieldToComplexCohomology K X n) :=
  (complexToFieldCohomology_leftInverse K X n).injective

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma fieldToDeRhamCohomology_factor
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n α =
      hypercohomologyMap X
        (constantsToHolomorphicDeRhamComplexInt X) n
        (fieldToComplexCohomology K X n α) := by
  unfold fieldToDeRhamCohomology fieldToComplexCohomology
    fieldToHolomorphicDeRhamComplexInt
  exact hypercohomologyMap_comp_apply X
    (fieldToComplexConstantSheafComplexInt K X)
    (constantsToHolomorphicDeRhamComplexInt X) n α

/-- Once the analytic Poincare comparison is proved to be a quasi-isomorphism, the
rational-to-de Rham comparison is injective. This uses the explicit splitting of `K → ℂ`, not a
finite-dimensionality assumption. -/
lemma fieldToDeRhamCohomology_injective_of_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X)) (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) := by
  intro α β hαβ
  apply fieldToComplexCohomology_injective K X n
  apply (complexConstantCohomologyDeRhamEquiv X h n).injective
  simpa only [complexConstantCohomologyDeRhamEquiv_apply,
    fieldToDeRhamCohomology_factor K X n] using hαβ

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit coefficient splitting proves that extending
scalars from `K` to `ℂ` is injective. -/
lemma fieldToDeRhamCohomology_injective
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) :=
  fieldToDeRhamCohomology_injective_of_quasiIso K X inferInstance n

@[simp] lemma fieldToDeRhamComplexification_tmul
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (c : ℂ) (α : H^n(X; K)) :
    fieldToDeRhamComplexification K X n (c ⊗ₜ[K] α) =
      c • fieldToDeRhamCohomology K X n α :=
  rfl

/-- On the rational lattice, the complexified comparison agrees with the original map. -/
@[simp] lemma fieldToDeRhamComplexification_ofField
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : H^n(X; K)) :
    fieldToDeRhamComplexification K X n (1 ⊗ₜ[K] α) =
      fieldToDeRhamCohomology K X n α := by
  simp

/-- The part of the holomorphic de Rham complex in form degrees at least `p` is zero when `p`
is above the complex dimension. -/
lemma hodgeFilteredDeRhamComplex_isZero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    IsZero (hodgeFilteredDeRhamComplex X p) := by
  rw [hodgeFilteredDeRhamComplex,
    HomologicalComplex.isZero_stupidTrunc_iff]
  refine ⟨fun n => ?_⟩
  change IsZero ((holomorphicDeRhamComplexInt X).X (p + n))
  exact (holomorphicDeRhamComplexInt X).isZero_of_isStrictlyLE
    (dim X.left) (p + n) (by lia)

/-- Above the complex dimension the filtered-to-full inclusion has zero source and hence is the
zero morphism. -/
lemma hodgeFilteredDeRhamInclusion_eq_zero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    hodgeFilteredDeRhamInclusion X p = 0 :=
  (hodgeFilteredDeRhamComplex_isZero_of_lt X hp).eq_of_src _ _

/-- The Hodge filtration is zero above the complex dimension. -/
lemma hodgeFiltration_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    hodgeFiltration X p n = ⊥ := by
  rw [hodgeFiltration]
  change (hypercohomologyMap X
    (hodgeFilteredDeRhamInclusion X p) n).range = ⊥
  rw [hodgeFilteredDeRhamInclusion_eq_zero_of_lt X hp,
    hypercohomologyMap_zero]
  simp

/-- Conjugation on de Rham hypercohomology is an involution. -/
lemma deRhamConj_involutive [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Involutive (deRhamConj X n) := by
  intro α
  rw [deRhamConj_apply, deRhamConj_apply, AddEquiv.symm_apply_apply,
    ← hypercohomologyMap_comp_apply, conjConstantComplexSheafComplexInt_comp_self,
    hypercohomologyMap_id]
  exact AddEquiv.apply_symm_apply _ α

@[simp] lemma deRhamConjSemilinear_apply [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : DeRhamHypercohomology X n) :
    deRhamConjSemilinear X n α = deRhamConj X n α := rfl

/-! #### Real coefficient fields

The hypothesis `hK` below says conjugation fixes the image of `K` in `ℂ`, equivalently that
`K → ℂ` lands in `ℝ`. It holds for `ℚ` and fails for `ℚ(i) ⊆ ℂ`. -/

/-- If conjugation fixes the image of `K` in `ℂ`, it fixes the constant `K`-sheaf sitting inside
the constant `ℂ`-sheaf. -/
lemma fieldToComplexConstantSheaf_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheaf K X ≫ conjConstantComplexSheaf X =
      fieldToComplexConstantSheaf K X := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (starRingEnd ℂ).toAddMonoidHom) =
    (constantSheaf J AddCommGrpCat).map
      (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)
  rw [← Functor.map_comp]
  congr 1
  ext q
  exact hK q

/-- The same statement for the integer-indexed constant complexes. -/
lemma fieldToComplexConstantSheafComplexInt_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheafComplexInt K X ≫
        conjConstantComplexSheafComplexInt X =
      fieldToComplexConstantSheafComplexInt K X := by
  unfold fieldToComplexConstantSheafComplexInt conjConstantComplexSheafComplexInt
    conjConstantComplexComplex constantFieldSheafComplexInt constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_conj K X hK]

/-- Such classes are their own conjugates in complex constant-sheaf cohomology. -/
lemma conj_fieldToComplexCohomology
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    hypercohomologyMap X (conjConstantComplexSheafComplexInt X) n
        (fieldToComplexCohomology K X n α) =
      fieldToComplexCohomology K X n α := by
  unfold fieldToComplexCohomology
  rw [← hypercohomologyMap_comp_apply,
    fieldToComplexConstantSheafComplexInt_comp_conj K X hK]

/-- Such classes are their own conjugates in de Rham hypercohomology. This is the step that
makes `F^p` alone the right condition over `ℚ`. -/
lemma deRhamConj_fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    deRhamConj X n (fieldToDeRhamCohomology K X n α) =
      fieldToDeRhamCohomology K X n α := by
  have he : fieldToDeRhamCohomology K X n α =
      complexConstantCohomologyDeRhamAddEquiv X inferInstance n
        (fieldToComplexCohomology K X n α) :=
    fieldToDeRhamCohomology_factor K X n α
  rw [he, deRhamConj_apply, AddEquiv.symm_apply_apply,
    conj_fieldToComplexCohomology K X hK]

lemma mem_conjHodgeFiltrationComplexSubmodule_iff [IsIntegral X.left] [Smooth X.hom]
    (p n : ℤ) (α : DeRhamHypercohomology X n) :
    α ∈ conjHodgeFiltrationComplexSubmodule X p n ↔
      deRhamConj X n α ∈ hodgeFiltration X p n :=
  Iff.rfl

lemma mem_hodgePiece_iff [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ)
    (α : DeRhamHypercohomology X n) :
    α ∈ hodgePiece X p q n ↔
      α ∈ hodgeFiltration X p n ∧ deRhamConj X n α ∈ hodgeFiltration X q n :=
  Iff.rfl

/-- A Hodge piece is contained in the corresponding Hodge filtration step. -/
lemma hodgePiece_le_hodgeFiltration [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ) :
    hodgePiece X p q n ≤ hodgeFiltrationComplexSubmodule X p n :=
  inf_le_left

/-- Above the complex dimension the Hodge pieces vanish, because `F^p` already does. -/
lemma hodgePiece_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (q n : ℤ) :
    hodgePiece X p q n = ⊥ := by
  refine le_antisymm (fun α hα ↦ ?_) bot_le
  have h : α ∈ hodgeFiltration X p n := hα.1
  rw [hodgeFiltration_eq_bot_of_lt X hp n, AddSubgroup.mem_bot] at h
  exact h

lemma filteredToDeRhamCohomology_zero_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FilteredDeRhamHypercohomology X 0 n) :
    filteredToDeRhamCohomology X 0 n α =
      hodgeFiltrationZeroEquiv X n α := rfl

/-- The zeroth Hodge filtration is the whole de Rham hypercohomology group. -/
lemma hodgeFiltration_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltration X 0 n = ⊤ := by
  ext α
  simp only [hodgeFiltration, AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
  exact ⟨(hodgeFiltrationZeroEquiv X n).symm α,
    filteredToDeRhamCohomology_zero_apply X n _ |>.trans
      ((hodgeFiltrationZeroEquiv X n).apply_symm_apply α)⟩

/-- `F⁰ ⊓ conj F⁰` is everything, in every degree, because `F⁰` is. In degree `0` this says the
`(0,0)` piece is everything; in other degrees it is not a statement about a Hodge piece. -/
lemma hodgePiece_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgePiece X 0 0 n = ⊤ := by
  refine eq_top_iff.mpr fun α _ ↦ ⟨?_, ?_⟩
  · show α ∈ hodgeFiltration X 0 n
    rw [hodgeFiltration_zero_eq_top X n]
    trivial
  · show deRhamConj X n α ∈ hodgeFiltration X 0 n
    rw [hodgeFiltration_zero_eq_top X n]
    trivial

/-- The rational submodule underlying `F⁰` is the whole de Rham hypercohomology group. -/
lemma hodgeFiltrationSubmodule_zero_eq_top [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    hodgeFiltrationSubmodule K X 0 n = ⊤ := by
  refine SetLike.ext fun α ↦ ?_
  change α ∈ hodgeFiltration X 0 n ↔ α ∈ (⊤ :
    Submodule K (DeRhamHypercohomology X n))
  rw [hodgeFiltration_zero_eq_top X n]
  simp

/-- When conjugation fixes `K`, a `K`-class is its own conjugate, so `F^p` already implies
`(p,p)` and the Hodge filtration alone cuts out the Hodge classes. -/
lemma hodgeClasses_eq_comap_hodgeFiltrationSubmodule [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) (p : ℕ) :
    Hdg^p(K; X) =
      (hodgeFiltrationSubmodule K X p (2 * p)).comap
        (fieldToDeRhamCohomologyLinear K X (2 * p)) := by
  refine SetLike.ext fun α ↦ ?_
  show fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgePiece X (p : ℤ) (p : ℤ) (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgeFiltration X (p : ℤ) (2 * (p : ℤ))
  rw [mem_hodgePiece_iff, deRhamConj_fieldToDeRhamCohomology K X hK]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h⟩⟩

/-- Over `ℚ`, the coefficient field the Hodge conjecture is stated for, the `(p,p)` and `F^p`
definitions agree. -/
lemma hodgeClasses_rat_eq_comap_hodgeFiltrationSubmodule [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) :
    Hdg^p(ℚ; X) =
      (hodgeFiltrationSubmodule ℚ X p (2 * p)).comap
        (fieldToDeRhamCohomologyLinear ℚ X (2 * p)) :=
  hodgeClasses_eq_comap_hodgeFiltrationSubmodule ℚ X (fun q ↦ by simp) p

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma hodgeClasses_eq_ker_of_lt [IsIntegral X.left] [Smooth X.hom] {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) =
      LinearMap.ker (fieldToDeRhamCohomologyLinear K X (2 * p)) := by
  rw [hodgeClasses,
    hodgePiece_eq_bot_of_lt X (by exact_mod_cast hp : (dim X.left : ℤ) < (p : ℤ)),
    Submodule.restrictScalars_bot, Submodule.comap_bot]

/-- If the analytic constant-to-holomorphic de Rham comparison is a quasi-isomorphism, rational
Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt_of_quasiIso [IsIntegral X.left] [Smooth X.hom]
    (h : QuasiIso (constantsToHolomorphicDeRhamComplexInt X))
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) = ⊥ := by
  rw [hodgeClasses_eq_ker_of_lt K X hp]
  exact LinearMap.ker_eq_bot.mpr (fieldToDeRhamCohomology_injective_of_quasiIso K X h (2 * p))

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt
    [IsIntegral X.left] [Smooth X.hom]
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(K; X) = ⊥ :=
  hodgeClasses_eq_bot_of_lt_of_quasiIso K X inferInstance hp

/-- The direct definition of rational Hodge classes agrees with the definition using the
complexified rational lattice. -/
lemma hodgeClassesViaComplexification_eq [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    hodgeClassesViaComplexification K X p =
      Hdg^p(K; X) := by
  ext α
  change fieldToDeRhamComplexification K X (2 * (p : ℤ))
      (HodgeStructure.ofBase K
        (H^(2 * (p : ℤ))(X; K)) α) ∈
        hodgePiece X p p (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgePiece X p p (2 * (p : ℤ))
  rw [HodgeStructure.ofBase_apply,
    fieldToDeRhamComplexification_ofField]

lemma mem_hodgeClasses_iff [IsIntegral X.left] [Smooth X.hom]
    (p : ℕ) (α : H^(2 * p)(X; K)) :
    α ∈ Hdg^p(K; X) ↔
      IsHodgeClass K X p α :=
  Iff.rfl

/-- Every rational degree-zero cohomology class belongs to the rational Hodge subgroup. -/
lemma hodgeClasses_zero_eq_top [IsIntegral X.left] [Smooth X.hom]
    :
    Hdg^0(K; X) = ⊤ := by
  refine SetLike.ext fun α ↦ ?_
  change fieldToDeRhamCohomology K X (2 * (0 : ℕ)) α ∈
      hodgePiece X ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) (2 * (0 : ℕ)) ↔ True
  simp only [Nat.cast_zero]
  rw [hodgePiece_zero_eq_top]
  trivial

/-- Every rational degree-zero class has Hodge type `(0,0)`. -/
lemma isHodgeClass_zero [IsIntegral X.left] [Smooth X.hom]
    (α : H^0(X; K)) :
    IsHodgeClass K X 0 α := by
  change α ∈ Hdg^0(K; X)
  rw [hodgeClasses_zero_eq_top]
  trivial

end AlgebraicGeometry.ComplexPoint
