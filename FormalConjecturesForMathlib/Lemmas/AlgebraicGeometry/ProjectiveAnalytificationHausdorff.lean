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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ProjectiveAnalyticImmersion

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexOpen
import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Hausdorff analytifications of projective complex schemes

The analytification of an affine complex scheme is Hausdorff because global regular functions
separate its complex points. Any two points of finite-dimensional projective space lie in a
common affine basic open: an explicit integral linear form can be chosen not to vanish at either
of two homogeneous coordinate vectors. Pulling this open back along a closed projective
presentation proves that every projective complex scheme has Hausdorff analytification.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry

namespace ComplexPoint

open Point

/-- The analytification of an affine complex scheme is Hausdorff. -/
lemma t2Space_of_isAffine (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    @T2Space (ComplexPoint X) analyticTopology := by
  let : TopologicalSpace (ComplexPoint X) := analyticTopology
  rw [t2Space_iff_nhds]
  intro z w hzw
  have happ : z.left.appTop ≠ w.left.appTop := fun h ↦
    hzw (Over.OverMorphism.ext (ext_of_isAffine (Y := X.left) h))
  have hex : ∃ s : Γ(X.left, ⊤),
      (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop s) ≠
        (Scheme.ΓSpecIso ↧ℂ).hom (w.left.appTop s) := by
    by_contra hn
    push Not at hn
    apply happ
    ext s
    exact (Scheme.ΓSpecIso ↧ℂ).commRingCatIsoToRingEquiv.injective (hn s)
  obtain ⟨s, hs⟩ := hex
  have heval : evaluate ⊤ s z ≠ evaluate ⊤ s w := by
    simpa only [evaluate_top_eq_appTop] using hs
  obtain ⟨U, V, hU, hV, hzU, hwV, hUV⟩ := t2_separation heval
  refine ⟨evaluate ⊤ s ⁻¹' U,
    (hU.preimage (continuous_evaluate_top s)).mem_nhds hzU,
    evaluate ⊤ s ⁻¹' V,
    (hV.preimage (continuous_evaluate_top s)).mem_nhds hwV, ?_⟩
  exact hUV.preimage _

/-- A complex scheme whose every pair of complex points lies in a common affine open has a
Hausdorff analytification. -/
lemma t2Space_of_pair_mem_affineOpen (X : Over (Spec ↧ℂ))
    (hpair : ∀ z w : ComplexPoint X,
      ∃ U : X.left.Opens, z ∈ overOpen U ∧ w ∈ overOpen U ∧ IsAffine U.toScheme) :
    @T2Space (ComplexPoint X) analyticTopology := by
  let : TopologicalSpace (ComplexPoint X) := analyticTopology
  rw [t2Space_iff_nhds]
  intro z w hzw
  obtain ⟨U, hzU, hwU, hUaff⟩ := hpair z w
  let : IsAffine (openScheme X U).left := hUaff
  let : TopologicalSpace (ComplexPoint (openScheme X U)) := analyticTopology
  let : T2Space (ComplexPoint (openScheme X U)) :=
    t2Space_of_isAffine (openScheme X U)
  let : TopologicalSpace {q : ComplexPoint X // q ∈ overOpen U} :=
    TopologicalSpace.induced Subtype.val analyticTopology
  let : T2Space {q : ComplexPoint X // q ∈ overOpen U} :=
    (openHomeomorph X U).t2Space
  let zU : {q : ComplexPoint X // q ∈ overOpen U} := ⟨z, hzU⟩
  let wU : {q : ComplexPoint X // q ∈ overOpen U} := ⟨w, hwU⟩
  have hzwU : zU ≠ wU := fun h ↦ hzw (congrArg Subtype.val h)
  obtain ⟨A, B, hA, hB, hzA, hwB, hAB⟩ := t2_separation hzwU
  let e : {q : ComplexPoint X // q ∈ overOpen U} →
      ComplexPoint X := Subtype.val
  have he : IsOpenEmbedding e := (isOpen_overOpen (X := X) U).isOpenEmbedding_subtypeVal
  refine ⟨e '' A, (he.isOpenMap A hA).mem_nhds ⟨zU, hzA, rfl⟩,
    e '' B, (he.isOpenMap B hB).mem_nhds ⟨wU, hwB, rfl⟩, ?_⟩
  exact Set.disjoint_image_of_injective he.injective hAB

end ComplexPoint

namespace ComplexProjectiveSpace

open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- There is an integral linear form which is nonzero on each of two nonzero complex coordinate
vectors. -/
lemma exists_common_nonvanishing_linearForm {n : ℕ}
    (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ r : UniversalRing n,
      r ∈ UniversalGrading n 1 ∧
      (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) ≠ 0 ∧
      (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom w r) ≠ 0 := by
  let i := coordinateIndex v hv
  have hvi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  by_cases hwi : w i ≠ 0
  · refine ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X _ _, ?_, ?_⟩
    · simpa using hvi
    · simpa using hwi
  · let j := coordinateIndex w hw
    have hwj : w j ≠ 0 := coordinateIndex_ne_zero w hw
    have hwi0 : w i = 0 := not_ne_iff.mp hwi
    by_cases hvij : v i + v j ≠ 0
    · refine ⟨MvPolynomial.X i + MvPolynomial.X j,
        (UniversalGrading n 1).add_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · simpa using hvij
      · simpa [coordinateGlobalSectionsHom_X, hwi0] using hwj
    · refine ⟨MvPolynomial.X i - MvPolynomial.X j,
        (UniversalGrading n 1).sub_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · push Not at hvij
        have hvj : v j = -v i := by linear_combination hvij
        simp only [map_sub, coordinateGlobalSectionsHom_X]
        simp
        rw [hvj]
        simpa using hvi
      · simpa [coordinateGlobalSectionsHom_X, hwi0] using hwj

/-- A homogeneous polynomial is nonzero at a coordinate vector exactly when the corresponding
projective point lies in its basic open. -/
lemma chartIntegralProjAt_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (i : Fin (n + 1)) (hi : v i ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    chartIntegralProjAt v i hi ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  unfold chartIntegralProjAt
  rw [Scheme.Hom.comp_preimage, show Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) r =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr) from
    Proj.awayι_preimage_basicOpen
      (𝒜 := UniversalGrading n) (f := MvPolynomial.X i) (g := r)
      (m := 1) (m' := d)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one hr hd]
  rw [SpecMap_preimage_basicOpen, show HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr =
      HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) i) d r (by simpa using hr) by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem]]
  simp only [CommRingCat.hom_ofHom]
  rw [awayCoordinateEvaluation_mk v i hi d r hr]
  split_ifs with h
  · rw [h, zero_mul, PrimeSpectrum.basicOpen_zero]
    rfl
  · apply top_unique
    intro x hx
    change coordinateEvaluationHom v r * (v i)⁻¹ ^ d ∉ x.asIdeal
    rw [Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using mul_ne_zero h (pow_ne_zero d (inv_ne_zero hi))

/-- The basic-open membership formula without fixing the selected standard coordinate chart. -/
lemma chartIntegralProj_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  let i := coordinateIndex v hv
  let hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
  exact chartIntegralProjAt_preimage_basicOpen v i hi r hd hr

/-- The inverse image of a projective-spectrum basic open in complex projective space. -/
noncomputable def projectiveSpaceBasicOpen (n : ℕ) (r : UniversalRing n) :
    (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).Opens :=
  Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (UniversalGrading n))) ⁻¹ᵁ
    Proj.basicOpen (UniversalGrading n) r

set_option linter.style.haveILetI false in
/-- A positive-degree basic open in complex projective space is affine. -/
lemma projectiveSpaceBasicOpen_isAffine {n d : ℕ}
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    IsAffine (projectiveSpaceBasicOpen n r).toScheme := by
  haveI : IsAffineHom (Limits.terminal.from (Spec ↧ℂ)) := inferInstance
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom)
      (Limits.terminal.from (Proj (UniversalGrading n))) :=
    { of_isPullback := fun pb h ↦
        MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h }
  have hsnd : IsAffineHom (Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (UniversalGrading n)))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact @IsAffineHom.isAffine_preimage _ _ _ hsnd
    (Proj.basicOpen (UniversalGrading n) r)
    (Proj.isAffineOpen_basicOpen
      (𝒜 := UniversalGrading n) (f := r) hr hd)

/-- A coordinate point lies in the projective-space basic open whenever the defining homogeneous
polynomial is nonzero on its coordinates. -/
lemma vectorToComplexPoint_mem_projectiveSpaceBasicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d)
    (hne : coordinateEvaluationHom v r ≠ 0) :
    vectorToComplexPoint v hv ∈ Point.overOpen (projectiveSpaceBasicOpen n r) := by
  change (vectorToProjectiveSpace v hv) (IsLocalRing.closedPoint ℂ) ∈
    projectiveSpaceBasicOpen n r
  unfold projectiveSpaceBasicOpen
  change ((vectorToProjectiveSpace v hv) ≫ Limits.pullback.snd
    (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (UniversalGrading n))))
      (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen (UniversalGrading n) r
  rw [vectorToProjectiveSpace_toProj]
  change IsLocalRing.closedPoint ℂ ∈
    chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r
  rw [chartIntegralProj_preimage_basicOpen v hv r hd hr, if_neg hne]
  trivial

/-- Any two complex points of finite-dimensional projective space lie in a common affine open. -/
lemma projectiveSpace_pair_mem_affineOpen (n : ℕ)
    (z w : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    ∃ U : (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).Opens,
      z ∈ Point.overOpen U ∧ w ∈ Point.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨v, hvz⟩ := surjective_vectorToComplexPoint z
  obtain ⟨u, huw⟩ := surjective_vectorToComplexPoint w
  obtain ⟨r, hr, hrv, hru⟩ :=
    exists_common_nonvanishing_linearForm v.1 u.1 v.2 u.2
  refine ⟨projectiveSpaceBasicOpen n r, ?_, ?_,
    projectiveSpaceBasicOpen_isAffine r zero_lt_one hr⟩
  · rw [← hvz]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      v.1 v.2 r zero_lt_one hr hrv
  · rw [← huw]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      u.1 u.2 r zero_lt_one hr hru

/-- Finite-dimensional scheme-theoretic complex projective space is Hausdorff. -/
noncomputable instance instT2SpaceProjectiveSpaceComplexPoint (n : ℕ) :
    T2Space
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  ComplexPoint.t2Space_of_pair_mem_affineOpen
    (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
    (projectiveSpace_pair_mem_affineOpen n)

end ComplexProjectiveSpace

namespace ProjectiveSpace.Presentation

set_option linter.style.haveILetI false in
/-- Any two complex points of a projective presentation lie in a common affine open. -/
lemma pair_mem_affineOpen {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) (z w : ComplexPoint (Over.mk f)) :
    ∃ U : X.Opens, z ∈ Point.overOpen U ∧
      w ∈ Point.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨U, hzU, hwU, hUaff⟩ :=
    ComplexProjectiveSpace.projectiveSpace_pair_mem_affineOpen P.ambientDimension
      (analyticImmersion P z) (analyticImmersion P w)
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  let j := overImmersion P
  refine ⟨P.immersion ⁻¹ᵁ U,
    (Point.mem_overOpen_map_iff j z U).mp hzU,
    (Point.mem_overOpen_map_iff j w U).mp hwU, ?_⟩
  exact @IsAffineHom.isAffine_preimage _ _ P.immersion inferInstance U hUaff

/-- The analytification of an explicit projective presentation is Hausdorff. -/
theorem complexPoint_t2Space {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : ProjectiveSpace.Presentation f) :
    @T2Space (ComplexPoint (Over.mk f)) Point.analyticTopology :=
  ComplexPoint.t2Space_of_pair_mem_affineOpen (Over.mk f) (pair_mem_affineOpen P)

end ProjectiveSpace.Presentation

namespace IsProjective

/-- The analytification of a projective complex scheme is Hausdorff. -/
noncomputable instance complexPoint_t2Space {X : Over (Spec ↧ℂ)}
    [h : IsProjective X.hom] : T2Space (ComplexPoint X) :=
  ProjectiveSpace.Presentation.complexPoint_t2Space
    (Classical.choice h.nonempty_presentation)

end IsProjective

end AlgebraicGeometry
