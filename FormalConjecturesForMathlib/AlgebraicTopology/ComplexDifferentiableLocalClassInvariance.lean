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

public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexLinearLocalClassInvariance
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativePairExcision
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Invariance of the complex local class under differentiable coordinate changes

This file supplies the nonlinear local-degree step in the comparison of complex charts.  If a
continuous map fixes the origin, is complex differentiable there, and has invertible derivative,
then on a sufficiently small neighborhood its straight-line homotopy to the derivative avoids the
origin away from the origin.  Point excision lets us use this local homotopy to compare the induced
maps on the ambient local homology group.  Combining this with the complex-linear calculation shows
that the map preserves the standard complex local class.

The only global condition is the one required to even define a self-map of the point-complement
pair: the map has no zero away from the origin.  In chart applications this follows from
injectivity of the coordinate change.  No local homotopy or local-degree datum is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter Asymptotics

namespace AlgebraicTopology.Singular

variable (d : ℕ)

/-- A continuous map fixing the origin and having no other zero defines a self-map of the
punctured complex affine-space pair. -/
def complexPuncturedPairMapOf
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (_hf0 : f 0 = 0) (hf_ne : ∀ z, z ≠ 0 → f z ≠ 0) :
    standardComplexPuncturedPair d ⟶ standardComplexPuncturedPair d :=
  TopPair.ofHom
    (TopCat.ofHom ⟨f, hf⟩)
    (TopCat.ofHom
      ⟨fun z ↦ ⟨f z.1, hf_ne z.1 z.2⟩,
        by fun_prop⟩)
    (by ext z; rfl)

@[simp]
lemma complexPuncturedPairMapOf_fst_apply
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf_ne : ∀ z, z ≠ 0 → f z ≠ 0) (z : Fin d → ℂ) :
    TopPair.Hom.fst (complexPuncturedPairMapOf d f hf hf0 hf_ne) z = f z := rfl

/-- Point excision upgrades a homotopy on any open neighborhood of the distinguished point to
equality of the two induced maps on ambient relative homology. -/
theorem relativeHomologyMap_eq_of_neighborhood_pairHomotopy
    {Y : TopPair} (n : ℕ) (F G : standardComplexPuncturedPair d ⟶ Y)
    (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (H : TopPair.Homotopy
      (neighborhoodPointComplementPairMap U 0 ≫ F)
      (neighborhoodPointComplementPairMap U 0 ≫ G)) :
    relativeHomologyMap ℚ n F = relativeHomologyMap ℚ n G := by
  ext a
  obtain ⟨b, rfl⟩ := neighborhoodPointComplement_relativeHomologyMap_surjective
    U 0 hU h0U n a
  have h := H.relativeHomologyMap_apply_eq (R := ℚ) n b
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply] using h

/-- Two chart-local classes agree if the compressed chart maps are homotopic after restriction
to any open neighborhood of the model origin.  This is the germ-local version of
`localClassOfChart_eq_of_pairHomotopy`. -/
theorem localClassOfChart_eq_of_neighborhood_pairHomotopy
    {M : Type} [TopologicalSpace M]
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ))
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (H : TopPair.Homotopy
      (neighborhoodPointComplementPairMap U 0 ≫ chartModelEmbeddingPair d e x hx)
      (neighborhoodPointComplementPairMap U 0 ≫ chartModelEmbeddingPair d e' x hx')) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  unfold localClassOfChart
  rw [relativeHomologyMap_eq_of_neighborhood_pairHomotopy d (2 * d)
    (chartModelEmbeddingPair d e x hx) (chartModelEmbeddingPair d e' x hx') U hU h0U H]

/-- The straight line from a differentiable map to its injective derivative avoids zero on a
sufficiently small punctured neighborhood.

This is the analytic heart of the nonlinear local-degree argument.  The proof compares the
first-order error with an anti-Lipschitz lower bound for the derivative. -/
theorem exists_open_straightLine_ne_zero
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (f' : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hf0 : f 0 = 0) (hf' : HasFDerivAt f f' 0) (hf'_inj : Function.Injective f') :
    ∃ U : Set (Fin d → ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ U → z ≠ 0 →
        f' z + (((t : ℝ) : ℂ) • (f z - f' z)) ≠ 0 := by
  obtain ⟨K, hK_pos, hK⟩ :=
    f'.toLinearMap.injective_iff_antilipschitz.mp hf'_inj
  let ε : ℝ := ((K : ℝ) * 2)⁻¹
  have hK_real_pos : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have herr : ∀ᶠ z in nhds 0,
      ‖f z - f 0 - f' (z - 0)‖ ≤ ε * ‖z - 0‖ :=
    (isLittleO_iff.1 hf'.isLittleO) hε_pos
  rw [hf0] at herr
  simp only [sub_zero, sub_zero] at herr
  obtain ⟨U, hUsub, hUopen, h0U⟩ := mem_nhds_iff.mp herr
  refine ⟨U, hUopen, h0U, ?_⟩
  intro t z hzU hz
  have herr_z : ‖f z - f' z‖ ≤ ε * ‖z‖ := hUsub hzU
  have hbound : ‖z‖ ≤ (K : ℝ) * ‖f' z‖ := by
    have hbound' := hK.le_mul_dist z 0
    have h_apply (x : Fin d → ℂ) : f'.toLinearMap x = f' x := rfl
    simpa only [dist_eq_norm, h_apply, sub_zero, map_zero] using hbound'
  have hf'z_ne : f' z ≠ 0 := by
    simpa only [map_zero] using hf'_inj.ne hz
  have hf'z_pos : 0 < ‖f' z‖ := norm_pos_iff.mpr hf'z_ne
  have herr_lt : ‖f z - f' z‖ < ‖f' z‖ := by
    calc
      ‖f z - f' z‖ ≤ ε * ‖z‖ := herr_z
      _ ≤ ε * ((K : ℝ) * ‖f' z‖) :=
        mul_le_mul_of_nonneg_left hbound hε_pos.le
      _ = (1 / 2 : ℝ) * ‖f' z‖ := by
        rw [show ε * ((K : ℝ) * ‖f' z‖) =
            (ε * (K : ℝ)) * ‖f' z‖ by ring]
        congr 1
        dsimp [ε]
        field_simp [hK_real_pos.ne']
      _ < ‖f' z‖ := by nlinarith
  intro hzero
  have heq : f' z = -(((t : ℝ) : ℂ) • (f z - f' z)) :=
    eq_neg_iff_add_eq_zero.mpr hzero
  have ht : ‖((t : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg t.2.1] using t.2.2
  have hle : ‖f' z‖ ≤ ‖f z - f' z‖ := by
    calc
      ‖f' z‖ = ‖-(((t : ℝ) : ℂ) • (f z - f' z))‖ := congrArg norm heq
      _ = ‖((t : ℝ) : ℂ)‖ * ‖f z - f' z‖ := by rw [norm_neg, norm_smul]
      _ ≤ 1 * ‖f z - f' z‖ :=
        mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = ‖f z - f' z‖ := one_mul _
  exact (not_lt_of_ge hle) herr_lt

/-- A map defined continuously on a neighborhood and avoiding the origin off its distinguished
point gives a map from that neighborhood pair to the standard punctured pair. -/
def complexNeighborhoodPuncturedPairMapOf
    (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d → ℂ))
    (hf : ContinuousOn f U) (_hf0 : f 0 = 0)
    (hf_ne : ∀ z, z ∈ U → z ≠ 0 → f z ≠ 0) :
    neighborhoodPointComplementPair U 0 ⟶ standardComplexPuncturedPair d :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun z ↦ f z.1, hf.domRestrict⟩)
    (TopCat.ofHom
      ⟨fun z ↦ ⟨f z.1.1, hf_ne z.1.1 z.1.2 z.2⟩,
        Continuous.subtype_mk (hf.domRestrict.comp continuous_subtype_val) _⟩)
    (by ext z; rfl)

/-- The germ-local straight-line homotopy, requiring continuity and nonvanishing only on its
source neighborhood. -/
def complexStraightLineLocalPairHomotopy
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (U : Set (Fin d → ℂ))
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : ContinuousOn f U)
    (hf0 : f 0 = 0) (hf_ne : ∀ z, z ∈ U → z ≠ 0 → f z ≠ 0)
    (hline : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ U → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0) :
    TopPair.Homotopy
      (neighborhoodPointComplementPairMap U 0 ≫ complexMatrixPuncturedPairMap d A hA)
      (complexNeighborhoodPuncturedPairMapOf d U f hf hf0 hf_ne) where
  fst :=
    { toFun := fun tx ↦
        A.mulVec tx.2.1 + (((tx.1 : ℝ) : ℂ) • (f tx.2.1 - A.mulVec tx.2.1))
      continuous_toFun := by
        have hAz : Continuous (fun tx : unitInterval × U ↦ A.mulVec tx.2.1) :=
          A.mulVecLin.continuous_of_finiteDimensional.comp
            (continuous_subtype_val.comp continuous_snd)
        have hfz : Continuous (fun tx : unitInterval × U ↦ f tx.2.1) :=
          hf.domRestrict.comp continuous_snd
        have ht : Continuous (fun tx : unitInterval × U ↦ ((tx.1 : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
        exact hAz.add (ht.smul (hfz.sub hAz))
      map_zero_left := fun z ↦ by
        change A.mulVec z.1 + (((0 : unitInterval) : ℝ) : ℂ) •
          (f z.1 - A.mulVec z.1) = A.mulVec z.1
        simp
      map_one_left := fun z ↦ by
        change A.mulVec z.1 + (((1 : unitInterval) : ℝ) : ℂ) •
          (f z.1 - A.mulVec z.1) = f z.1
        simp }
  snd :=
    { toFun := fun tx ↦
        ⟨A.mulVec tx.2.1.1 +
            (((tx.1 : ℝ) : ℂ) • (f tx.2.1.1 - A.mulVec tx.2.1.1)),
          hline tx.1 tx.2.1.1 tx.2.1.2 tx.2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        have hval : Continuous
            (fun tx : unitInterval × {u : U | u.1 ≠ 0} ↦ tx.2.1.1) :=
          continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
        have hAz : Continuous
            (fun tx : unitInterval × {u : U | u.1 ≠ 0} ↦ A.mulVec tx.2.1.1) :=
          A.mulVecLin.continuous_of_finiteDimensional.comp hval
        have hfz : Continuous
            (fun tx : unitInterval × {u : U | u.1 ≠ 0} ↦ f tx.2.1.1) :=
          hf.domRestrict.comp (continuous_subtype_val.comp continuous_snd)
        have ht : Continuous
            (fun tx : unitInterval × {u : U | u.1 ≠ 0} ↦ ((tx.1 : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
        exact hAz.add (ht.smul (hfz.sub hAz))
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        change A.mulVec z.1.1 + (((0 : unitInterval) : ℝ) : ℂ) •
          (f z.1.1 - A.mulVec z.1.1) = A.mulVec z.1.1
        simp
      map_one_left := fun z ↦ by
        apply Subtype.ext
        change A.mulVec z.1.1 + (((1 : unitInterval) : ℝ) : ℂ) •
          (f z.1.1 - A.mulVec z.1.1) = f z.1.1
        simp }
  w := rfl

/-- A genuinely local coordinate-change theorem.  On some open neighborhood `V` contained in
the prescribed coordinate domain `U`, the local map sends every lift of the standard local class
through point excision back to the standard local class.  In particular, neither a global
extension nor a global injectivity/nonvanishing hypothesis is needed. -/
theorem exists_open_complexDifferentiable_localClass_invariance
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : ContinuousOn f U)
    (hf0 : f 0 = 0)
    (hf' : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    ∃ (V : Set (Fin d → ℂ)) (hVU : V ⊆ U)
        (hf_ne : ∀ z, z ∈ V → z ≠ 0 → f z ≠ 0),
      IsOpen V ∧ 0 ∈ V ∧
      ∀ c : RelativeHomology ℚ (neighborhoodPointComplementPair V 0) (2 * d),
        relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) c =
            standardComplexLocalClass d →
          relativeHomologyMap ℚ (2 * d)
              (complexNeighborhoodPuncturedPairMapOf d V f (hf.mono hVU) hf0 hf_ne) c =
            standardComplexLocalClass d := by
  let f' : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    A.mulVecLin.toContinuousLinearMap
  have hf'_apply (z : Fin d → ℂ) : f' z = A.mulVec z := rfl
  have hf'_inj : Function.Injective f' := fun x y hxy ↦
    A.mulVec_injective_of_det_ne_zero hA (by simpa only [← hf'_apply] using hxy)
  obtain ⟨W, hW, h0W, hline⟩ :=
    exists_open_straightLine_ne_zero d f f' hf0 hf' hf'_inj
  let V := U ∩ W
  have hV : IsOpen V := hU.inter hW
  have h0V : 0 ∈ V := ⟨h0U, h0W⟩
  have hlineV : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ V → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0 := by
    intro t z hz hz0
    simpa only [hf'_apply] using hline t z hz.2 hz0
  have hfV : ContinuousOn f V := hf.mono Set.inter_subset_left
  have hf_neV : ∀ z, z ∈ V → z ≠ 0 → f z ≠ 0 := by
    intro z hz hz0
    simpa using hlineV (1 : unitInterval) z hz hz0
  refine ⟨V, Set.inter_subset_left, hf_neV, hV, h0V, ?_⟩
  intro c hc
  let H := complexStraightLineLocalPairHomotopy d A hA V f hfV hf0 hf_neV hlineV
  have hhom := H.relativeHomologyMap_apply_eq (R := ℚ) (2 * d) c
  calc
    relativeHomologyMap ℚ (2 * d)
        (complexNeighborhoodPuncturedPairMapOf d V f hfV hf0 hf_neV) c =
        relativeHomologyMap ℚ (2 * d)
          (neighborhoodPointComplementPairMap V 0 ≫
            complexMatrixPuncturedPairMap d A hA) c := hhom.symm
    _ = relativeHomologyMap ℚ (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) c) := by
          rw [relativeHomologyMap_comp]
          rfl
    _ = relativeHomologyMap ℚ (2 * d) (complexMatrixPuncturedPairMap d A hA)
        (standardComplexLocalClass d) := by rw [hc]
    _ = standardComplexLocalClass d :=
      relativeHomologyMap_complexMatrix_standardComplexLocalClass d A hA

/-- A puncture-preserving straight line from an invertible complex-linear map to a nonlinear
map gives a homotopy of pair maps after restricting the source to the neighborhood on which the
straight line avoids the origin. -/
def complexStraightLineNeighborhoodPairHomotopy
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf_ne : ∀ z, z ≠ 0 → f z ≠ 0)
    (U : Set (Fin d → ℂ))
    (hline : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ U → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0) :
    TopPair.Homotopy
      (neighborhoodPointComplementPairMap U 0 ≫
        complexMatrixPuncturedPairMap d A hA)
      (neighborhoodPointComplementPairMap U 0 ≫
        complexPuncturedPairMapOf d f hf hf0 hf_ne) where
  fst :=
    { toFun := fun tx ↦
        A.mulVec tx.2.1 + (((tx.1 : ℝ) : ℂ) • (f tx.2.1 - A.mulVec tx.2.1))
      continuous_toFun := by fun_prop
      map_zero_left := fun z ↦ by
        change A.mulVec z.1 + (((0 : unitInterval) : ℝ) : ℂ) •
          (f z.1 - A.mulVec z.1) = A.mulVec z.1
        simp
      map_one_left := fun z ↦ by
        change A.mulVec z.1 + (((1 : unitInterval) : ℝ) : ℂ) •
          (f z.1 - A.mulVec z.1) = f z.1
        simp }
  snd :=
    { toFun := fun tx ↦
        ⟨A.mulVec tx.2.1.1 +
            (((tx.1 : ℝ) : ℂ) • (f tx.2.1.1 - A.mulVec tx.2.1.1)),
          hline tx.1 tx.2.1.1 tx.2.1.2 tx.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        change A.mulVec z.1.1 + (((0 : unitInterval) : ℝ) : ℂ) •
          (f z.1.1 - A.mulVec z.1.1) = A.mulVec z.1.1
        simp
      map_one_left := fun z ↦ by
        apply Subtype.ext
        change A.mulVec z.1.1 + (((1 : unitInterval) : ℝ) : ℂ) •
          (f z.1.1 - A.mulVec z.1.1) = f z.1.1
        simp }
  w := rfl

/-- A continuous, origin-preserving map with no other zero and invertible complex derivative at
the origin preserves the standard complex local homology class.

Unlike a global straight-line argument, only the germ of the homotopy is required to avoid zero:
`exists_open_straightLine_ne_zero` constructs the required open neighborhood, and point excision
then cancels its inclusion on relative homology. -/
theorem relativeHomologyMap_complexDifferentiable_standardComplexLocalClass
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf_ne : ∀ z, z ≠ 0 → f z ≠ 0)
    (hf' : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    relativeHomologyMap ℚ (2 * d) (complexPuncturedPairMapOf d f hf hf0 hf_ne)
        (standardComplexLocalClass d) =
      standardComplexLocalClass d := by
  let f' : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    A.mulVecLin.toContinuousLinearMap
  have hf'_apply (z : Fin d → ℂ) : f' z = A.mulVec z := rfl
  have hf'_inj : Function.Injective f' := fun x y hxy ↦
    A.mulVec_injective_of_det_ne_zero hA (by simpa only [← hf'_apply] using hxy)
  obtain ⟨U, hU, h0U, hline⟩ :=
    exists_open_straightLine_ne_zero d f f' hf0 hf' hf'_inj
  have hline' : ∀ (t : unitInterval) (z : Fin d → ℂ), z ∈ U → z ≠ 0 →
      A.mulVec z + (((t : ℝ) : ℂ) • (f z - A.mulVec z)) ≠ 0 := by
    simpa only [hf'_apply] using hline
  let H := complexStraightLineNeighborhoodPairHomotopy d A hA f hf hf0 hf_ne U hline'
  have hmaps := relativeHomologyMap_eq_of_neighborhood_pairHomotopy d (2 * d)
    (complexMatrixPuncturedPairMap d A hA)
    (complexPuncturedPairMapOf d f hf hf0 hf_ne) U hU h0U H
  rw [← hmaps]
  exact relativeHomologyMap_complexMatrix_standardComplexLocalClass d A hA

/-- Injectivity is the natural chart-transition hypothesis ensuring that the origin is the only
zero, so an injective differentiable coordinate change with invertible complex derivative
preserves the standard local class. -/
theorem relativeHomologyMap_complexDifferentiable_standardComplexLocalClass_of_injective
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (f : (Fin d → ℂ) → (Fin d → ℂ)) (hf : Continuous f)
    (hf0 : f 0 = 0) (hf_inj : Function.Injective f)
    (hf' : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    relativeHomologyMap ℚ (2 * d)
        (complexPuncturedPairMapOf d f hf hf0 (fun z hz ↦ by
          intro hfz
          apply hz
          apply hf_inj
          simpa only [hf0] using hfz))
        (standardComplexLocalClass d) =
      standardComplexLocalClass d := by
  exact relativeHomologyMap_complexDifferentiable_standardComplexLocalClass d A hA f hf hf0 _ hf'

end AlgebraicTopology.Singular
