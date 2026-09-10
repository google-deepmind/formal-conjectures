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

public import FormalConjecturesForMathlib.AlgebraicTopology.LocalFundamentalClass
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularChainSheafStalk
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# A normalized relative orientation class over a Euclidean neighborhood

The standard affine simplex has compact boundary disjoint from the origin. Consequently the
same simplex defines a relative cycle modulo the complement of a sufficiently small open ball.
Its restriction at the origin is exactly `standardLocalClass`, with its original vertex order.
Translation through the ball gives homotopies of pairs identifying its restriction at every
other point of the ball with the translate of that same normalized class.

The ball radius is chosen only to avoid the explicitly constructed boundary. No local homology
generator, orientation, or local representability theorem is supplied as data.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The image of the boundary of the standard affine simplex. -/
def standardAffineBoundarySupport (d : ℕ) : Set (StandardRealModel d) :=
  ⋃ i : Fin (d + 1), standardAffineSimplex d ''
    (fun t : stdSimplex ℝ (Fin (d + 1)) => t i) ⁻¹' {0}

lemma isCompact_standardAffineBoundarySupport (d : ℕ) :
    IsCompact (standardAffineBoundarySupport d) :=
  isCompact_iUnion fun i => (isClosed_eq ((continuous_apply i).comp continuous_subtype_val)
    continuous_const).isCompact.image (continuous_standardAffineSimplex d)

lemma zero_not_mem_standardAffineBoundarySupport (d : ℕ) :
    (0 : StandardRealModel d) ∉ standardAffineBoundarySupport d := by
  intro h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
  rcases hi with ⟨t, ht, hzero⟩
  exact standardAffineSimplex_ne_zero_of_coord_zero d t i ht hzero

lemma exists_standardOrientationRadius (d : ℕ) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : StandardRealModel d) r ⊆
      (standardAffineBoundarySupport d)ᶜ :=
  Metric.isOpen_iff.mp (isCompact_standardAffineBoundarySupport d).isClosed.isOpen_compl
    0 (zero_not_mem_standardAffineBoundarySupport d)

/-- A positive radius whose ball misses the boundary of the fixed standard simplex. -/
def standardOrientationRadius (d : ℕ) : ℝ :=
  (exists_standardOrientationRadius d).choose

lemma standardOrientationRadius_pos (d : ℕ) : 0 < standardOrientationRadius d :=
  (exists_standardOrientationRadius d).choose_spec.1

lemma ball_standardOrientationRadius_subset (d : ℕ) :
    Metric.ball (0 : StandardRealModel d) (standardOrientationRadius d) ⊆
      (standardAffineBoundarySupport d)ᶜ :=
  (exists_standardOrientationRadius d).choose_spec.2

/-- The small ball on which one and the same simplex represents the orientation. -/
def standardOrientationBall (d : ℕ) : TopologicalSpace.Opens (StandardRealModel d) :=
  ⟨Metric.ball 0 (standardOrientationRadius d), Metric.isOpen_ball⟩

lemma zero_mem_standardOrientationBall (d : ℕ) :
    (0 : StandardRealModel d) ∈ standardOrientationBall d :=
  Metric.mem_ball_self (standardOrientationRadius_pos d)

/-- The pair supporting the Euclidean neighborhood class, not just a point class. -/
abbrev standardOrientationBallPair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (StandardRealModel d))
    (standardOrientationBall d : Set (StandardRealModel d))ᶜ

/-- A boundary face as a simplex in the complement of the entire orientation ball. -/
def standardOrientationBallFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)),
      ((standardOrientationBall (n + 1) : Set (StandardRealModel (n + 1)))ᶜ :
        Set (StandardRealModel (n + 1)))) where
  toFun t := ⟨standardAffineSimplex (n + 1) (stdSimplex.map i.succAbove t), by
    intro hball
    apply ball_standardOrientationRadius_subset (n + 1) hball
    exact Set.mem_iUnion.mpr ⟨i, ⟨stdSimplex.map i.succAbove t,
      stdSimplex_map_succAbove_self_zero n i t, rfl⟩⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_standardAffineSimplex (n + 1)).comp
      (stdSimplex.continuous_map i.succAbove)) _

lemma standardOrientationBallFace_projection (n : ℕ) (i : Fin (n + 2)) :
    standardAmbientFaceChain n i ≫
      (relativeChainProjection ℚ (standardOrientationBallPair (n + 1))).f n = 0 := by
  let σ := ((standardOrientationBallPair (n + 1)).snd.toSSetObjEquiv (.op ⦋n⦌)).symm
    (standardOrientationBallFaceMap n i)
  have hσ :
      (TopCat.toSSet.map (standardOrientationBallPair (n + 1)).map).app _ σ =
        (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).δ i
          (standardSingularSimplex (n + 1)) := by
    apply ((standardOrientationBallPair (n + 1)).fst.toSSetObjEquiv _).injective
    ext t
    rfl
  rw [standardAmbientFaceChain, ← hσ]
  exact iota_subspace_relativeChainProjection ℚ (standardOrientationBallPair (n + 1)) σ

/-- The fixed ordered affine simplex projected modulo the complement of the ball. -/
def standardOrientationBallChain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).X d :=
  standardAmbientSimplexChain d ≫
    (relativeChainProjection ℚ (standardOrientationBallPair d)).f d

set_option backward.isDefEq.respectTransparency false in
lemma standardOrientationBallChain_boundary (d : ℕ) :
    standardOrientationBallChain d ≫
      ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).d
        d ((ComplexShape.down ℕ).next d) = 0 := by
  cases d with
  | zero => simp
  | succ n =>
    rw [ChainComplex.next_nat_succ, standardOrientationBallChain, Category.assoc,
      (relativeChainProjection ℚ (standardOrientationBallPair (n + 1))).comm,
      ← Category.assoc]
    change (standardAmbientSimplexChain (n + 1) ≫
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).right.d (n + 1) n) ≫ _ = 0
    rw [standardAmbientSimplexChain_boundary, Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro i _
    rw [Preadditive.zsmul_comp, standardOrientationBallFace_projection]
    simp

/-- The actual relative cycle on a neighborhood, obtained by lifting the fixed simplex. -/
def standardOrientationBallCycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).cycles d :=
  ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).liftCycles
    (standardOrientationBallChain d) ((ComplexShape.down ℕ).next d) rfl
    (standardOrientationBallChain_boundary d)

/-- The normalized neighborhood-relative class in degree `d`. -/
def standardOrientationBallClass (d : ℕ) :
    RelativeHomology ℚ (standardOrientationBallPair d) d :=
  ((standardOrientationBallCycle d ≫
    ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).homologyπ d).hom) 1

/-- Restriction from ball support to a point of that ball. -/
def standardOrientationBallPointMap (d : ℕ) (y : StandardRealModel d)
    (hy : y ∈ standardOrientationBall d) :
    standardOrientationBallPair d ⟶ TopPair.ofSubset (X := TopCat.of (StandardRealModel d))
      ({y}ᶜ : Set (StandardRealModel d)) :=
  supportInclusionPairMap _ (Set.singleton_subset_iff.mpr hy)

set_option backward.isDefEq.respectTransparency false in
lemma standardOrientationBallCycle_restrict_zero (d : ℕ) :
    standardOrientationBallCycle d ≫ HomologicalComplex.cyclesMap
      ((relativeChainFunctor ℚ).map
        (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))) d =
      standardLocalCycle d := by
  apply (cancel_mono ((standardLocalRelativeChainComplex d).iCycles d)).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    standardOrientationBallCycle, HomologicalComplex.liftCycles_i,
    standardLocalCycle_inclusion, standardOrientationBallChain, Category.assoc]
  have h := congrArg (fun f => f.f d)
    (relativeChainProjection_supportInclusion ℚ (TopCat.of (StandardRealModel d))
      (Set.singleton_subset_iff.mpr (zero_mem_standardOrientationBall d)))
  exact congrArg (fun f => standardAmbientSimplexChain d ≫ f) h

/-- At the center, the neighborhood class restricts to the original normalized class,
not merely to some generator or a nonzero rational multiple. -/
theorem standardOrientationBallClass_restrict_zero (d : ℕ) :
    relativeHomologyMap ℚ d
      (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))
      (standardOrientationBallClass d) = standardLocalClass d := by
  have hmor : standardOrientationBallCycle d ≫
      ((relativeChainFunctor ℚ).obj (standardOrientationBallPair d)).homologyπ d ≫
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d))) d =
      standardLocalCycle d ≫ (standardLocalRelativeChainComplex d).homologyπ d := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      standardOrientationBallCycle_restrict_zero]
  exact ConcreteCategory.congr_hom hmor 1

section Translation

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation carries the complement of the origin to the complement of its center. -/
def translationPointComplementPairMap (y : E) :
    TopPair.ofSubset (X := TopCat.of E) ({0}ᶜ : Set E) ⟶
      TopPair.ofSubset (X := TopCat.of E) ({y}ᶜ : Set E) := by
  refine TopPair.ofHom
    (TopCat.ofHom ⟨fun v : E => v + y, continuous_id.add continuous_const⟩) ?_ ?_
  · have hne : ∀ v : ({0}ᶜ : Set E), v.1 + y ∈ ({y}ᶜ : Set E) := by
      intro v h
      exact v.2 (add_right_cancel (show v.1 + y = 0 + y by simpa using h))
    exact TopCat.ofHom
      ⟨fun v => ⟨v.1 + y, hne v⟩,
        (continuous_subtype_val.add continuous_const).subtype_mk hne⟩
  · rfl

lemma convexSupport_translation_ne (U : Set E) (h0 : (0 : E) ∈ U)
    (hU : Convex ℝ U) (y : E) (hy : y ∈ U) (t : unitInterval)
    (v : E) (hv : v ∉ U) : v + (t : ℝ) • y ≠ y := by
  intro heq
  apply hv
  have hv' : v = (1 - (t : ℝ)) • y := by
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq heq
  rw [hv']
  exact hU.smul_mem_of_zero_mem h0 hy ⟨sub_nonneg.mpr t.2.2, by linarith [t.2.1]⟩

/-- Over convex support, restriction to `y` is homotopic to restriction to the origin
followed by translation. This is a homotopy of actual relative pairs. -/
def convexSupportTranslationPairHomotopy (U : Set E) (h0 : (0 : E) ∈ U)
    (hU : Convex ℝ U) (y : E) (hy : y ∈ U) :
    TopPair.Homotopy
      (X := TopPair.ofSubset (X := TopCat.of E) Uᶜ)
      (Y := TopPair.ofSubset (X := TopCat.of E) ({y}ᶜ : Set E))
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hy))
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr h0) ≫
        translationPointComplementPairMap E y) where
  fst :=
    { toFun := fun tv : unitInterval × E => tv.2 + (tv.1 : ℝ) • y
      continuous_toFun := by
        change Continuous (fun tv : unitInterval × E => tv.2 + (tv.1 : ℝ) • y)
        exact continuous_snd.add
          ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
      map_zero_left := fun v : E => by change v + (0 : ℝ) • y = v; simp
      map_one_left := fun v : E => by change v + (1 : ℝ) • y = v + y; simp }
  snd :=
    { toFun := fun tv => ⟨tv.2.1 + (tv.1 : ℝ) • y,
        convexSupport_translation_ne E U h0 hU y hy tv.1 tv.2.1 tv.2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp continuous_snd).add
          ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
      map_zero_left := fun v => by
        apply Subtype.ext
        change v.1 + (0 : ℝ) • y = v.1
        simp
      map_one_left := fun v => by
        apply Subtype.ext
        change v.1 + (1 : ℝ) • y = v.1 + y
        simp }
  w := rfl

end Translation

/-- At every point of the ball, restriction gives the exact translated standard class.
This is simultaneous local representability, with normalization fixed by the ordered simplex. -/
theorem standardOrientationBallClass_restrict (d : ℕ) (y : StandardRealModel d)
    (hy : y ∈ standardOrientationBall d) :
    relativeHomologyMap ℚ d (standardOrientationBallPointMap d y hy)
      (standardOrientationBallClass d) =
      relativeHomologyMap ℚ d (translationPointComplementPairMap (StandardRealModel d) y)
        (standardLocalClass d) := by
  have h := (convexSupportTranslationPairHomotopy (StandardRealModel d)
    (standardOrientationBall d) (zero_mem_standardOrientationBall d)
    (convex_ball _ _) y hy).relativeHomologyMap_apply_eq (R := ℚ) d
      (standardOrientationBallClass d)
  change relativeHomologyMap ℚ d (standardOrientationBallPointMap d y hy)
    (standardOrientationBallClass d) = relativeHomologyMap ℚ d
      (standardOrientationBallPointMap d 0 (zero_mem_standardOrientationBall d) ≫
        translationPointComplementPairMap (StandardRealModel d) y)
      (standardOrientationBallClass d) at h
  simpa only [relativeHomologyMap_comp, LinearMap.comp_apply,
    standardOrientationBallClass_restrict_zero] using h

end AlgebraicTopology.Singular
