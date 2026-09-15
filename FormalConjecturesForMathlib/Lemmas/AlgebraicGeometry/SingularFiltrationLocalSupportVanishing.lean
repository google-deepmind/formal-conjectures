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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentSingularClosedFiltration
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportOpenTransport
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportCohomologySheaf
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenRestrictedCohomologyVanishing

/-!
# Local support vanishing on canonical singular-filtration layers

Every point of a smooth layer has a fixed-dimensional affine source neighborhood, of
dimension strictly less than that of the original cycle component. Deleting the image of
the discarded source complement makes that neighborhood closed in a smaller ambient open,
and normal neighborhoods there transport to the original projective ambient space and its
fixed supported injective resolution. The local lower vanishing follows from those maps
and the dimension bounds.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) (k : ℕ)

local instance singularFiltrationLocalSupportVanishingAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

include d hx in
/-- Every point in the actual `k`th layer has cofinal actual ambient neighborhoods
whose relative cohomology below degree `2(p+1)` vanishes. -/
theorem cycleComponentSingularLayer_exists_relativeCohomology_vanishing
    (y : ComplexPoint X)
    (hy : y ∈ cycleComponentSingularAnalyticClosedFiltration X x k)
    (hyNext : y ∉ cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧
      W ≤ (cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl ∧
      y ∈ W ∧ ∀ n : ℕ, n < 2 * (p + 1) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X))) n)) := by
  obtain ⟨z, rfl⟩ := (cycleComponentSingularAnalyticClosedFiltration_layer X x k).ge ⟨hy, hyNext⟩
  let O := cycleComponentSingularStratumAmbientOpen X x k
  let OX := cycleComponentSingularStratumAmbientOpenOver X x k
  let Y := cycleComponentSingularFiltrationStratumOver X x k
  let i : Y ⟶ OX := cycleComponentSingularStratumClosedLiftOver X x k
  obtain ⟨A, hA, hzA, m, hm, hcodim, hdim⟩ :=
    cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
      X x (d := d) hx k z.underlying
  let : SmoothOfRelativeDimension m (openScheme Y A).hom := hdim
  let zA := asOpenPoint Y A z hzA
  let f := Point.map (openInclusion X O)
  have hS : f ⁻¹'
      (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X)) =
        Set.range (Point.map i) :=
    (cycleComponentSingularStratumClosedLift_complexPoints_range X x k).symm
  have he : f (Point.map (openInclusion Y A ≫ i) zA) =
      Point.map (cycleComponentSingularFiltrationStratumOverι X x k) z := by
    apply Over.OverMorphism.ext
    change (zA.left ≫ (A.ι ≫ cycleComponentSingularStratumClosedLift X x k)) ≫ O.ι =
      z.left ≫ cycleComponentSingularFiltrationStratumι X x k
    rw [Category.assoc, Category.assoc, cycleComponentSingularStratumClosedLift_ι,
      ← Category.assoc]
    exact congrArg (fun g => g ≫ cycleComponentSingularFiltrationStratumι X x k)
      (liftToOpen_fac Y A z hzA)
  let V' := V ⊓ (cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl
  have hzV' : f (Point.map (openInclusion Y A ≫ i) zA) ∈ V' := by
    rw [he]
    exact ⟨hyV, hyNext⟩
  have : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d O.ι X.hom
  obtain ⟨W, hWV', hzW, hW⟩ := exists_smoothClosedSourceOpenImageNeighborhood
    OX Y i m d f (isOpenEmbedding_map_open X O)
    (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X))
    hS A zA V' hzV'
  exact ⟨W, hWV'.trans inf_le_left, hWV'.trans inf_le_right, he ▸ hzW,
    fun n hn ↦ hW n (by omega)⟩

include d hx in
/-- The original ambient supported injective complex has cofinally vanishing section
cohomology below `2(p+1)` at every point outside the next closed support. -/
theorem cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1))
    (y : ComplexPoint X)
    (hyNext : y ∉ cycleComponentSingularAnalyticClosedFiltration X x (k + 1))
    (V : Opens (ComplexPoint X)) (hyV : y ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ y ∈ W ∧
      IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex X
          (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  by_cases hneg : n < 0
  · refine ⟨V, le_rfl, hyV, ?_⟩
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).map_isZero
      ((complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x k)).isZero_of_isStrictlyGE 0 n hneg)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    by_cases hy : y ∈ cycleComponentSingularAnalyticClosedFiltration X x k
    · obtain ⟨W, hWV, _, hyW, hW⟩ :=
        cycleComponentSingularLayer_exists_relativeCohomology_vanishing X x (d := d) hx k
          y hy hyNext V hyV
      refine ⟨W, hWV, hyW, ?_⟩
      let : Subsingleton (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint X))) q) :=
        ModuleCat.subsingleton_of_isZero (hW q (by exact_mod_cast hn))
      let e := complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentSingularAnalyticClosedFiltration X x k) W q
      let : Subsingleton ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
            (complexSupportInjectiveComplex X
              (cycleComponentSingularAnalyticClosedFiltration X x k))).homology (q : ℤ)) :=
        e.injective.subsingleton
      exact AddCommGrpCat.isZero_of_subsingleton _
    · let W := V ⊓ (cycleComponentSingularAnalyticClosedFiltration X x k).compl
      refine ⟨W, inf_le_left, ⟨hyV, hy⟩, ?_⟩
      apply ShortComplex.isZero_homology_of_isZero_X₂
      exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
        (TopCat.of (ComplexPoint X))
        (cycleComponentSingularAnalyticClosedFiltration X x k).compl W
        ((ambientRationalInjectiveComplex X).X (q : ℤ)) inf_le_right

include d hx in
/-- The exact open-layer section complex needed by finite support localization has
zero cohomology below `2(p+1)`. The resolution remains the one on the original
projective ambient variety; no injective resolution on a projective auxiliary open
is assumed. -/
theorem cycleComponentSingularLayerSectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSingularAnalyticClosedFiltration X x (k + 1)).compl).mapHomologicalComplex
        (.up ℤ)).obj (complexSupportInjectiveComplex X
          (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j ↦ TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X))
      (cycleComponentSingularAnalyticClosedFiltration X x k).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV ↦
      cycleComponentSingularLayer_exists_supportedInjectiveSection_vanishing
        X x (d := d) hx k j (hj.trans_lt hn) y hy V hyV

end AlgebraicGeometry.ComplexPoint
