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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.NormalSlicePurity
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Relative homology near a flattened support

Radial compression into a small product-norm ball preserves the zero-normal plane.
Composing with the inverse flattening chart gives a pair homeomorphism from the normal-slice
model to a small open neighborhood paired with its support complement, along which the
homology calculation and the normalized class are transported.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

/-- The actual pair consisting of a neighborhood and the complement of a support in it. -/
abbrev neighborhoodSupportComplementPair (W S : Set M) : TopPair :=
  TopPair.ofSubset (X := TopCat.of W) {w | w.1 ∉ S}

/-- Radial compression centered on the zero-normal plane preserves that plane exactly. -/
private theorem univBall_normal_eq_zero_iff (a : E) (r : ℝ) (hr : 0 < r)
    (v : E × (Fin c → ℂ)) :
    (OpenPartialHomeomorph.univBall (a, (0 : Fin c → ℂ)) r v).2 = 0 ↔ v.2 = 0 := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr]
  change (r • ((Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v) + (a, (0 : Fin c → ℂ))).2 = 0 ↔ _
  have hs : (Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ ≠ 0 := by positivity
  simp only [Prod.snd_add, Prod.smul_snd, add_zero, smul_eq_zero, hr.ne', hs, false_or]

variable (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (x : M) (hx : x ∈ e.source)

include hx

omit [NormedSpace ℝ E] in
/-- A positive coordinate-ball radius is obtained from the actual open chart target. -/
theorem exists_flattenedSupportRadius :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (e x) r ⊆ e.target :=
  Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)

def flattenedSupportRadius : ℝ := (exists_flattenedSupportRadius E c e x hx).choose

omit [NormedSpace ℝ E] in
theorem flattenedSupportRadius_pos : 0 < flattenedSupportRadius E c e x hx :=
  (exists_flattenedSupportRadius E c e x hx).choose_spec.1

omit [NormedSpace ℝ E] in
private theorem ball_flattenedSupportRadius_subset :
    Metric.ball (e x) (flattenedSupportRadius E c e x hx) ⊆ e.target :=
  (exists_flattenedSupportRadius E c e x hx).choose_spec.2

/-- Actual radial compression followed by the inverse chart. -/
def flattenedSupportEmbedding : OpenPartialHomeomorph (E × (Fin c → ℂ)) M :=
  (OpenPartialHomeomorph.univBall (e x) (flattenedSupportRadius E c e x hx)).trans e.symm

theorem flattenedSupportEmbedding_source :
    (flattenedSupportEmbedding E c e x hx).source = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ⟨by simp, ?_⟩
  apply ball_flattenedSupportRadius_subset E c e x hx
  rw [← OpenPartialHomeomorph.univBall_target (e x)
    (flattenedSupportRadius_pos E c e x hx)]
  exact (OpenPartialHomeomorph.univBall (e x)
    (flattenedSupportRadius E c e x hx)).map_source (by simp)

/-- The actual open neighborhood on which the support has the normal-slice pair model. -/
def flattenedSupportNeighborhood : TopologicalSpace.Opens M :=
  ⟨(flattenedSupportEmbedding E c e x hx).target,
    (flattenedSupportEmbedding E c e x hx).open_target⟩

theorem flattenedSupportNeighborhood_subset_source :
    (flattenedSupportNeighborhood E c e x hx : Set M) ⊆ e.source :=
  fun _ hy => hy.1

/-- The homeomorphism is constructed from radial compression and the inverse chart. -/
def flattenedSupportHomeomorph :
    (E × (Fin c → ℂ)) ≃ₜ flattenedSupportNeighborhood E c e x hx :=
  (((Homeomorph.setCongr (flattenedSupportEmbedding_source E c e x hx)).trans
    (Homeomorph.Set.univ _)).symm).trans
      (flattenedSupportEmbedding E c e x hx).toHomeomorphSourceTarget

theorem flattenedSupportHomeomorph_coordinates (v : E × (Fin c → ℂ)) :
    e (flattenedSupportHomeomorph E c e x hx v) =
      OpenPartialHomeomorph.univBall (e x) (flattenedSupportRadius E c e x hx) v := by
  apply e.right_inv
  apply ball_flattenedSupportRadius_subset E c e x hx
  rw [← OpenPartialHomeomorph.univBall_target (e x)
    (flattenedSupportRadius_pos E c e x hx)]
  exact (OpenPartialHomeomorph.univBall (e x)
    (flattenedSupportRadius E c e x hx)).map_source (by simp)

variable (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (h0 : (e x).2 = 0)

include hS h0

theorem flattenedSupportHomeomorph_mem_support_iff (v : E × (Fin c → ℂ)) :
    (flattenedSupportHomeomorph E c e x hx v : M) ∈ S ↔ v.2 = 0 := by
  rw [hS _ (flattenedSupportNeighborhood_subset_source E c e x hx
    (flattenedSupportHomeomorph E c e x hx v).2), flattenedSupportHomeomorph_coordinates]
  have he : e x = ((e x).1, (0 : Fin c → ℂ)) := Prod.ext rfl h0
  rw [he]
  exact univBall_normal_eq_zero_iff E c _ _ (flattenedSupportRadius_pos E c e x hx) v

/-- Restriction of the actual homeomorphism to the support complements. -/
def flattenedSupportComplementHomeomorph :
    {v : E × (Fin c → ℂ) | v.2 ≠ 0} ≃ₜ
      {w : flattenedSupportNeighborhood E c e x hx | (w : M) ∉ S} :=
  (flattenedSupportHomeomorph E c e x hx).subtype fun v =>
    not_congr (flattenedSupportHomeomorph_mem_support_iff E c e x hx S hS h0 v).symm

/-- A genuine pair isomorphism from the standard normal model to the local support pair. -/
def flattenedSupportPairIso : normalSlicePair E c ≅
    neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨flattenedSupportHomeomorph E c e x hx,
      (flattenedSupportHomeomorph E c e x hx).continuous⟩)
    (TopCat.ofHom ⟨flattenedSupportComplementHomeomorph E c e x hx S hS h0,
      (flattenedSupportComplementHomeomorph E c e x hx S hS h0).continuous⟩) (by ext v; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(flattenedSupportHomeomorph E c e x hx).symm,
      (flattenedSupportHomeomorph E c e x hx).symm.continuous⟩)
    (TopCat.ofHom ⟨(flattenedSupportComplementHomeomorph E c e x hx S hS h0).symm,
      (flattenedSupportComplementHomeomorph E c e x hx S hS h0).symm.continuous⟩) (by ext v; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      exact (flattenedSupportComplementHomeomorph E c e x hx S hS h0).left_inv v
    · ext v
      exact (flattenedSupportHomeomorph E c e x hx).left_inv v
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext v
      exact (flattenedSupportComplementHomeomorph E c e x hx S hS h0).right_inv v
    · ext v
      exact (flattenedSupportHomeomorph E c e x hx).right_inv v

/-- Local relative homology is computed by actual pair maps and tangent contraction. -/
def flattenedSupportRelativeHomologyIso (n : ℕ) :
    RelativeHomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n ≅
        RelativeHomology ℚ (standardComplexPuncturedPair c) n :=
  ((relativeHomologyFunctor ℚ n).mapIso (flattenedSupportPairIso E c e x hx S hS h0).symm) ≪≫
    normalSliceRelativeHomologyIso E c n

/-- The local class is the transport of the fixed, exactly normalized complex normal class. -/
def flattenedSupportNormalClass :
    RelativeHomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) (2 * c) :=
  (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).inv.hom
    (standardComplexLocalClass c)

/-- The corresponding cohomology equivalence is the dual of those same actual maps. -/
def flattenedSupportRelativeCohomologyEquiv (n : ℕ) :
    RelativeCohomology ℚ (standardComplexPuncturedPair c) n ≃ₗ[ℚ]
      RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n :=
  (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 n).toLinearEquiv.dualMap

end AlgebraicTopology.Singular
