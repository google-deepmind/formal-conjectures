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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlattenedSupportLocalHomology
/-!
# Transporting actual neighborhood-support pairs through embeddings

An embedding identifies a neighborhood and its support complement with their actual
images. Only equality of support membership on that neighborhood is required; no
cohomology comparison is supplied. Open embeddings therefore transport the cofinal
normal neighborhoods of auxiliary algebraic opens to the original ambient space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicTopology.Singular

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (f : M → N) (hf : IsEmbedding f) (W B : Set M) (S : Set N)
  (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S)

/-- The actual embedding-induced homeomorphism of the two support complements. -/
def neighborhoodSupportComplementImageHomeomorph :
    {w : W | (w : M) ∉ B} ≃ₜ {v : f '' W | (v : N) ∉ S} :=
  (hf.homeomorphImage W).subtype fun w => not_congr (hS w w.2)

/-- The literal pair isomorphism, with the embedding as ambient map. -/
def neighborhoodSupportPairImageIso :
    neighborhoodSupportComplementPair W B ≅
      neighborhoodSupportComplementPair (f '' W) S where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨hf.homeomorphImage W, (hf.homeomorphImage W).continuous⟩)
    (TopCat.ofHom ⟨neighborhoodSupportComplementImageHomeomorph f hf W B S hS,
      (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).continuous⟩)
    (by ext w; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(hf.homeomorphImage W).symm, (hf.homeomorphImage W).symm.continuous⟩)
    (TopCat.ofHom ⟨(neighborhoodSupportComplementImageHomeomorph f hf W B S hS).symm,
      (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).symm.continuous⟩)
    (by ext w; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).left_inv w
    · ext w
      exact (hf.homeomorphImage W).left_inv w
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).right_inv w
    · ext w
      exact (hf.homeomorphImage W).right_inv w

/-- Relative cohomology transport is the dual of the actual induced homology map. -/
def neighborhoodSupportPairImageCohomologyEquiv (n : ℕ) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair (f '' W) S) n ≃ₗ[ℚ]
      RelativeCohomology ℚ (neighborhoodSupportComplementPair W B) n :=
  (((relativeHomologyFunctor ℚ n).mapIso
    (neighborhoodSupportPairImageIso f hf W B S hS)).toLinearEquiv).dualMap

end AlgebraicTopology.Singular
