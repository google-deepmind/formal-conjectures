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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.FlattenedSupportLocalHomology

/-!
# Actual relative homology near a flattened support

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.FlattenedSupportLocalHomology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)

variable (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (x : M) (hx : x ∈ e.source)

include hx

@[simp] theorem flattenedSupportEmbedding_zero : flattenedSupportEmbedding E c e x hx 0 = x := by
  change e.symm (OpenPartialHomeomorph.univBall (e x) _ 0) = x
  rw [OpenPartialHomeomorph.univBall_apply_zero, e.left_inv hx]

theorem mem_flattenedSupportNeighborhood : x ∈ flattenedSupportNeighborhood E c e x hx := by
  have h := (flattenedSupportEmbedding E c e x hx).map_source
    (show 0 ∈ (flattenedSupportEmbedding E c e x hx).source by
      rw [flattenedSupportEmbedding_source]; trivial)
  change x ∈ (flattenedSupportEmbedding E c e x hx).target
  simpa only [flattenedSupportEmbedding_zero] using h

@[simp] theorem flattenedSupportHomeomorph_apply (v : E × (Fin c → ℂ)) :
    (flattenedSupportHomeomorph E c e x hx v : M) =
      flattenedSupportEmbedding E c e x hx v := rfl

variable (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (h0 : (e x).2 = 0)

include hS h0

theorem flattenedSupportRelativeHomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (RelativeHomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n) :=
  (standardComplexLocalHomology_isZero_of_ne c n hn).of_iso
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 n)

@[simp] theorem flattenedSupportNormalClass_normalization :
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).hom.hom
      (flattenedSupportNormalClass E c e x hx S hS h0) = standardComplexLocalClass c :=
  ConcreteCategory.congr_hom
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).inv_hom_id _

theorem flattenedSupportRelativeCohomology_isZero_of_ne (n : ℕ) (hn : n ≠ 2 * c) :
    IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) n)) := by
  have := ModuleCat.subsingleton_of_isZero
    (flattenedSupportRelativeHomology_isZero_of_ne E c e x hx S hS h0 n hn)
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicTopology.Singular
