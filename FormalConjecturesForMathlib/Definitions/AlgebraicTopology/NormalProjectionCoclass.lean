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
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.CenteredComplexEmbeddingOrientation
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentPurity
/-!
# Normal projections and the local support coclass

The normal projection of a support-flattening chart is a map of pairs on every open subset of
its source, and pulling the fixed normal coclass back along it is compatible with restriction.
The radial-fiber factorization below identifies that coclass with the normalized local coclass.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

/-- Inclusion of actual neighborhood/support-complement pairs. -/
def neighborhoodSupportInclusionPairMap {W V : Set M} (hWV : W ⊆ V) (S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1.1, hWV w.1.2⟩, w.2⟩, by fun_prop⟩) (by ext w; rfl)

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)

/-- The actual normal projection from a neighborhood support pair. -/
def chartNormalProjectionPair (W : Set M) (hW : W ⊆ e.source) :
    neighborhoodSupportComplementPair W S ⟶ standardComplexPuncturedPair c :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => (e w.1).2, ((e.continuousOn.mono hW).domRestrict).snd⟩)
    (TopCat.ofHom ⟨fun w => ⟨(e w.1.1).2, fun h => w.2 ((hS _ (hW w.1.2)).mpr h)⟩,
      ((((e.continuousOn.mono hW).domRestrict).comp continuous_subtype_val).snd).subtype_mk _⟩)
    (by ext w; rfl)

/-- The coclass on a whole chart neighborhood is the actual normal-projection pullback. -/
def chartNormalProjectionCoclass (W : Set M) (hW : W ⊆ e.source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W S) (2 * c) :=
  relativeCohomologyMap ℚ (2 * c) (chartNormalProjectionPair E c e S hS W hW)
    (normalizedDual (standardComplexLocalClass c) (standardComplexLocalClass_ne_zero_for_chart c))

variable (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

end AlgebraicTopology.Singular
