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

public import FormalConjecturesForMathlib.AlgebraicTopology.CohomologySheafStalkVanishing
public import FormalConjecturesForMathlib.AlgebraicTopology.OpenSheafRestriction
public import FormalConjecturesForMathlib.AlgebraicTopology.LowestFlasqueCohomology

/-!
# Local vanishing on an open subset and actual restricted section complexes

Cofinal calculations are performed on opens of the original ambient space.
The literal image/preimage identities identify these section complexes with
sections of the actual open-restricted sheaf complex. For a bounded-below
flasque complex, lower local vanishing therefore implies lower cohomology
vanishing of sections on that open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
  (U : Opens X)

/-- Cofinal ambient calculations on points of `U` imply actual cohomology-sheaf
vanishing of the restricted complex. -/
theorem openRestriction_homology_isZero_of_cofinal_sections (n : ℤ)
    (hlocal : ∀ (x : X), x ∈ U → ∀ (V : Opens X), x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        IsZero ((((supportEvaluation X W).mapHomologicalComplex (.up ℤ)).obj K).homology n)) :
    IsZero ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).obj K).homology n) := by
  apply cohomologySheaf_isZero_of_cofinal_sections
  intro x V hxV
  let V' := U.isOpenEmbedding.functor.obj V
  have hxV' : x.1 ∈ V' := ⟨x, hxV, rfl⟩
  obtain ⟨W, hWV', hxW, hW⟩ := hlocal x.1 x.2 V' hxV'
  let W' := (Opens.map U.inclusion').obj W
  have hWU : W ≤ U := by
    intro y hy
    obtain ⟨v, _, hv⟩ := hWV' hy
    exact hv ▸ v.2
  have he : U.isOpenEmbedding.functor.obj W' = W := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hWU]
  refine ⟨W', ?_, hxW, ?_⟩
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := hWV' hy
    exact (Subtype.ext hvy : v = y) ▸ hv
  · change IsZero ((((supportEvaluation X (U.isOpenEmbedding.functor.obj W')).mapHomologicalComplex
      (.up ℤ)).obj K).homology n)
    rwa [he]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On a bounded-below flasque complex, actual lower local vanishing on `U`
implies vanishing of the section-complex cohomology on `U`. -/
theorem sectionCohomology_isZero_of_cofinal_lower_vanishing (N n : ℤ) [K.IsStrictlyGE N]
    (hflasque : ∀ j, (K.X j).IsFlasque)
    (hlocal : ∀ j : ℤ, j ≤ n → ∀ (x : X), x ∈ U → ∀ (V : Opens X), x ∈ V →
      ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        IsZero ((((supportEvaluation X W).mapHomologicalComplex (.up ℤ)).obj K).homology j)) :
    IsZero ((((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n) := by
  let L := ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
    (.up ℤ)).obj K
  have hL (j : ℤ) (hj : j ≤ n) : IsZero (L.homology j) :=
    openRestriction_homology_isZero_of_cofinal_sections X K U j (hlocal j hj)
  have hLF (j : ℤ) : (L.X j).IsFlasque := by
    let := hflasque j
    exact openSheafRestriction_isFlasque X U (K.X j)
  let e := lowestSectionCohomologyIso (TopCat.of U) L N n
    (fun j hj => hL j hj.le) hLF ⊤
  have hzero := ((supportEvaluation (TopCat.of U) ⊤).map_isZero (hL n le_rfl)).of_iso e
  change IsZero ((((supportEvaluation X (U.isOpenEmbedding.functor.obj ⊤)).mapHomologicalComplex
    (.up ℤ)).obj K).homology n) at hzero
  rwa [Opens.isOpenEmbedding_obj_top] at hzero

end TopCat.Sheaf
