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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ClosedImmersionResidueField
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexAffineSpace

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points of a closed subscheme

This file describes the complex points of a closed subscheme of a complex scheme. The local
lifting of sections proved in
`FormalConjecturesForMathlib.AlgebraicGeometry.ClosedImmersionResidueField` identifies the analytic
subbasis of the closed subscheme with the subbasis induced from the ambient scheme. Its analytic
image is the set of complex points supported on the closed subscheme, which is closed, so a closed
immersion induces a closed topological embedding on complex points.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Topology

namespace AlgebraicGeometry

namespace ComplexPoint

open Point

variable {X Y : Over (Spec ↧ℂ)}

/-- For a complex scheme locally of finite type, a complex point is determined by its underlying
closed point. -/
lemma underlying_injective_of_locallyOfFiniteType
    [LocallyOfFiniteType X.hom] :
    Function.Injective (@underlying ℂ _ _ X) := fun z w h ↦
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq X.hom (Over.w z) (Over.w w) h)

/-- A monomorphism of schemes induces an injection on complex points. -/
lemma map_injective_of_mono (i : X ⟶ Y) [Mono i] :
    Function.Injective (map i) := fun _ _ h ↦ (cancel_mono i).mp h

section AnalyticClosedImmersion

variable {A B : Over (Spec ↧ℂ)} (i : A ⟶ B)

/-- The analytic image of a closed immersion consists exactly of the complex points supported
on its scheme-theoretic image. -/
lemma range_map_of_closedImmersion [IsClosedImmersion i.left] :
    Set.range (map i) =
      {y : ComplexPoint B | y.underlying ∈ Set.range i.left} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.underlying, (underlying_map i x).symm⟩
  · rintro ⟨x, hx⟩
    change i.left x = y.residueData.1 at hx
    let φ : A.left.residueField x ⟶ ↧ℂ :=
      (IsClosedImmersion.residueFieldIso x).inv ≫
        (B.left.residueFieldCongr hx).hom ≫ y.residueData.2
    let zHom : Spec ↧ℂ ⟶ A.left :=
      (Scheme.SpecToEquivOfField ℂ A.left).symm ⟨x, φ⟩
    have hzmap : zHom ≫ i.left = y.left := by
      dsimp only [zHom]
      rw [Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
        ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      rw [← Category.assoc, ← Spec.map_comp]
      dsimp [φ]
      rw [← IsClosedImmersion.residueFieldIso_hom,
        Iso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        Scheme.residueFieldCongr_fromSpecResidueField]
      exact (Scheme.SpecToEquivOfField ℂ B.left).symm_apply_apply y.left
    have hz : zHom ≫ A.hom = 𝟙 _ := by
      rw [← Over.w i, ← Category.assoc, hzmap]
      exact Over.w y
    exact ⟨Over.homMk zHom hz, Over.OverMorphism.ext hzmap⟩

/-- The analytic image of a closed immersion is closed. -/
lemma isClosed_range_map_of_closedImmersion [IsClosedImmersion i.left] :
    @IsClosed (ComplexPoint B) analyticTopology
      (Set.range (map i)) := by
  let : TopologicalSpace (ComplexPoint B) := analyticTopology
  rw [range_map_of_closedImmersion i]
  apply isOpen_compl_iff.mp
  let U : B.left.Opens :=
    ⟨(Set.range i.left)ᶜ, i.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have h : IsOpen (overOpen U : Set (ComplexPoint B)) :=
    isOpen_overOpen (X := B) U
  convert h using 1
  ext y
  simp [overOpen, U]

/-- A subbasic analytic open of a closed subscheme is open in the topology induced from the
ambient analytic space. -/
lemma isOpen_induced_chartSubbasic [IsClosedImmersion i.left]
    (U : B.left.Opens) (s : Γ(A.left, i.left ⁻¹ᵁ U)) (O : Set ℂ) (hO : IsOpen O) :
    @IsOpen (ComplexPoint A)
      (TopologicalSpace.induced (map i) analyticTopology)
      (overOpen (i.left ⁻¹ᵁ U) ∩ evaluate (i.left ⁻¹ᵁ U) s ⁻¹' O) := by
  let : TopologicalSpace (ComplexPoint B) := analyticTopology
  let : TopologicalSpace (ComplexPoint A) :=
    TopologicalSpace.induced (map i) analyticTopology
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨hzU, hzO⟩
  obtain ⟨V, hVU, ⟨r, hr⟩, hzV⟩ :=
    IsClosedImmersion.exists_local_ambient_lift U s z.underlying hzU
  let T : Set (ComplexPoint B) :=
    overOpen V ∩ evaluate V r ⁻¹' O
  refine ⟨map i ⁻¹' T, ?_, ?_, ?_⟩
  · rintro w ⟨hwV, hwO⟩
    have hwV' : w.underlying ∈ i.left ⁻¹ᵁ V :=
      (mem_overOpen_map_iff i w V).mp hwV
    have hpre : i.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ U :=
      leOfHom ((Opens.map i.left.base).map hVU)
    refine ⟨hpre hwV', ?_⟩
    have hmap := evaluate_map i V r w
    change evaluate (X := B) V r _ =
      evaluate (X := A) (i.left ⁻¹ᵁ V) (i.left.app V r) w at hmap
    rw [hr] at hmap
    have hres := evaluate_res (X := A)
      (U := i.left ⁻¹ᵁ U) (V := i.left ⁻¹ᵁ V) hpre s w hwV'
    have hsection :
        (((TopCat.Presheaf.pushforward CommRingCat i.left.base).obj A.left.presheaf).map hVU.op) s =
          A.left.presheaf.map (homOfLE hpre).op s := rfl
    rw [hsection] at hmap
    change evaluate (i.left ⁻¹ᵁ U) s w ∈ O
    rw [hres]
    exact hmap ▸ hwO
  · exact (isOpen_overOpen_inter_preimage (X := B) V r O hO).preimage
      continuous_induced_dom
  · refine ⟨?_, ?_⟩
    · exact (mem_overOpen_map_iff i z V).mpr hzV
    · have hmap := evaluate_map i V r z
      change evaluate (X := B) V r _ =
        evaluate (X := A) (i.left ⁻¹ᵁ V) (i.left.app V r) z at hmap
      rw [hr] at hmap
      have hpre : i.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ U :=
        leOfHom ((Opens.map i.left.base).map hVU)
      have hres := evaluate_res (X := A)
        (U := i.left ⁻¹ᵁ U) (V := i.left ⁻¹ᵁ V) hpre s z hzV
      have hsection :
          (((TopCat.Presheaf.pushforward CommRingCat i.left.base).obj A.left.presheaf).map hVU.op) s =
            A.left.presheaf.map (homOfLE hpre).op s := rfl
      rw [hsection] at hmap
      change evaluate V r (map i z) ∈ O
      rw [hmap]
      exact hres ▸ hzO

/-- Every generator of the analytic topology on a closed subscheme is open for the topology
induced from the ambient analytic space. -/
lemma analyticSubbasis_isOpen_induced [IsClosedImmersion i.left]
    {W : Set (ComplexPoint A)} (hW : W ∈ analyticSubbasis) :
    @IsOpen (ComplexPoint A)
      (TopologicalSpace.induced (map i) analyticTopology) W := by
  obtain ⟨U, s, O, hO, rfl⟩ := hW
  obtain ⟨q, hq, hpre⟩ :=
    i.left.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  let Q : B.left.Opens := ⟨q, hq⟩
  have hQU : i.left ⁻¹ᵁ Q = U := Opens.ext hpre
  subst U
  exact isOpen_induced_chartSubbasic i Q s O hO

/-- A closed immersion induces the subspace topology on complex points. -/
lemma isInducing_map_of_closedImmersion [IsClosedImmersion i.left] :
    @IsInducing (ComplexPoint A) (ComplexPoint B)
      analyticTopology analyticTopology (map i) := by
  let : TopologicalSpace (ComplexPoint A) := analyticTopology
  let : TopologicalSpace (ComplexPoint B) := analyticTopology
  rw [isInducing_iff]
  apply le_antisymm
  · exact continuous_iff_le_induced.mp (continuous_map i)
  · rw [show (analyticTopology : TopologicalSpace (ComplexPoint A)) =
      .generateFrom analyticSubbasis from analyticTopology_eq_generateFrom]
    exact le_generateFrom_iff_subset_isOpen.mpr fun _ hW ↦
      analyticSubbasis_isOpen_induced i hW

/-- A closed immersion induces a topological embedding on complex points. -/
lemma isEmbedding_map_of_closedImmersion [IsClosedImmersion i.left] :
    @IsEmbedding (ComplexPoint A) (ComplexPoint B)
      analyticTopology analyticTopology (map i) := by
  let : TopologicalSpace (ComplexPoint A) := analyticTopology
  let : TopologicalSpace (ComplexPoint B) := analyticTopology
  let : Mono i := Over.mono_of_mono_left i
  exact ⟨isInducing_map_of_closedImmersion i, map_injective_of_mono i⟩

/-- A closed immersion induces a closed topological embedding on complex points. -/
lemma isClosedEmbedding_map_of_closedImmersion [IsClosedImmersion i.left] :
    @IsClosedEmbedding (ComplexPoint A) (ComplexPoint B)
      analyticTopology analyticTopology (map i) := by
  let : TopologicalSpace (ComplexPoint A) := analyticTopology
  let : TopologicalSpace (ComplexPoint B) := analyticTopology
  exact ⟨isEmbedding_map_of_closedImmersion i, isClosed_range_map_of_closedImmersion i⟩

end AnalyticClosedImmersion

end ComplexPoint

end AlgebraicGeometry
