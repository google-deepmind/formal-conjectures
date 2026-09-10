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

public import FormalConjecturesForMathlib.AlgebraicTopology.BoundedBelowFlasqueComplex
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Cokernel preservation for a map with flasque source and kernel

The sheaf-forgetful functor is not exact in general. For a map whose source and
kernel are flasque, its image is flasque and both associated short exact sequences
remain exact on every open. Consequently its actual cokernel is preserved by the
forgetful functor. This is a local hypothesis on one actual map, not a fabricated
exactness instance for the whole forgetful functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf.IsFlasque

variable {X : TopCat.{u}}

/-- A short exact sequence with flasque first term stays short exact as presheaves.
The epimorphism is proved sectionwise using the actual flasque lifting theorem. -/
lemma shortExact_map_forget {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [S.X₁.IsFlasque] :
    (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X)).ShortExact := by
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} X
  have hleft := ((Functor.preservesFiniteLimits_tfae F).out 3 1).mp
    (inferInstance : PreservesFiniteLimits F)
  have he : (S.map F).Exact ∧ Mono (S.map F).f := hleft S ⟨hS.exact, hS.mono_f⟩
  have hg : Epi (F.map S.g) := by
    have : ∀ U, Epi ((F.map S.g).app U) := fun U =>
      epi_of_shortExact (U := U.unop) hS
    exact NatTrans.epi_of_epi_app _
  exact { exact := he.1, mono_f := he.2, epi_g := hg }

variable {A B : TopCat.Sheaf AddCommGrpCat.{u} X} (f : A ⟶ B)

/-- The actual kernel/source/image short complex. -/
def kernelImageShortComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (kernel.ι f) (Abelian.factorThruImage f) (by
    rw [← cancel_mono (Abelian.image.ι f), zero_comp, Category.assoc,
      Abelian.image.fac, kernel.condition])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Kernel, source, and actual image form a short exact sequence. -/
lemma kernelImageShortComplex_shortExact : (kernelImageShortComplex f).ShortExact := by
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  let φ : kernelImageShortComplex f ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.image.ι f
      comm₁₂ := by simp [kernelImageShortComplex, T]
      comm₂₃ := by simp [kernelImageShortComplex, T] }
  have he : (kernelImageShortComplex f).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr (ShortComplex.exact_kernel f)
  exact { exact := he
          mono_f := by dsimp [kernelImageShortComplex]; infer_instance
          epi_g := by dsimp [kernelImageShortComplex]; infer_instance }

/-- The image/codomain/cokernel short exact sequence is the actual abelian image sequence. -/
def imageCokernelShortComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (Abelian.image.ι f) (cokernel.π f)
    (Abelian.image_ι_comp_eq_zero (cokernel.condition f))

lemma imageCokernelShortComplex_shortExact : (imageCokernelShortComplex f).ShortExact := by
  have he := (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).exact_iff_exact_image_ι
  exact { exact := he.mp (ShortComplex.exact_cokernel f)
          mono_f := by dsimp [imageCokernelShortComplex]; infer_instance
          epi_g := by dsimp [imageCokernelShortComplex]; infer_instance }

/-- The actual image is flasque when both the source and kernel are flasque. -/
lemma image_isFlasque [A.IsFlasque] [(kernel f).IsFlasque] : (Abelian.image f).IsFlasque := by
  let : (kernelImageShortComplex f).X₁.IsFlasque := inferInstanceAs ((kernel f).IsFlasque)
  let : (kernelImageShortComplex f).X₂.IsFlasque := inferInstanceAs A.IsFlasque
  exact of_shortExact_of_isFlasque₁₂ (kernelImageShortComplex_shortExact f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For one map with flasque source and kernel, the forgetful functor preserves its
actual cokernel. No exactness assertion is made for arbitrary sheaf maps. -/
lemma forget_preservesCokernel [A.IsFlasque] [(kernel f).IsFlasque] :
    PreservesColimit (parallelPair f 0) (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := by
  let F := TopCat.Sheaf.forget AddCommGrpCat.{u} X
  let := image_isFlasque f
  let : (kernelImageShortComplex f).X₁.IsFlasque := inferInstanceAs ((kernel f).IsFlasque)
  let : (imageCokernelShortComplex f).X₁.IsFlasque := inferInstanceAs ((Abelian.image f).IsFlasque)
  have h1 := shortExact_map_forget (kernelImageShortComplex_shortExact f)
  have h2 := shortExact_map_forget (imageCokernelShortComplex_shortExact f)
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let φ : T.map F ⟶ (imageCokernelShortComplex f).map F :=
    { τ₁ := F.map (Abelian.factorThruImage f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [T, imageCokernelShortComplex]
        rw [Category.comp_id, ← F.map_comp, Abelian.image.fac]
      comm₂₃ := by simp [T, imageCokernelShortComplex] }
  let : Epi φ.τ₁ := h1.epi_g
  have he : (T.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr h2.exact
  let : Epi (T.map F).g := h2.epi_g
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm he.gIsCokernel)

end TopCat.Sheaf.IsFlasque
