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

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The short exact sequence of kernels of a composition with an epimorphism

For `A → B → C`, restriction to kernels gives
`0 → ker f → ker (f ≫ g) → ker g → 0` when `f` is an epimorphism.
The maps are the actual kernel maps, with their inclusion normalizations retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

/-- The canonical sequence of the three kernels in a composable pair. -/
abbrev kernelCompositionShortComplex : ShortComplex C :=
  (kernelCokernelCompSequence.snakeInput f g).L₀

/-- Exactness in the middle does not require either map to be an epimorphism. -/
lemma kernelCompositionShortComplex_exact :
    (kernelCompositionShortComplex f g).Exact :=
  (kernelCokernelCompSequence.snakeInput f g).L₀_exact

/-- If the first map is onto, every element of the last kernel lifts to the middle one. -/
lemma kernelCompositionShortComplex_shortExact [Epi f] :
    (kernelCompositionShortComplex f g).ShortExact where
  exact := kernelCompositionShortComplex_exact f g
  mono_f := by
    dsimp [kernelCompositionShortComplex, kernelCokernelCompSequence.snakeInput]
    infer_instance
  epi_g := by
    have h := (kernelCokernelCompSequence_exact f g).exact 1
    apply h.epi_f
    change kernelCokernelCompSequence.δ f g = 0
    rw [kernelCokernelCompSequence.δ_fac]
    have hπ : cokernel.π f = 0 := (cancel_epi f).1 (by simp)
    simp [hπ]

variable (k : A ⟶ D) (hk : f ≫ g = k)

/-- The same sequence with a specified composite, preserving the actual kernel objects. -/
def kernelFactorizationShortComplex : ShortComplex C where
  X₁ := kernel f
  X₂ := kernel k
  X₃ := kernel g
  f := kernel.map f k (𝟙 A) g (by simpa using hk)
  g := kernel.map k g f (𝟙 D) (by simpa using hk.symm)
  zero := by
    apply (cancel_mono (kernel.ι g)).1
    simp

/-- Replacing the composite by its proved equality is a canonical kernel isomorphism. -/
def kernelCompositionFactorizationIso :
    kernelCompositionShortComplex f g ≅ kernelFactorizationShortComplex f g k hk :=
  ShortComplex.isoMk (Iso.refl _) (kernelIsoOfEq hk) (Iso.refl _)
    (by
      apply (cancel_mono (kernel.ι k)).1
      simp [kernelCompositionShortComplex, kernelFactorizationShortComplex,
        kernelCokernelCompSequence.snakeInput])
    (by
      apply (cancel_mono (kernel.ι g)).1
      simp [kernelCompositionShortComplex, kernelFactorizationShortComplex,
        kernelCokernelCompSequence.snakeInput])

lemma kernelFactorizationShortComplex_shortExact [Epi f] :
    (kernelFactorizationShortComplex f g k hk).ShortExact :=
  ShortComplex.shortExact_of_iso (kernelCompositionFactorizationIso f g k hk)
    (kernelCompositionShortComplex_shortExact f g)

variable {E : Type*} [Category* E] [Abelian E]
  (F : C ⥤ E) [F.Additive] [PreservesLimitsOfShape WalkingParallelPair F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Kernel-preserving functors identify the actual sequence with that of the mapped
restriction maps. This does not require them to preserve epimorphisms in general. -/
def kernelFactorizationShortComplexMapIso :
    (kernelFactorizationShortComplex f g k hk).map F ≅
      kernelFactorizationShortComplex (F.map f) (F.map g) (F.map k)
        (by rw [← F.map_comp, hk]) :=
  ShortComplex.isoMk (PreservesKernel.iso F f) (PreservesKernel.iso F k)
    (PreservesKernel.iso F g)
    (by
      apply (cancel_mono (kernel.ι (F.map k))).1
      dsimp [kernelFactorizationShortComplex]
      simp only [Category.assoc, kernel.map, kernel.lift_ι, PreservesKernel.iso_hom,
        kernelComparison_comp_ι, Category.comp_id, ← F.map_comp])
    (by
      apply (cancel_mono (kernel.ι (F.map g))).1
      dsimp [kernelFactorizationShortComplex]
      simp only [Category.assoc, kernel.map, kernel.lift_ι, PreservesKernel.iso_hom,
        kernelComparison_comp_ι_assoc, kernelComparison_comp_ι, ← F.map_comp])

/-- A kernel-preserving functor preserves this particular short exact sequence
whenever the image of its first restriction map is epi. -/
lemma kernelFactorizationShortComplex_map_shortExact [Epi (F.map f)] :
    ((kernelFactorizationShortComplex f g k hk).map F).ShortExact :=
  ShortComplex.shortExact_of_iso (kernelFactorizationShortComplexMapIso f g k hk F).symm
    (kernelFactorizationShortComplex_shortExact (F.map f) (F.map g) (F.map k) _)

end CategoryTheory
