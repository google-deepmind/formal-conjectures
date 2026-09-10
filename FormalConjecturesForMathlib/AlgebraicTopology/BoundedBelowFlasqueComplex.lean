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

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Global sections of bounded-below exact flasque complexes

An exact bounded-below cochain complex of flasque sheaves remains exact after taking global
sections.  The proof is elementary: starting at the lower bound, the cycle sheaves are flasque
by induction through their short exact sequences.  Global sections are then exact on each of
those sequences.

This is the acyclic-complex lemma needed to compare a bounded-below flasque resolution with a
termwise-injective replacement.  It does not assume or invoke a hypercohomology spectral
sequence.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Sheaf.IsFlasque

universe u

variable {X : TopCat.{u}}

/-- A zero sheaf is flasque. -/
lemma of_isZero (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) : F.IsFlasque where
  epi {U V} i := by
    have hobj : IsZero F.obj :=
      (TopCat.Sheaf.forget AddCommGrpCat X).map_isZero hF
    have hV : IsZero (F.obj.obj V) :=
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj V).map_isZero hobj
    exact hV.epi (F.obj.map i)

namespace BoundedBelowComplex

variable (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The short exact sequence from cycles in degree `i`, through the degree-`i` term, to cycles
in degree `i + 1`. -/
def cyclesShortComplex (i : ℤ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1))]
    simp)

lemma cyclesShortComplex_shortExact (i : ℤ) (hK : K.ExactAt (i + 1)) :
    (cyclesShortComplex K i).ShortExact := by
  let S := cyclesShortComplex K i
  have hkerD := K.cyclesIsKernel i (i + 1) (by simp)
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    Limits.isKernelOfComp (K.iCycles (i + 1)) (K.d i (i + 1)) hkerD
      S.zero (K.toCycles_i i (i + 1))
  have hepi : Epi S.g := by
    dsimp [S, cyclesShortComplex]
    have hnext : (ComplexShape.up ℤ).next (i + 1) = i + 2 :=
      (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk _ _ (by lia))
    have hsc' : (K.sc' i (i + 1) (i + 2)).Exact :=
      (K.exactAt_iff' (i := i) (j := i + 1) (k := i + 2) (by simp) hnext).mp hK
    have hepi' : Epi ((K.sc' i (i + 1) (i + 2)).toCycles) :=
      hsc'.epi_toCycles
    rw [← K.toCycles_cyclesIsoSc'_hom i (i + 1) (i + 2) (by simp) hnext] at hepi'
    let e := K.cyclesIsoSc' i (i + 1) (i + 2) (by simp) hnext
    have hfac : K.toCycles i (i + 1) =
        (K.toCycles i (i + 1) ≫ e.hom) ≫ e.inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    let : Epi (K.toCycles i (i + 1) ≫ e.hom) := hepi'
    rw [hfac]
    infer_instance
  have hmono : Mono S.f := by
    dsimp [S, cyclesShortComplex]
    infer_instance
  exact
    { exact := S.exact_of_f_is_kernel hker
      mono_f := hmono
      epi_g := hepi }

/-- The cycle sheaves in every degree at or above a strict lower bound are flasque. -/
lemma cycles_isFlasque_add_nat (N : ℤ) [K.IsStrictlyGE N]
    (hK : K.Acyclic) (hflasque : ∀ i, (K.X i).IsFlasque) (m : ℕ) :
    (K.cycles (N + (m : ℤ))).IsFlasque := by
  induction m with
  | zero =>
      let S := cyclesShortComplex K (N - 1)
      have hS : S.ShortExact := by
        apply cyclesShortComplex_shortExact K (N - 1)
        simpa only [sub_add_cancel] using hK N
      have hsource : IsZero S.X₂ := by
        dsimp [S, cyclesShortComplex]
        exact K.isZero_of_isStrictlyGE N (N - 1) (by lia)
      let : Epi S.g := hS.epi_g
      have htarget : IsZero S.X₃ := IsZero.of_epi S.g hsource
      have hzero : IsZero (K.cycles N) := by
        simpa only [S, cyclesShortComplex, sub_add_cancel] using htarget
      simpa using of_isZero (K.cycles N) hzero
  | succ m ih =>
      let i : ℤ := N + (m : ℤ)
      let S := cyclesShortComplex K i
      have hS : S.ShortExact := cyclesShortComplex_shortExact K i (hK (i + 1))
      let : S.X₁.IsFlasque := by
        dsimp [S, cyclesShortComplex, i]
        exact ih
      let : S.X₂.IsFlasque := by
        dsimp [S, cyclesShortComplex]
        exact hflasque i
      have htarget : S.X₃.IsFlasque := of_shortExact_of_isFlasque₁₂ hS
      simpa only [Nat.cast_succ, i, S, cyclesShortComplex, add_assoc] using htarget

/-- Every cycle sheaf of an acyclic bounded-below complex of flasque sheaves is flasque. -/
lemma cycles_isFlasque (N : ℤ) [K.IsStrictlyGE N]
    (hK : K.Acyclic) (hflasque : ∀ i, (K.X i).IsFlasque) (i : ℤ) :
    (K.cycles i).IsFlasque := by
  by_cases hi : i < N
  · exact of_isZero _ (IsZero.of_mono (K.iCycles i) (K.isZero_of_isStrictlyGE N i hi))
  · let m : ℕ := (i - N).toNat
    have hm : i = N + (m : ℤ) := by
      dsimp [m]
      rw [Int.toNat_of_nonneg (by lia)]
      lia
    rw [hm]
    exact cycles_isFlasque_add_nat K N hK hflasque m

/-- Evaluation of a sheaf on the top open subset, viewed as a functor. -/
def globalSectionsFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

noncomputable instance globalSectionsFunctor_additive :
    (globalSectionsFunctor X).Additive := by
  constructor
  intro A B f g
  change (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))).map
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (f + g))) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

noncomputable instance globalSectionsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (globalSectionsFunctor X) := by
  let : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))) :=
    inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))

/-- The integer-indexed cochain complex obtained by evaluating a sheaf complex on the top open
subset. -/
def globalSectionsComplex
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Global sections preserve exactness of an acyclic bounded-below complex of flasque sheaves. -/
theorem globalSectionsComplex_acyclic (N : ℤ) [K.IsStrictlyGE N]
    (hK : K.Acyclic) (hflasque : ∀ i, (K.X i).IsFlasque) :
    (globalSectionsComplex K).Acyclic := by
  intro i
  let F := globalSectionsFunctor X
  let L := globalSectionsComplex K
  let A : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))
  have hA : A.Exact ∧ Mono A.f := by
    have hker := K.cyclesIsKernel i (i + 1) (by simp)
    refine ⟨A.exact_of_f_is_kernel ?_, ?_⟩
    · simpa only [A] using hker
    · dsimp [A]
      infer_instance
  have hFA : (A.map F).Exact := by
    have hleft := ((Functor.preservesFiniteLimits_tfae F).out 3 1).mp
      (inferInstance : PreservesFiniteLimits F)
    exact (hleft A hA).1
  let Sprev := cyclesShortComplex K (i - 1)
  have hSprev : Sprev.ShortExact := by
    apply cyclesShortComplex_shortExact K (i - 1)
    simpa only [sub_add_cancel] using hK i
  let : Sprev.X₁.IsFlasque := by
    dsimp [Sprev, cyclesShortComplex]
    exact cycles_isFlasque K N hK hflasque (i - 1)
  have hepiTop : Epi (Sprev.g.hom.app (op (⊤ : Opens X))) :=
    epi_of_shortExact (U := (⊤ : Opens X)) hSprev
  have hepi : Epi (F.map (K.toCycles (i - 1) i)) := by
    change Epi ((K.toCycles (i - 1) i).hom.app (op (⊤ : Opens X)))
    have hi : i - 1 + 1 = i := by lia
    change Epi ((K.toCycles (i - 1) (i - 1 + 1)).hom.app
      (op (⊤ : Opens X))) at hepiTop
    rw [hi] at hepiTop
    exact hepiTop
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk _ _ (by lia))
  have hnext : (ComplexShape.up ℤ).next i = i + 1 :=
    (ComplexShape.up ℤ).next_eq' (ComplexShape.up_mk _ _ rfl)
  let T : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk (F.map (K.d (i - 1) i)) (F.map (K.d i (i + 1))) (by
      rw [← F.map_comp, K.d_comp_d, F.map_zero])
  let B : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk (F.map (K.iCycles i)) (F.map (K.d i (i + 1))) (by
      rw [← F.map_comp, K.iCycles_d, F.map_zero])
  have hB : B.Exact := hFA
  let φ : T ⟶ B :=
    { τ₁ := F.map (K.toCycles (i - 1) i)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [T, B]
        rw [Category.comp_id, ← F.map_comp, K.toCycles_i]
      comm₂₃ := by
        dsimp [T, B]
        simp }
  let : Epi φ.τ₁ := hepi
  let : IsIso φ.τ₂ := by
    change IsIso (𝟙 (F.obj (K.X i)))
    infer_instance
  let : Mono φ.τ₃ := by
    change Mono (𝟙 (F.obj (K.X (i + 1))))
    infer_instance
  apply (L.exactAt_iff' (i := i - 1) (j := i) (k := i + 1) hprev hnext).mpr
  change T.Exact
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hB

end BoundedBelowComplex

end TopCat.Sheaf.IsFlasque
