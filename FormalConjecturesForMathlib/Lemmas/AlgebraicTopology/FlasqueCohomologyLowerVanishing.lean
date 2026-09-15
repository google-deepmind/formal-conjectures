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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.BoundedBelowFlasqueComplex
/-!
# Global lower-degree vanishing for flasque coefficient complexes

If a bounded-below termwise-flasque sheaf complex is exact through degree `M`,
its global section complex is exact through the same degree. Only the stated
initial range is used; exactness in higher degrees is not assumed.

The proof inductively establishes flasqueness of the cycle sheaves in that
range and then applies the actual short exact cycles sequence. This is the
globalization step for supported semipurity, without assuming a spectral
sequence or an exact global-sections functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex

universe u

namespace TopCat.Sheaf.IsFlasque.BoundedBelowComplex

variable {X : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Cycle sheaves are flasque in the initial exact range. -/
lemma cycles_isFlasque_add_nat_of_exact_le (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → K.ExactAt i) (hflasque : ∀ i, (K.X i).IsFlasque)
    (m : ℕ) (hm : N + (m : ℤ) ≤ M) :
    (K.cycles (N + (m : ℤ))).IsFlasque := by
  induction m with
  | zero =>
      let S := cyclesShortComplex K (N - 1)
      have hS : S.ShortExact := by
        apply cyclesShortComplex_shortExact
        simpa only [sub_add_cancel] using hK N (by simpa using hm)
      have hsource : IsZero S.X₂ := K.isZero_of_isStrictlyGE N (N - 1) (by omega)
      let : Epi S.g := hS.epi_g
      have hzero : IsZero (K.cycles N) := by
        simpa only [S, cyclesShortComplex, sub_add_cancel] using IsZero.of_epi S.g hsource
      simpa using of_isZero (K.cycles N) hzero
  | succ m ih =>
      let i : ℤ := N + (m : ℤ)
      let S := cyclesShortComplex K i
      have hS : S.ShortExact :=
        cyclesShortComplex_shortExact K i (hK (i + 1) (by dsimp [i]; omega))
      let : S.X₁.IsFlasque := ih (by omega)
      let : S.X₂.IsFlasque := hflasque i
      have htarget : S.X₃.IsFlasque := of_shortExact_of_isFlasque₁₂ hS
      simpa only [Nat.cast_succ, i, S, cyclesShortComplex, add_assoc] using htarget

/-- All cycle sheaves through the specified exactness bound are flasque,
including those below the strict starting degree, which are zero. -/
lemma cycles_isFlasque_of_exact_le (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → K.ExactAt i) (hflasque : ∀ i, (K.X i).IsFlasque)
    (i : ℤ) (hi : i ≤ M) : (K.cycles i).IsFlasque := by
  by_cases hiN : i < N
  · exact of_isZero _ (IsZero.of_mono (K.iCycles i) (K.isZero_of_isStrictlyGE N i hiN))
  · let m := (i - N).toNat
    have hm : i = N + (m : ℤ) := by
      dsimp [m]
      omega
    rw [hm]
    exact cycles_isFlasque_add_nat_of_exact_le K N M hK hflasque m (by omega)

/-- At one exact degree, global sections are exact provided the preceding
cycle sheaf is flasque. -/
lemma globalSectionsComplex_exactAt_of_cycles_isFlasque (i : ℤ)
    (hK : K.ExactAt i) [(K.cycles (i - 1)).IsFlasque] :
    (globalSectionsComplex K).ExactAt i := by
  let F := globalSectionsFunctor X
  let L := globalSectionsComplex K
  let A : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))
  have hA : A.Exact ∧ Mono A.f := by
    refine ⟨A.exact_of_f_is_kernel ?_, ?_⟩
    · simpa only [A] using K.cyclesIsKernel i (i + 1) (by simp)
    · dsimp [A]
      infer_instance
  have hFA : (A.map F).Exact := by
    have hleft := ((Functor.preservesFiniteLimits_tfae F).out 3 1).mp
      (inferInstance : PreservesFiniteLimits F)
    exact (hleft A hA).1
  let Sprev := cyclesShortComplex K (i - 1)
  have hSprev : Sprev.ShortExact := by
    apply cyclesShortComplex_shortExact K (i - 1)
    simpa only [sub_add_cancel] using hK
  let : Sprev.X₁.IsFlasque := inferInstanceAs ((K.cycles (i - 1)).IsFlasque)
  have hepiTop : Epi (Sprev.g.hom.app (op (⊤ : Opens X))) :=
    epi_of_shortExact (U := (⊤ : Opens X)) hSprev
  have hepi : Epi (F.map (K.toCycles (i - 1) i)) := by
    have hi : i - 1 + 1 = i := by omega
    change Epi ((K.toCycles (i - 1) (i - 1 + 1)).hom.app (op (⊤ : Opens X))) at hepiTop
    rw [hi] at hepiTop
    exact hepiTop
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 :=
    (ComplexShape.up ℤ).prev_eq' (ComplexShape.up_mk _ _ (by omega))
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
      comm₂₃ := by dsimp [T, B]; simp }
  let : Epi φ.τ₁ := hepi
  let : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (F.obj (K.X i))))
  let : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (F.obj (K.X (i + 1)))))
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hB
  exact (L.exactAt_iff' (i := i - 1) (j := i) (k := i + 1) hprev hnext).mpr hT

/-- Global sections preserve the entire initial exact range of a bounded-below
termwise-flasque complex. -/
theorem globalSectionsComplex_exactAt_of_exact_le (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → K.ExactAt i) (hflasque : ∀ i, (K.X i).IsFlasque)
    (i : ℤ) (hi : i ≤ M) : (globalSectionsComplex K).ExactAt i := by
  let := cycles_isFlasque_of_exact_le K N M hK hflasque (i - 1) (by omega)
  exact globalSectionsComplex_exactAt_of_cycles_isFlasque K i (hK i hi)

/-- Local sheaf-cohomology vanishing through a degree bound implies global
section-complex cohomology vanishing through the same bound for flasque models. -/
theorem globalSectionsComplex_homology_isZero_of_homology_isZero_le
    (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → IsZero (K.homology i)) (hflasque : ∀ i, (K.X i).IsFlasque)
    (i : ℤ) (hi : i ≤ M) : IsZero ((globalSectionsComplex K).homology i) :=
  (globalSectionsComplex_exactAt_of_exact_le K N M
    (fun j hj => (K.exactAt_iff_isZero_homology j).mpr (hK j hj)) hflasque i hi).isZero_homology

end TopCat.Sheaf.IsFlasque.BoundedBelowComplex
