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

public import FormalConjecturesForMathlib.AlgebraicTopology.NestedSheafSupportOnOpen
public import FormalConjecturesForMathlib.AlgebraicTopology.FlasqueSheafSupportComparison

/-!
# Vanishing through an actual finite closed-support filtration

The localization sequence for two nested supports is short exact on every
open for termwise-flasque coefficients. A finite filtration ending in the
empty support therefore propagates cohomological vanishing from its actual
open layers to the whole support. Layer vanishing is an explicit hypothesis
of this general lemma, not an asserted purity or dimension theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction to the whole space is an isomorphism on each actual open-set
section group. -/
theorem toOpenRestrictionPushforward_top_app_isIso
    (F : Sheaf AddCommGrpCat.{u} X) (W : Opens X) :
    IsIso (((toOpenRestrictionPushforward X ⊤).app F).hom.app (op W)) := by
  have hw : openRestrictionImage X ⊤ W = W := by
    simpa only [inf_top_eq] using Opens.functor_map_eq_inf (⊤ : Opens X) W
  have heq : (((toOpenRestrictionPushforward X ⊤).app F).hom.app (op W)) =
      F.obj.map (eqToHom (congrArg op hw.symm)) := by
    change F.obj.map _ = F.obj.map _
    congr 1
  rw [heq]
  infer_instance

/-- The actual whole-space restriction morphism is an isomorphism of sheaves. -/
theorem toOpenRestrictionPushforward_top_isIso (F : Sheaf AddCommGrpCat.{u} X) :
    IsIso ((toOpenRestrictionPushforward X ⊤).app F) := by
  let : ∀ W, IsIso (((toOpenRestrictionPushforward X ⊤).app F).hom.app W) :=
    fun W => toOpenRestrictionPushforward_top_app_isIso X F W.unop
  let : IsIso ((toOpenRestrictionPushforward X ⊤).app F).hom :=
    NatIso.isIso_of_isIso_app _
  let : IsIso ((forget AddCommGrpCat.{u} X).map
      ((toOpenRestrictionPushforward X ⊤).app F)) := by
    change IsIso ((toOpenRestrictionPushforward X ⊤).app F).hom
    infer_instance
  exact isIso_of_reflects_iso ((toOpenRestrictionPushforward X ⊤).app F)
    (forget AddCommGrpCat.{u} X)

/-- The actual kernel defining sections with empty support is zero. -/
theorem isZero_sheafSectionsSupportedOutside_top (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero ((sheafSectionsSupportedOutside X ⊤).obj F) := by
  let := toOpenRestrictionPushforward_top_isIso X F
  exact isZero_kernel_of_mono ((toOpenRestrictionPushforward X ⊤).app F)

/-- In particular the empty supported-section complex has zero cohomology,
without any acyclicity or boundedness assumption on its coefficients. -/
theorem supportedSections_top_homology_isZero (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) :
    IsZero ((((supportEvaluation X W).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X ⊤).mapHomologicalComplex (.up ℤ)).obj K)).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((supportEvaluation X W).map_isZero
      (isZero_sheafSectionsSupportedOutside_top X (K.X n)))

variable {U V : Opens X} (h : V ≤ U)

/-- Flasqueness suffices for the nested-support sequence to be short exact
on every open. Injectivity is not required. -/
theorem nestedSupportRestrictionSectionsShortComplex_shortExact_of_flasque
    (W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    ((nestedSupportRestrictionShortComplex X h F).map (supportEvaluation X W)).ShortExact := by
  rw [nestedSupportRestrictionShortComplex_eq]
  let : Epi ((supportEvaluation X W).map ((toOpenRestrictionPushforward X U).app F)) :=
    toOpenRestrictionPushforward_app_epi X U F W
  exact kernelFactorizationShortComplex_map_shortExact _ _ _ _ _

/-- The same exact sequence for actual section complexes of flasque sheaves. -/
theorem nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
    (W : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let := hK n
  exact nestedSupportRestrictionSectionsShortComplex_shortExact_of_flasque X h W (K.X n)

include h in
/-- Vanishing of the smaller support and the actual open layer implies
vanishing of the larger support in the same degree. -/
theorem nestedSupportRestriction_middle_homology_isZero
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hsmall : IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj K)).homology n))
    (hlayer : IsZero ((((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)).homology n)) :
    IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)).homology n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X h ⊤ K hK
  have hlast : IsZero (S.X₃.homology n) := hlayer.of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (nestedSupportRestrictionLastComplexIso X h K))
  exact (hS.homology_exact₂ n).isZero_X₂
    (hsmall.eq_zero_of_src _) (hlast.eq_zero_of_tgt _)

/-- A finite increasing sequence of open complements, terminating at the
whole space, gives vanishing on every corresponding closed support once the
actual open layers vanish. The induction uses only the proved localization
sequence; the layer hypotheses still have to be discharged geometrically. -/
theorem finiteNestedSupport_homology_isZero
    (O : ℕ → Opens X) (hO : Monotone O) (N : ℕ) (hN : O N = ⊤)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ)
    (hlayer : ∀ k, k < N → IsZero
      ((((supportEvaluation X (O (k + 1))).mapHomologicalComplex (.up ℤ)).obj
        (((sheafSectionsSupportedOutside X (O k)).mapHomologicalComplex (.up ℤ)).obj K)).homology n))
    (k : ℕ) (hk : k ≤ N) :
    IsZero ((((supportEvaluation X ⊤).mapHomologicalComplex (.up ℤ)).obj
      (((sheafSectionsSupportedOutside X (O k)).mapHomologicalComplex (.up ℤ)).obj K)).homology n) := by
  induction hk using Nat.decreasingInduction with
  | self =>
      rw [hN]
      exact supportedSections_top_homology_isZero X ⊤ K n
  | of_succ k hk ih =>
      exact nestedSupportRestriction_middle_homology_isZero X
        (hO (Nat.le_succ k)) K hK n ih (hlayer k (by omega))

end TopCat.Sheaf
