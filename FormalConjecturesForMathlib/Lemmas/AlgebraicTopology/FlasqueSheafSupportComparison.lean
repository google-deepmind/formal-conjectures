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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.CohomologySheafStalkVanishing
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenSheafRestriction
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.ShortExactQuasiIso

/-!
# Local sections of flasque resolution comparisons

A quasi-isomorphism of bounded-below termwise-flasque complexes remains a
quasi-isomorphism on every open set. The proof restricts to that open set and
uses the proved flasque global-sections theorem. Consequently its direct image
under any continuous map is a sheaf quasi-isomorphism. This is a theorem about
flasque models, not an assertion that arbitrary direct image is exact.

The localization sequence is short exact on every open set for flasque
coefficients, so the actual supported-sections complex computes the fiber of
restriction even for the singular-cochain flasque model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Global sections after open restriction are actual sections on the ambient
open set, via the canonical equality of the image of the top open with `U`. -/
def openRestrictionGlobalSectionsIso :
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⋙
        IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of U) ≅
      supportEvaluation X U :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U)))) (fun {_ _} f =>
      (f.hom.naturality (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)))).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Open-set sections preserve quasi-isomorphisms between bounded-below
termwise-flasque complexes. All acyclicity is proved from flasqueness. -/
theorem supportEvaluation_map_quasiIso_of_flasque
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) [QuasiIso f]
    (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ n, (K.X n).IsFlasque) (hL : ∀ n, (L.X n).IsFlasque) :
    QuasiIso (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).map f) := by
  let R := U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  let Γ := IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of U)
  let K' : CochainComplex (Sheaf AddCommGrpCat.{u} (TopCat.of U)) ℤ :=
    (R.mapHomologicalComplex (.up ℤ)).obj K
  let L' : CochainComplex (Sheaf AddCommGrpCat.{u} (TopCat.of U)) ℤ :=
    (R.mapHomologicalComplex (.up ℤ)).obj L
  let f' : K' ⟶ L' := (R.mapHomologicalComplex (.up ℤ)).map f
  let : QuasiIso f' := openSheafRestriction_map_quasiIso X U f
  let : K'.IsStrictlyGE nK := by dsimp [K']; infer_instance
  let : L'.IsStrictlyGE nL := by dsimp [L']; infer_instance
  have hK' (n : ℤ) : (K'.X n).IsFlasque := by
    let : (K.X n).IsFlasque := hK n
    exact openSheafRestriction_isFlasque X U _
  have hL' (n : ℤ) : (L'.X n).IsFlasque := by
    let : (L.X n).IsFlasque := hL n
    exact openSheafRestriction_isFlasque X U _
  let : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map f') :=
    IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso f' nK nL hK' hL'
  let e := NatIso.mapHomologicalComplex (openRestrictionGlobalSectionsIso X U) (.up ℤ)
  apply (quasiIso_iff_of_arrow_mk_iso ((Γ.mapHomologicalComplex (.up ℤ)).map f')
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).map f)
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)).mp
  infer_instance

/-- Direct image preserves quasi-isomorphisms of bounded-below flasque models.
The conclusion is detected by actual sections on preimages of ambient opens. -/
theorem pushforward_map_quasiIso_of_flasque
    {Y : TopCat.{u}} (j : X ⟶ Y)
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) [QuasiIso f]
    (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ n, (K.X n).IsFlasque) (hL : ∀ n, (L.X n).IsFlasque) :
    QuasiIso (((pushforward AddCommGrpCat.{u} j).mapHomologicalComplex (.up ℤ)).map f) := by
  apply quasiIso_of_cofinal_section_quasiIso
  exact fun y V hyV => ⟨V, le_rfl, hyV,
    supportEvaluation_map_quasiIso_of_flasque X ((Opens.map j).obj V) f nK nL hK hL⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual supported-sections localization sequence is short exact for a
flasque coefficient sheaf, without an injectivity assumption. -/
lemma supportRestrictionShortComplex_shortExact_of_flasque
    (F : Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (supportRestrictionShortComplex X U F).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι _))
  epi_g := inferInstanceAs (Epi ((toOpenRestrictionPushforward X U).app F))

/-- The flasque localization sequence is short exact on each open set. -/
lemma supportRestrictionSectionsShortComplex_shortExact_of_flasque (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (supportRestrictionSectionsShortComplex X U V F).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  mono_f := mono_of_isLimit_fork
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  epi_g := toOpenRestrictionPushforward_app_epi X U F V

/-- Termwise flasqueness is sufficient for the actual localization sequence
of section complexes to be short exact. -/
lemma supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque
    (V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) :
    (supportRestrictionSectionsComplexShortComplex X U V K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let := hK n
  exact supportRestrictionSectionsShortComplex_shortExact_of_flasque X U V (K.X n)

/-- The canonical inclusion into the restriction fiber is a quasi-isomorphism
for actual flasque coefficient complexes. -/
lemma supportRestrictionToFiber_quasiIso_of_flasque
    (V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    (hK : ∀ n, (K.X n).IsFlasque) :
    QuasiIso (supportRestrictionToFiber X U V K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)

/-- A coefficient-complex map induces the actual map of localization sequences. -/
def supportRestrictionComplexShortComplexMap
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) :
    supportRestrictionComplexShortComplex X U K ⟶
      supportRestrictionComplexShortComplex X U L where
  τ₁ := ((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).map f
  τ₂ := f
  τ₃ := ((openRestrictionPushforward X U).mapHomologicalComplex (.up ℤ)).map f
  comm₁₂ := by
    ext n
    exact (sheafSectionsSupportedOutsideInclusion X U).naturality (f.f n)
  comm₂₃ := by
    ext n
    exact (toOpenRestrictionPushforward X U).naturality (f.f n)

/-- Supported sections of a quasi-isomorphism between bounded-below flasque
models are a quasi-isomorphism on every open set. This is a proved acyclicity
statement for these models, not exactness of supported sections in general. -/
theorem supportedSections_map_quasiIso_of_flasque
    (V : Opens X) {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f] (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ n, (K.X n).IsFlasque) (hL : ∀ n, (L.X n).IsFlasque) :
    QuasiIso (((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).map
      (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).map f)) := by
  let φ := (((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).mapShortComplex).map
    (supportRestrictionComplexShortComplexMap X U f)
  have h₂ : QuasiIso φ.τ₂ :=
    supportEvaluation_map_quasiIso_of_flasque X V f nK nL hK hL
  have h₃ : QuasiIso φ.τ₃ := by
    change QuasiIso (((supportEvaluation X
      (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))).mapHomologicalComplex
        (.up ℤ)).map f)
    exact supportEvaluation_map_quasiIso_of_flasque X _ f nK nL hK hL
  exact CochainComplex.quasiIso_first_of_shortExact φ
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)
    (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V L hL)

/-- Termwise supported sections preserve quasi-isomorphisms between bounded-below
flasque models, as detected by their actual section complexes. -/
theorem sheafSectionsSupportedOutside_map_quasiIso_of_flasque
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f] (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ n, (K.X n).IsFlasque) (hL : ∀ n, (L.X n).IsFlasque) :
    QuasiIso (((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).map f) := by
  apply quasiIso_of_cofinal_section_quasiIso
  exact fun x V hxV =>
    ⟨V, le_rfl, hxV, supportedSections_map_quasiIso_of_flasque X U V f nK nL hK hL⟩

end TopCat.Sheaf
