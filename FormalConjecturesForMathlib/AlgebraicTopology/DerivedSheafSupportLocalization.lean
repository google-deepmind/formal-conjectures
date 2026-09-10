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

public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupport
public import FormalConjecturesForMathlib.AlgebraicTopology.InjectiveFlasque
public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.MappingCoconeShortExact

/-!
# The actual localization sequence on injective coefficient complexes

The kernel defining sections supported outside `U` fits into a short exact
sequence with the coefficient sheaf and its restriction-pushforward whenever
the coefficient is injective. Surjectivity is proved using the existing theorem
that injective sheaves are flasque. In particular, it is not an extra certificate.

Evaluation of this sequence on an arbitrary open set is also short exact. This
is stronger than sheaf-level exactness alone: it supplies the actual complex of
supported sections in the localization calculation.

The comparison with the mapping cocone is an explicit quasi-isomorphism,
normalized by its projection to the coefficient complex. The final isomorphisms
start from the actual `D⁺` right-derived functors, using their canonical units on
bounded-below injective models. They are displayed in the ambient derived
category using the full inclusion `D⁺ → D`.

This file does not yet compare restriction of the ambient injective model with
an independently chosen injective resolution on the complement. That normalized
resolution comparison is still needed to identify these fibers with the
repository's separate constant-rational restriction-cone model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- The actual support inclusion followed by restriction-pushforward. -/
def supportRestrictionShortComplex (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((sheafSectionsSupportedOutsideInclusion X U).app F)
    ((toOpenRestrictionPushforward X U).app F)
    (sheafSectionsSupportedOutsideInclusion_restriction X U F)

/-- Restriction of a flasque coefficient sheaf is surjective on every open set. -/
instance toOpenRestrictionPushforward_app_epi (F : Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] (V : Opens X) :
    Epi (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) := by
  change Epi (F.obj.map _)
  infer_instance

instance toOpenRestrictionPushforward_epi (F : Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] : Epi ((toOpenRestrictionPushforward X U).app F) := by
  let : ∀ V, Epi (((toOpenRestrictionPushforward X U).app F).hom.app V) :=
    fun V => toOpenRestrictionPushforward_app_epi X U F V.unop
  have : Epi ((toOpenRestrictionPushforward X U).app F).hom :=
    NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).epi_of_epi_map this

set_option backward.isDefEq.respectTransparency false in
/-- The localization sequence is short exact for an injective coefficient sheaf.
The first map is literally its defining kernel inclusion. -/
lemma supportRestrictionShortComplex_shortExact (F : Sheaf AddCommGrpCat.{u} X)
    [Injective F] : (supportRestrictionShortComplex X U F).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι _))
  epi_g := inferInstanceAs (Epi ((toOpenRestrictionPushforward X U).app F))

/-- Evaluation of an additive sheaf on an ambient open set. -/
def supportEvaluation (V : Opens X) : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op V)

instance (V : Opens X) : (supportEvaluation X V).Additive where
  map_add := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
instance (V : Opens X) :
    PreservesLimitsOfShape WalkingParallelPair (supportEvaluation X V) :=
  comp_preservesLimitsOfShape
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))

/-- The sequence of sections on `V`, with the actual supported-sections inclusion
and actual restriction map. -/
def supportRestrictionSectionsShortComplex (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex AddCommGrpCat.{u} :=
  (supportRestrictionShortComplex X U F).map (supportEvaluation X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on every open set preserves this particular localization sequence
for injective coefficients. This does not assert that evaluation is exact in
general. -/
lemma supportRestrictionSectionsShortComplex_shortExact (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    (supportRestrictionSectionsShortComplex X U V F).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  mono_f := mono_of_isLimit_fork
    (KernelFork.mapIsLimit _ (kernelIsKernel _) (supportEvaluation X V))
  epi_g := toOpenRestrictionPushforward_app_epi X U F V

instance : (openRestrictionPushforward X U).Additive where
  map_add := by intros; rfl

/-- The actual support/restriction sequence applied termwise to a coefficient
complex. No boundedness is needed for this algebraic sequence. -/
def supportRestrictionComplexShortComplex
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :=
  ShortComplex.mk
    (show ((sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj K ⟶ K from
      { f n := (sheafSectionsSupportedOutsideInclusion X U).app (K.X n)
        comm' i j h := ((sheafSectionsSupportedOutsideInclusion X U).naturality (K.d i j)).symm })
    (show K ⟶ ((openRestrictionPushforward X U).mapHomologicalComplex (.up ℤ)).obj K from
      { f n := (toOpenRestrictionPushforward X U).app (K.X n)
        comm' i j h := ((toOpenRestrictionPushforward X U).naturality (K.d i j)).symm })
    (by ext n; exact sheafSectionsSupportedOutsideInclusion_restriction X U (K.X n))

/-- A termwise injective complex gives an actual short exact localization
sequence of complexes of sheaves. -/
lemma supportRestrictionComplexShortComplex_shortExact
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (supportRestrictionComplexShortComplex X U K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportRestrictionShortComplex_shortExact X U (K.X n)

/-- Evaluate the actual termwise support/restriction sequence on `V`. -/
def supportRestrictionSectionsComplexShortComplex (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ) :=
  (supportRestrictionComplexShortComplex X U K).map
    ((supportEvaluation X V).mapHomologicalComplex (.up ℤ))

/-- The support/restriction sequence is short exact even after taking sections
on an arbitrary open set, for a termwise injective coefficient complex. -/
lemma supportRestrictionSectionsComplexShortComplex_shortExact (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (supportRestrictionSectionsComplexShortComplex X U V K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    supportRestrictionSectionsShortComplex_shortExact X U V (K.X n)

/-- Canonical localization comparison to the homotopy fiber of actual
restriction, on a coefficient complex. -/
def supportRestrictionToFiber (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (supportRestrictionSectionsComplexShortComplex X U V K).X₁ ⟶
      CochainComplex.mappingCocone
        (supportRestrictionSectionsComplexShortComplex X U V K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

/-- Injectivity proves that the canonical localization comparison is a
quasi-isomorphism; no duality or acyclicity certificate is supplied. -/
lemma supportRestrictionToFiber_quasiIso (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (supportRestrictionToFiber X U V K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (supportRestrictionSectionsComplexShortComplex_shortExact X U V K)

/-- The localization comparison preserves the actual support-forgetting map,
including its sign. -/
@[reassoc (attr := simp)]
lemma supportRestrictionToFiber_fst (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    supportRestrictionToFiber X U V K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionSectionsComplexShortComplex X U V K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

/-- The analogous canonical localization comparison before global sections. -/
def sheafSupportRestrictionToFiber
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (supportRestrictionComplexShortComplex X U K).X₁ ⟶
      CochainComplex.mappingCocone (supportRestrictionComplexShortComplex X U K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

lemma sheafSupportRestrictionToFiber_quasiIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (sheafSupportRestrictionToFiber X U K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (supportRestrictionComplexShortComplex_shortExact X U K)

@[reassoc (attr := simp)]
lemma sheafSupportRestrictionToFiber_fst
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    sheafSupportRestrictionToFiber X U K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionComplexShortComplex X U K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

local instance derivedSupportLocalizationSheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance derivedSupportLocalizationGroupDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The derived unit identifies the actual `D⁺` supported-sections functor
with its termwise value on a bounded-below injective complex. The displayed
comparison takes values in the ambient derived category via its full inclusion. -/
def derivedClosedSupportInjectiveModelIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedClosedSupportSections X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).X₁ :=
  (DerivedCategory.Plus.ι.mapIso
    (asIso ((derivedClosedSupportSectionsUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I))))).symm ≪≫
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Localization for the actual derived support functor, evaluated on a
bounded-below injective model. The fiber is built from actual restriction, not
an unrelated morphism between isomorphic cohomology groups. -/
def derivedClosedSupportInjectiveFiberIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedClosedSupportSections X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCocone
          (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
            (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
              (.up ℤ)).obj I.obj)).g) := by
  let : ∀ n, Injective
      ((((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
        (.up ℤ)).obj I.obj).X n) := fun n => (I.obj.X n).property
  have := supportRestrictionToFiber_quasiIso X Z.compl ⊤
    (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
      (.up ℤ)).obj I.obj)
  exact derivedClosedSupportInjectiveModelIso X Z I ≪≫
    asIso (DerivedCategory.Q.map (supportRestrictionToFiber X Z.compl ⊤ _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedClosedSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedClosedSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedClosedSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedClosedSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheaf-valued derived unit on a bounded-below injective model. -/
def derivedSheafSupportInjectiveModelIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedSheafSectionsWithClosedSupport X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (supportRestrictionComplexShortComplex X Z.compl
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).X₁ :=
  (DerivedCategory.Plus.ι.mapIso
    (asIso ((derivedSheafSectionsWithClosedSupportUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I))))).symm ≪≫
    (DerivedCategory.quotientCompQhIso (Sheaf AddCommGrpCat.{u} X)).app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheaf-valued localization for the actual derived support functor on a
bounded-below injective model, through the canonical restriction fiber. -/
def derivedSheafSupportInjectiveFiberIso (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    DerivedCategory.Plus.ι.obj
      ((derivedSheafSectionsWithClosedSupport X Z).obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mappingCocone
          (supportRestrictionComplexShortComplex X Z.compl
            (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
              (.up ℤ)).obj I.obj)).g) := by
  let : ∀ n, Injective
      ((((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
        (.up ℤ)).obj I.obj).X n) := fun n => (I.obj.X n).property
  have := sheafSupportRestrictionToFiber_quasiIso X Z.compl
    (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
      (.up ℤ)).obj I.obj)
  exact derivedSheafSupportInjectiveModelIso X Z I ≪≫
    asIso (DerivedCategory.Q.map (sheafSupportRestrictionToFiber X Z.compl _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedSheafSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedSheafSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedSheafSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionComplexShortComplex X Z.compl
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedSheafSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]

end TopCat.Sheaf
