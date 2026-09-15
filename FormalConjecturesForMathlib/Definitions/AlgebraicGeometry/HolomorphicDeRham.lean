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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.AnalyticDifferentialForms
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothEquidimensional
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Topology.Sheaves.Abelian

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The holomorphic de Rham complex

This file assembles the analytic differential forms constructed from actual manifold derivatives
into a presheaf complex and then sheafifies it degree by degree. Restriction of functions induces
restriction of forms and commutes with the exterior derivative.

Constant complex-valued functions define a canonical morphism from the constant sheaf complex to
the holomorphic de Rham complex. Both complexes are also extended by zero to integer degrees for
use in the derived category. No differential forms, differentials, or comparison maps are supplied
as data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Holomorphic de Rham forms in a fixed degree, as a presheaf of complex vector spaces.

This is the coefficient-aware object.  It is the migration target for the additive presheaf used
by the existing derived comparison below, and keeps the linearity of restriction maps available
for module-valued sheafification. -/
def holomorphicDeRhamModulePresheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X)) where
  obj U := ModuleCat.of ℂ
    (HolomorphicForm X d U p)
  map {U V} i := ModuleCat.ofHom
    (holomorphicFormRestriction X d i p)
  map_id U := by
    ext x
    rw [holomorphicFormRestriction_id]
    rfl
  map_comp i j := by
    ext x
    rw [holomorphicFormRestriction_comp]
    rfl

/-- The legacy additive-group presentation of the holomorphic de Rham presheaf. -/
def holomorphicDeRhamPresheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) where
  obj U := AddCommGrpCat.of
    (HolomorphicForm X d U p)
  map {U V} i := AddCommGrpCat.ofHom
    (holomorphicFormRestriction X d i p).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    change (holomorphicFormRestriction X d (𝟙 U) p).toAddMonoidHom = _
    rw [holomorphicFormRestriction_id]
    rfl
  map_comp i j := by
    apply AddCommGrpCat.hom_ext
    change (holomorphicFormRestriction X d (i ≫ j) p).toAddMonoidHom = _
    rw [holomorphicFormRestriction_comp]
    rfl

/-- Holomorphic differential forms vanish in degrees above the complex dimension, already before
sheafification. -/
private lemma holomorphicDeRhamPresheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamPresheaf X d p) := by
  apply Functor.isZero
  intro U
  let : Subsingleton ((holomorphicDeRhamPresheaf X d p).obj U) :=
    ⟨fun x y => by
      rw [holomorphicForm_eq_zero_of_lt X d U hp x,
        holomorphicForm_eq_zero_of_lt X d U hp y]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The exterior derivative as a morphism of presheaves. -/
def holomorphicDeRhamModuleDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamModulePresheaf X d p ⟶
      holomorphicDeRhamModulePresheaf X d (p + 1) where
  app U := ModuleCat.ofHom <|
    holomorphicFormDifferential X d U p
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    ext x
    exact (holomorphicFormRestriction_differential X d i p x).symm

/-- The legacy additive presentation of the exterior derivative. -/
def holomorphicDeRhamDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamPresheaf X d p ⟶
      holomorphicDeRhamPresheaf X d (p + 1) where
  app U := AddCommGrpCat.ofHom <|
    (holomorphicFormDifferential X d U p).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext x
    exact (holomorphicFormRestriction_differential X d i p x).symm

lemma holomorphicDeRhamDifferential_comp [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamDifferential X d p ≫
      holomorphicDeRhamDifferential X d (p + 1) = 0 :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    holomorphicFormDifferential_squared X d U p x

/-- The holomorphic de Rham complex before forgetting its complex-linear structure. -/
def holomorphicDeRhamModulePresheafComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamModulePresheaf X d)
    (holomorphicDeRhamModuleDifferential X d)
    (fun p => NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext fun x =>
      holomorphicFormDifferential_squared X d U p x)

/-- The holomorphic de Rham complex before sheafification. -/
def holomorphicDeRhamPresheafComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamPresheaf X d)
    (holomorphicDeRhamDifferential X d)
    (holomorphicDeRhamDifferential_comp X d)

@[simp] lemma holomorphicDeRhamPresheafComplex_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (holomorphicDeRhamPresheafComplex X d).d p (p + 1) =
      holomorphicDeRhamDifferential X d p := by
  simp [holomorphicDeRhamPresheafComplex]

/-- The constant presheaf of additive groups with value `ℂ`. -/
def constantComplexAddCommGrpPresheaf :
    TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj
    (AddCommGrpCat.of ℂ)

/-- The constant presheaf with value `ℂ`, retaining its complex-module structure. -/
def constantComplexModulePresheaf :
    TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X)) :=
  (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj
    (ModuleCat.of ℂ ℂ)

/-- Complex-linear constants as holomorphic de Rham forms of degree zero. -/
def constantsToHolomorphicDeRhamModuleZero [SmoothOfRelativeDimension d X.hom] :
    constantComplexModulePresheaf X ⟶
      holomorphicDeRhamModulePresheaf X d 0 where
  app U := ModuleCat.ofHom
    (holomorphicFormOfConstant X d U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (holomorphicFormRestriction_ofConstant X d i c).symm

lemma constantsToHolomorphicDeRhamModuleZero_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamModuleZero X d ≫
      holomorphicDeRhamModuleDifferential X d 0 = 0 :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext fun c =>
    holomorphicFormDifferential_ofConstant X d U c

/-- The complex-linear inclusion of constants in the module-valued de Rham complex. -/
def constantsToHolomorphicDeRhamModulePresheafComplex
    [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀
      (TopCat.Presheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X)))).obj
        (constantComplexModulePresheaf X) ⟶
      holomorphicDeRhamModulePresheafComplex X d :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamModuleZero X d) <| by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      change constantsToHolomorphicDeRhamModuleZero X d ≫
        holomorphicDeRhamModuleDifferential X d 0 = 0
      exact constantsToHolomorphicDeRhamModuleZero_comp_differential X d

/-- Constants as holomorphic de Rham forms of degree zero. -/
def constantsToHolomorphicDeRhamZero [SmoothOfRelativeDimension d X.hom] :
    constantComplexAddCommGrpPresheaf X ⟶
      holomorphicDeRhamPresheaf X d 0 where
  app U := AddCommGrpCat.ofHom
    (holomorphicFormOfConstant X d U).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    ext c
    exact (holomorphicFormRestriction_ofConstant X d i c).symm

/-- On a nonempty open set, distinct complex constants define distinct holomorphic zero-forms. -/
private lemma holomorphicFormOfConstant_injective [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) [Nonempty U.unop] :
    Function.Injective (holomorphicFormOfConstant X d U) := by
  intro c c' hcc'
  have hzero : holomorphicFormOfConstant X d U (c - c') = 0 := by
    rw [map_sub, hcc', sub_self]
  let a : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) 0 :=
    Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) (c - c')
  have ha : a ∈ holomorphicFormRelations X d U 0 := by
    change Submodule.Quotient.mk a = 0 at hzero
    rwa [Submodule.Quotient.mk_eq_zero] at hzero
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel,
    restrictionStableAnalyticKernel] at ha
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at ha
  specialize ha U (𝟙 U)
  rw [formRestriction_id, LinearMap.id_apply] at ha
  let x : U.unop := Classical.arbitrary U.unop
  let e := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x.1
  have hxsource : x.1 ∈ e.source := mem_extChartAt_source x.1
  have hxe : e x.1 ∈ chartSectionDomain X d U x.1 := by
    refine ⟨mem_extChartAt_target x.1, ?_⟩
    change e.symm (e x.1) ∈ U.unop
    rw [e.left_inv hxsource]
    exact x.2
  have heval := (mem_chartEvaluationKernel_iff X d U 0 a).1 ha
    x.1 (e x.1) hxe
  rw [chartEvaluation_ofConstant X d U x.1 (c - c') hxe] at heval
  have hcoeff := congrArg
    (fun f : (Fin d → ℂ) [⋀^Fin 0]→L[ℂ] ℂ ↦ f Fin.elim0) heval
  exact sub_eq_zero.mp (by simpa using hcoeff)

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of complex constants into holomorphic zero-forms is a monomorphism on every
stalk. -/
private lemma constantsToHolomorphicDeRhamZero_stalk_mono
    [SmoothOfRelativeDimension d X.hom] (x : ComplexPoint X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (constantsToHolomorphicDeRhamZero X d)) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro z z' h
  obtain ⟨U, hxU, c, rfl⟩ := (constantComplexAddCommGrpPresheaf X).exists_germ_eq z
  obtain ⟨V, hxV, c', rfl⟩ := (constantComplexAddCommGrpPresheaf X).exists_germ_eq z'
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    (holomorphicDeRhamPresheaf X d 0).germ_eq x hxU hxV
      ((constantsToHolomorphicDeRhamZero X d).app (.op U) c)
      ((constantsToHolomorphicDeRhamZero X d).app (.op V) c') h
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hcc' : c = c' := by
    apply holomorphicFormOfConstant_injective X d (.op W)
    have hc := congrArg (fun k :
        (constantComplexAddCommGrpPresheaf X).obj (.op U) ⟶
          (holomorphicDeRhamPresheaf X d 0).obj (.op W) ↦ k c)
      ((constantsToHolomorphicDeRhamZero X d).naturality iWU.op)
    have hc' := congrArg (fun k :
        (constantComplexAddCommGrpPresheaf X).obj (.op V) ⟶
          (holomorphicDeRhamPresheaf X d 0).obj (.op W) ↦ k c')
      ((constantsToHolomorphicDeRhamZero X d).naturality iWV.op)
    change holomorphicFormOfConstant X d (.op W) c =
      (holomorphicDeRhamPresheaf X d 0).map iWU.op
        ((constantsToHolomorphicDeRhamZero X d).app (.op U) c) at hc
    change holomorphicFormOfConstant X d (.op W) c' =
      (holomorphicDeRhamPresheaf X d 0).map iWV.op
        ((constantsToHolomorphicDeRhamZero X d).app (.op V) c') at hc'
    exact hc.trans (hW.trans hc'.symm)
  subst c'
  rw [← (constantComplexAddCommGrpPresheaf X).germ_res_apply iWU x hxW,
    ← (constantComplexAddCommGrpPresheaf X).germ_res_apply iWV x hxW]
  rfl

lemma constantsToHolomorphicDeRhamZero_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamZero X d ≫
      holomorphicDeRhamDifferential X d 0 = 0 :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun c =>
    holomorphicFormDifferential_ofConstant X d U c

/-- The inclusion of the constant presheaf into the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀
      (TopCat.Presheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexAddCommGrpPresheaf X) ⟶
      holomorphicDeRhamPresheafComplex X d :=
  HomologicalComplex.mkHomFromSingle
    (constantsToHolomorphicDeRhamZero X d) <| by
      intro k hk
      obtain rfl : k = 1 := by simpa using hk.symm
      change constantsToHolomorphicDeRhamZero X d ≫
        (holomorphicDeRhamPresheafComplex X d).d 0 1 = 0
      rw [holomorphicDeRhamPresheafComplex_d]
      exact constantsToHolomorphicDeRhamZero_comp_differential X d

/-- Holomorphic de Rham forms in a fixed degree, after additive sheafification. -/
def holomorphicDeRhamSheaf [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J AddCommGrpCat).obj
    (holomorphicDeRhamPresheaf X d p)

/-- The sheaf of holomorphic `p`-forms is zero for `p` above the complex dimension. -/
lemma holomorphicDeRhamSheaf_isZero_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    IsZero (holomorphicDeRhamSheaf X d p) := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  exact (presheafToSheaf J AddCommGrpCat).map_isZero
    (holomorphicDeRhamPresheaf_isZero_of_lt X d hp)

/-- The sheafified exterior derivative. -/
def holomorphicDeRhamSheafDifferential [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamSheaf X d p ⟶
      holomorphicDeRhamSheaf X d (p + 1) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (holomorphicDeRhamDifferential X d p)

/-- The sheafified holomorphic de Rham complex. -/
def holomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℕ :=
  CochainComplex.of
    (holomorphicDeRhamSheaf X d)
    (holomorphicDeRhamSheafDifferential X d)
    (fun p => by
      let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
      change (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential X d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential X d (p + 1)) = 0
      rw [← Functor.map_comp, holomorphicDeRhamDifferential_comp, Functor.map_zero])

@[simp] lemma holomorphicDeRhamComplex_d [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (holomorphicDeRhamComplex X d).d p (p + 1) =
      holomorphicDeRhamSheafDifferential X d p := by
  simp [holomorphicDeRhamComplex]

/-- A neighborhood-wise primitive for every local kernel section gives exactness on a stalk.
The primitive may be taken after shrinking the original neighborhood. -/
private lemma holomorphicStalkExact_of_locallyPrimitive
    (S : ShortComplex (TopCat.Presheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X))))
    (hlocal : ∀ (x : ComplexPoint X)
      (U : Opens (TopCat.of (ComplexPoint X))) (_hx : x ∈ U)
      (s : S.X₂.obj (.op U)), S.g.app (.op U) s = 0 →
        ∃ (V : Opens (TopCat.of (ComplexPoint X))) (_hxV : x ∈ V)
          (i : V ⟶ U) (t : S.X₁.obj (.op V)),
          S.f.app (.op V) t = S.X₂.map i.op s)
    (x : ComplexPoint X) :
    (S.map (TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := S.X₂.exists_germ_eq z
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g
      (S.X₂.germ U x hxU s) = 0 at hz
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz
  have hz' : S.X₃.germ U x hxU (S.g.app (.op U) s) =
      S.X₃.germ U x hxU 0 := by
    rwa [map_zero]
  obtain ⟨W, hxW, iWU, iWU', hW⟩ :=
    S.X₃.germ_eq x hxU hxU (S.g.app (.op U) s) 0 hz'
  have hWs : S.g.app (.op W) (S.X₂.map iWU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.naturality, ConcreteCategory.comp_apply]
    simpa using hW
  obtain ⟨V, hxV, iVW, t, ht⟩ :=
    hlocal x W hxW (S.X₂.map iWU.op s) hWs
  refine ⟨S.X₁.germ V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f
      (S.X₁.germ V x hxV t) = S.X₂.germ U x hxU s
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    S.X₂.germ_res_apply iVW x hxV, S.X₂.germ_res_apply iWU x hxW]

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise sheafification unit from holomorphic forms to the underlying presheaf of the
holomorphic de Rham sheaf complex. -/
noncomputable def holomorphicDeRhamSheafificationUnit
    [SmoothOfRelativeDimension d X.hom] :
    holomorphicDeRhamPresheafComplex X d ⟶
      (TopCat.Sheaf.forget AddCommGrpCat
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex
          (ComplexShape.up ℕ) |>.obj (holomorphicDeRhamComplex X d) where
  f p := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X d p)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, holomorphicDeRhamPresheafComplex_d,
      holomorphicDeRhamComplex_d]
    dsimp [holomorphicDeRhamSheafDifferential, holomorphicDeRhamSheaf]
    exact (toSheafify_naturality
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      (holomorphicDeRhamDifferential X d i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified holomorphic de Rham complex is exact in every positive degree. -/
private lemma holomorphicDeRhamComplex_exactAt_succ
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    (holomorphicDeRhamComplex X d).ExactAt (p + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := holomorphicDeRhamComplex X d)
    (i := p) (j := p + 1) (k := (p + 1) + 1) (by simp) (by simp)]
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let P := holomorphicDeRhamPresheafComplex X d
  have hP : (P.sc' p (p + 1) ((p + 1) + 1)).map stalk |>.Exact :=
    holomorphicStalkExact_of_locallyPrimitive X
      (P.sc' p (p + 1) ((p + 1) + 1)) (by
        intro y U hyU form hform
        dsimp [P, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor'] at hform ⊢
        rw [holomorphicDeRhamPresheafComplex_d] at hform
        rw [holomorphicDeRhamPresheafComplex_d]
        change holomorphicFormDifferential X d (.op U) (p + 1) form = 0 at hform
        obtain ⟨W, k, θ, hyW, hθ⟩ :=
          exists_local_holomorphicForm_primitive X d (.op U) y hyU p form hform
        exact ⟨W.unop, hyW, k.unop, θ, hθ⟩) x
  let unit := holomorphicDeRhamSheafificationUnit X d
  let stalkUnit := (stalk.mapHomologicalComplex (ComplexShape.up ℕ)).map unit
  let η := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat
    (ComplexShape.up ℕ) p (p + 1) ((p + 1) + 1)).map stalkUnit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d p)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d (p + 1))
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d ((p + 1) + 1))
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

/-- Multiplication by a complex scalar on the presheaf of holomorphic de Rham forms. -/
def scalarHolomorphicDeRhamPresheaf [SmoothOfRelativeDimension d X.hom]
    (p : ℕ) (c : ℂ) :
    holomorphicDeRhamPresheaf X d p ⟶
      holomorphicDeRhamPresheaf X d p where
  app U := AddCommGrpCat.ofHom
    ((c • LinearMap.id : HolomorphicForm X d U p →ₗ[ℂ] _).toAddMonoidHom)
  naturality {U V} i := by
    ext x
    dsimp [holomorphicDeRhamPresheaf] at x ⊢
    change c • holomorphicFormRestriction X d i p x =
      holomorphicFormRestriction X d i p (c • x)
    exact (LinearMap.map_smul _ c x).symm

/-- Scalar multiplication commutes with the exterior derivative. -/
lemma scalarHolomorphicDeRhamPresheaf_d
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ) :
    scalarHolomorphicDeRhamPresheaf X d p c ≫
      holomorphicDeRhamDifferential X d p =
    holomorphicDeRhamDifferential X d p ≫
      scalarHolomorphicDeRhamPresheaf X d (p + 1) c :=
  NatTrans.ext <| funext fun U => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    (holomorphicFormDifferential X d U p).map_smul c x

/-- Multiplication by a complex scalar as an endomorphism of the presheaf de Rham complex. -/
def scalarHolomorphicDeRhamPresheafComplex
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    holomorphicDeRhamPresheafComplex X d ⟶
      holomorphicDeRhamPresheafComplex X d := by
  unfold holomorphicDeRhamPresheafComplex
  exact CochainComplex.ofHom
    (fun p => scalarHolomorphicDeRhamPresheaf X d p c)
    (fun p => by
      simpa [CochainComplex.of_d] using
        scalarHolomorphicDeRhamPresheaf_d X d p c)

/-- Multiplication by a complex scalar as an endomorphism of the sheafified de Rham complex. -/
def scalarHolomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom]
    (c : ℂ) :
    holomorphicDeRhamComplex X d ⟶
      holomorphicDeRhamComplex X d := by
  unfold holomorphicDeRhamComplex
  exact CochainComplex.ofHom
    (fun p =>
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf X d p c))
    (fun p => by
      let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))
      simp only [CochainComplex.of_d]
      change (presheafToSheaf J AddCommGrpCat).map
          (scalarHolomorphicDeRhamPresheaf X d p c) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential X d p) =
        (presheafToSheaf J AddCommGrpCat).map
          (holomorphicDeRhamDifferential X d p) ≫
        (presheafToSheaf J AddCommGrpCat).map
          (scalarHolomorphicDeRhamPresheaf X d (p + 1) c)
      rw [← Functor.map_comp, ← Functor.map_comp,
        scalarHolomorphicDeRhamPresheaf_d])

/-- The constant sheaf with value the additive group of complex numbers. -/
@[implicit_reducible]
def constantComplexSheaf :
    TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℂ)

/-- Scalar multiplication on the constant complex presheaf. -/
def complexScalarPresheaf (c : ℂ) :
    constantComplexAddCommGrpPresheaf X ⟶
      constantComplexAddCommGrpPresheaf X where
  app _ := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom ℂ c)
  naturality {U V} i := by
    ext x
    rfl

/-- Scalar multiplication on the constant complex sheaf. -/
def complexScalarSheaf (c : ℂ) :
    constantComplexSheaf X ⟶ constantComplexSheaf X := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  exact (presheafToSheaf J AddCommGrpCat).map
    (complexScalarPresheaf X c)

/-- Complex conjugation on the constant complex presheaf.

Conjugation is a ring automorphism of `ℂ`, so it acts on the constant complex sheaf exactly the
way a scalar does; unlike a scalar it is only additive over `ℂ`, which is what makes the induced
map on cohomology conjugate-linear rather than linear. -/
def conjConstantComplexPresheaf :
    constantComplexAddCommGrpPresheaf X ⟶
      constantComplexAddCommGrpPresheaf X where
  app _ := AddCommGrpCat.ofHom (starRingEnd ℂ).toAddMonoidHom
  naturality {U V} i := by
    ext x
    rfl

/-- Complex conjugation on the constant complex sheaf. -/
def conjConstantComplexSheaf :
    constantComplexSheaf X ⟶ constantComplexSheaf X := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  exact (presheafToSheaf J AddCommGrpCat).map
    (conjConstantComplexPresheaf X)

/-- The sheafified inclusion of constants as de Rham zero-forms. -/
def constantsToHolomorphicDeRhamZeroSheaf [SmoothOfRelativeDimension d X.hom] :
    constantComplexSheaf X ⟶ holomorphicDeRhamSheaf X d 0 :=
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  (presheafToSheaf J AddCommGrpCat).map
    (constantsToHolomorphicDeRhamZero X d)

lemma constantsToHolomorphicDeRhamZeroSheaf_comp_differential
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamZeroSheaf X d ≫
      holomorphicDeRhamSheafDifferential X d 0 = 0 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToHolomorphicDeRhamZero X d) ≫
    (presheafToSheaf J AddCommGrpCat).map
      (holomorphicDeRhamDifferential X d 0) = 0
  rw [← Functor.map_comp, constantsToHolomorphicDeRhamZero_comp_differential,
    Functor.map_zero]

/-- The augmented holomorphic de Rham short complex before sheafification. -/
noncomputable def constantsToHolomorphicDeRhamPresheafShortComplex
    [SmoothOfRelativeDimension d X.hom] :
    ShortComplex (TopCat.Presheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X))) :=
  ShortComplex.mk (constantsToHolomorphicDeRhamZero X d)
    (holomorphicDeRhamDifferential X d 0)
    (constantsToHolomorphicDeRhamZero_comp_differential X d)

/-- The augmented holomorphic de Rham short complex after sheafification. -/
noncomputable def constantsToHolomorphicDeRhamSheafShortComplex
    [SmoothOfRelativeDimension d X.hom] :
    ShortComplex (TopCat.Sheaf AddCommGrpCat
      (TopCat.of (ComplexPoint X))) :=
  ShortComplex.mk (constantsToHolomorphicDeRhamZeroSheaf X d)
    (holomorphicDeRhamSheafDifferential X d 0)
    (constantsToHolomorphicDeRhamZeroSheaf_comp_differential X d)

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification unit between the augmented presheaf and sheaf short complexes. -/
noncomputable def constantsToHolomorphicDeRhamShortComplexSheafificationUnit
    [SmoothOfRelativeDimension d X.hom] :
    constantsToHolomorphicDeRhamPresheafShortComplex X d ⟶
      (constantsToHolomorphicDeRhamSheafShortComplex X d).map
        (TopCat.Sheaf.forget AddCommGrpCat
          (TopCat.of (ComplexPoint X))) where
  τ₁ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (constantComplexAddCommGrpPresheaf X)
  τ₂ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X d 0)
  τ₃ := toSheafify
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamPresheaf X d 1)
  comm₁₂ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (constantsToHolomorphicDeRhamZero X d)).symm
  comm₂₃ := (toSheafify_naturality
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    (holomorphicDeRhamDifferential X d 0)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The augmented holomorphic de Rham sheaf complex is exact. Thus the kernel of the exterior
derivative on holomorphic functions is exactly the constant sheaf. -/
private lemma constantsToHolomorphicDeRhamSheafShortComplex_exact
    [SmoothOfRelativeDimension d X.hom] :
    (constantsToHolomorphicDeRhamSheafShortComplex X d).Exact := by
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have hP : ((constantsToHolomorphicDeRhamPresheafShortComplex X d).map
      stalk).Exact :=
    holomorphicStalkExact_of_locallyPrimitive X
      (constantsToHolomorphicDeRhamPresheafShortComplex X d) (by
        intro y U hyU form hform
        change holomorphicFormDifferential X d (.op U) 0 form = 0 at hform
        obtain ⟨V, i, c, hyV, hi⟩ :=
          exists_local_holomorphicForm_eq_constant X d (.op U) y hyU form hform
        exact ⟨V.unop, hyV, i.unop, c, hi.symm⟩) x
  let unit := constantsToHolomorphicDeRhamShortComplexSheafificationUnit X d
  let η := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (constantComplexAddCommGrpPresheaf X)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d 0)
  let : IsIso η.τ₃ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d 1)
  let : IsIso η := ShortComplex.isIso_of_isIso η
  exact ShortComplex.exact_of_iso (asIso η) hP

set_option backward.isDefEq.respectTransparency false in
/-- The sheafified inclusion of complex constants into holomorphic functions is a
monomorphism. -/
private lemma constantsToHolomorphicDeRhamZeroSheaf_mono
    [SmoothOfRelativeDimension d X.hom] :
    Mono (constantsToHolomorphicDeRhamZeroSheaf X d) := by
  rw [TopCat.Presheaf.mono_iff_stalk_mono]
  intro x
  let stalk := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let unit := constantsToHolomorphicDeRhamShortComplexSheafificationUnit X d
  let S := (constantsToHolomorphicDeRhamPresheafShortComplex X d).map stalk
  let T := (constantsToHolomorphicDeRhamSheafShortComplex X d).map
    (TopCat.Sheaf.forget AddCommGrpCat
      (TopCat.of (ComplexPoint X)) ⋙ stalk)
  let η : S ⟶ T := (stalk.mapShortComplex).map unit
  let : IsIso η.τ₁ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (constantComplexAddCommGrpPresheaf X)
  let : IsIso η.τ₂ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
      (holomorphicDeRhamPresheaf X d 0)
  let : Mono S.f := constantsToHolomorphicDeRhamZero_stalk_mono X d x
  change Mono T.f
  have h : T.f = inv η.τ₁ ≫ S.f ≫ η.τ₂ := by
    rw [← cancel_epi η.τ₁, η.comm₁₂]
    simp
  rw [h]
  infer_instance

/-- The comparison from the constant sheaf complex to the holomorphic de Rham complex. -/
def constantsToHolomorphicDeRhamComplex [SmoothOfRelativeDimension d X.hom] :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) ⟶
      holomorphicDeRhamComplex X d :=
  (CochainComplex.fromSingle₀Equiv (holomorphicDeRhamComplex X d)
    (constantComplexSheaf X)).symm
      ⟨constantsToHolomorphicDeRhamZeroSheaf X d, by
        rw [holomorphicDeRhamComplex_d]
        exact constantsToHolomorphicDeRhamZeroSheaf_comp_differential X d⟩

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma identifies the degree-zero de Rham cohomology sheaf with the
constant sheaf. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero
    [SmoothOfRelativeDimension d X.hom] :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex X d) 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · exact ⟨constantsToHolomorphicDeRhamSheafShortComplex_exact X d,
      constantsToHolomorphicDeRhamZeroSheaf_mono X d⟩
  all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- The holomorphic Poincaré lemma makes the constant-to-de Rham comparison a
quasi-isomorphism in every positive degree. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex X d) (p + 1) := by
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj (constantComplexSheaf X) p)]
  exact holomorphicDeRhamComplex_exactAt_succ X d p

/-- The constant sheaf resolves the holomorphic de Rham complex in all natural degrees. -/
instance constantsToHolomorphicDeRhamComplex_quasiIso
    [SmoothOfRelativeDimension d X.hom] :
    QuasiIso (constantsToHolomorphicDeRhamComplex X d) where
  quasiIsoAt p := by
    rcases p with _ | p
    · exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_zero X d
    · exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_succ X d p

/-- Scalar multiplication on the constant complex-valued complex concentrated in degree zero. -/
@[implicit_reducible]
def complexScalarComplex (c : ℂ) :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) :=
  (CochainComplex.single₀ _).map (complexScalarSheaf X c)

/-- The constant sheaf complex, extended by zero from natural to integer degrees. -/
@[implicit_reducible]
def constantComplexSheafComplexInt :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
      (constantComplexSheaf X)).extend ComplexShape.embeddingUpNat

/-- Scalar multiplication on the integer-indexed constant complex-valued complex. -/
def complexScalarComplexInt (c : ℂ) :
    constantComplexSheafComplexInt X ⟶
      constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (complexScalarComplex X c)
    ComplexShape.embeddingUpNat

/-- Complex conjugation on the constant complex-valued complex concentrated in degree zero. -/
def conjConstantComplexComplex :
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) ⟶
    (CochainComplex.single₀
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
        (constantComplexSheaf X) :=
  (CochainComplex.single₀ _).map (conjConstantComplexSheaf X)

/-- Complex conjugation on the integer-indexed constant complex-valued complex.

The holomorphic de Rham complex carries no such map: conjugation is not `ℂ`-linear, so it exists
only on the constant-sheaf side of the comparison. -/
def conjConstantComplexSheafComplexInt :
    constantComplexSheafComplexInt X ⟶ constantComplexSheafComplexInt X :=
  HomologicalComplex.extendMap (conjConstantComplexComplex X)
    ComplexShape.embeddingUpNat

/-- The holomorphic de Rham complex, extended by zero to negative degrees. -/
def holomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat ↧(ComplexPoint X)) ℤ :=
  (holomorphicDeRhamComplex X (dim X.left)).extend ComplexShape.embeddingUpNat

/-- The integer-indexed holomorphic de Rham complex vanishes in every degree above the complex
dimension. -/
lemma holomorphicDeRhamComplexInt_isZero_X_of_lt
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) (hn : (dim X.left : ℤ) < n) :
    IsZero ((holomorphicDeRhamComplexInt X).X n) := by
  have hn0 : 0 ≤ n := by lia
  let p := n.toNat
  have hp : (p : ℤ) = n := by
    simp [p, Int.toNat_of_nonneg hn0]
  have hdp : dim X.left < p := by lia
  exact (holomorphicDeRhamSheaf_isZero_of_lt X (dim X.left) hdp).of_iso
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat hp)

/-- The integer-indexed holomorphic de Rham complex is strictly supported in degrees at most the
complex dimension. -/
noncomputable instance holomorphicDeRhamComplexInt_isStrictlyLE
    [IsIntegral X.left] [Smooth X.hom] :
    (holomorphicDeRhamComplexInt X).IsStrictlySupported
      (ComplexShape.embeddingUpIntLE (dim X.left)) where
  isZero n hn := by
    rw [ComplexShape.notMem_range_embeddingUpIntLE_iff] at hn
    exact holomorphicDeRhamComplexInt_isZero_X_of_lt X n hn

/-- Multiplication by a complex scalar on the integer-indexed holomorphic de Rham complex. -/
def scalarHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom]
    (c : ℂ) :
    holomorphicDeRhamComplexInt X ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap
    (scalarHolomorphicDeRhamComplex X (dim X.left) c) ComplexShape.embeddingUpNat

/-- The constant-to-de Rham comparison on integer-indexed complexes. -/
def constantsToHolomorphicDeRhamComplexInt [IsIntegral X.left] [Smooth X.hom] :
    constantComplexSheafComplexInt X ⟶
      holomorphicDeRhamComplexInt X :=
  HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat

/-- Extending by zero gives the holomorphic de Rham quasi-isomorphism in every integer
degree. -/
instance constantsToHolomorphicDeRhamComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (constantsToHolomorphicDeRhamComplexInt X) := by
  change QuasiIso (HomologicalComplex.extendMap
    (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat).2
      inferInstance

end AlgebraicGeometry.ComplexPoint
