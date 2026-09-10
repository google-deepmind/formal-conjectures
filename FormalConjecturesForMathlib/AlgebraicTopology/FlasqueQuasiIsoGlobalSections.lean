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
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Global sections and quasi-isomorphisms of flasque complexes

This file upgrades the exact-complex result in `BoundedBelowFlasqueComplex` to morphisms.  A
quasi-isomorphism between bounded-below complexes of flasque sheaves remains a quasi-isomorphism
after taking global sections.  The proof applies the exact-complex theorem to the mapping cone.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated

universe u

namespace TopCat.Presheaf.IsFlasque

variable {X : TopCat.{u}}

/-- Flasqueness is invariant under isomorphism. -/
lemma of_iso {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (e : F ≅ G) [G.IsFlasque] :
    F.IsFlasque where
  epi {U V} i := by
    let : IsIso (e.hom.app U) := by infer_instance
    let : IsIso (e.inv.app V) := by infer_instance
    have hmap : F.map i =
        e.hom.app U ≫ G.map i ≫ e.inv.app V := by
      apply (cancel_mono (e.hom.app V)).1
      simpa only [Category.assoc, e.inv_hom_id_app, Category.comp_id] using
        e.hom.naturality i
    rw [hmap]
    infer_instance

set_option linter.style.haveILetI false in
/-- A binary biproduct of flasque presheaves is flasque. -/
lemma biprod (F G : TopCat.Presheaf AddCommGrpCat.{u} X) [F.IsFlasque] [G.IsFlasque] :
    (F ⊞ G).IsFlasque where
  epi {U V} i := by
    let evalU := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U
    let evalV := (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj V
    let : evalU.PreservesZeroMorphisms := evalU.preservesZeroMorphisms_of_additive
    let : evalV.PreservesZeroMorphisms := evalV.preservesZeroMorphisms_of_additive
    let : PreservesLimit (pair F G) evalU := by
      letI : PreservesLimitsOfShape (Discrete WalkingPair) evalU := by infer_instance
      exact PreservesLimitsOfShape.preservesLimit
    let : PreservesLimit (pair F G) evalV := by
      letI : PreservesLimitsOfShape (Discrete WalkingPair) evalV := by infer_instance
      exact PreservesLimitsOfShape.preservesLimit
    let : PreservesBinaryBiproduct F G evalU :=
      preservesBinaryBiproduct_of_preservesBinaryProduct _
    let : PreservesBinaryBiproduct F G evalV :=
      preservesBinaryBiproduct_of_preservesBinaryProduct _
    let eU := evalU.mapBiprod F G
    let eV := evalV.mapBiprod F G
    let pF : (F ⊞ G) ⟶ F := Limits.biprod.fst
    let pG : (F ⊞ G) ⟶ G := Limits.biprod.snd
    have hmap : (F ⊞ G).map i =
        eU.hom ≫ Limits.biprod.map (F.map i) (G.map i) ≫ eV.inv := by
      apply (cancel_mono eV.hom).1
      simp only [Category.assoc, eV.inv_hom_id]
      apply Limits.biprod.hom_ext
      · calc
          ((F ⊞ G).map i ≫ eV.hom) ≫ Limits.biprod.fst =
              (F ⊞ G).map i ≫ pF.app V := by
                dsimp [eV, pF]
                rw [Functor.mapBiprod_hom, Category.assoc, Limits.biprod.lift_fst]
                rfl
          _ = pF.app U ≫ F.map i := pF.naturality i
          _ = (eU.hom ≫ Limits.biprod.map (F.map i) (G.map i)) ≫
              Limits.biprod.fst := by
                dsimp [eU, pF]
                rw [Functor.mapBiprod_hom, Category.assoc, Limits.biprod.map_fst,
                  Limits.biprod.lift_fst_assoc]
                rfl
      · calc
          ((F ⊞ G).map i ≫ eV.hom) ≫ Limits.biprod.snd =
              (F ⊞ G).map i ≫ pG.app V := by
                dsimp [eV, pG]
                rw [Functor.mapBiprod_hom, Category.assoc, Limits.biprod.lift_snd]
                rfl
          _ = pG.app U ≫ G.map i := pG.naturality i
          _ = (eU.hom ≫ Limits.biprod.map (F.map i) (G.map i)) ≫
              Limits.biprod.snd := by
                dsimp [eU, pG]
                rw [Functor.mapBiprod_hom, Category.assoc, Limits.biprod.map_snd,
                  Limits.biprod.lift_snd_assoc]
                rfl
    rw [hmap]
    infer_instance

end TopCat.Presheaf.IsFlasque

namespace TopCat.Sheaf.IsFlasque

variable {X : TopCat.{u}}

set_option linter.style.haveILetI false in
/-- Flasqueness of sheaves is invariant under isomorphism. -/
lemma of_iso {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (e : F ≅ G)
    [hG : G.IsFlasque] :
    F.IsFlasque := by
  change TopCat.Presheaf.IsFlasque F.obj
  letI : TopCat.Presheaf.IsFlasque G.obj := hG
  exact TopCat.Presheaf.IsFlasque.of_iso (G := G.obj)
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapIso e)

set_option linter.style.haveILetI false in
/-- A binary biproduct of flasque sheaves is flasque. -/
lemma biprod (F G : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] [hG : G.IsFlasque] :
    (F ⊞ G).IsFlasque := by
  change TopCat.Presheaf.IsFlasque
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).obj (F ⊞ G))
  letI : TopCat.Presheaf.IsFlasque F.obj := hF
  letI : TopCat.Presheaf.IsFlasque G.obj := hG
  letI : TopCat.Presheaf.IsFlasque (F.obj ⊞ G.obj) :=
    TopCat.Presheaf.IsFlasque.biprod F.obj G.obj
  let forget := TopCat.Sheaf.forget AddCommGrpCat.{u} X
  let : PreservesBinaryBiproduct F G forget :=
    preservesBinaryBiproduct_of_preservesBinaryProduct forget
  exact TopCat.Presheaf.IsFlasque.of_iso (G := F.obj ⊞ G.obj) (forget.mapBiprod F G)

namespace BoundedBelowComplex

/-- The mapping cone of a quasi-isomorphism is acyclic. -/
lemma mappingCone_acyclic_of_quasiIso
    {C : Type u} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  apply ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).mp
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  change HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
  infer_instance

/-- A morphism whose mapping cone is acyclic is a quasi-isomorphism. -/
lemma quasiIso_of_mappingCone_acyclic
    {C : Type u} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (h : (CochainComplex.mappingCone f).Acyclic) : QuasiIso f := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  apply ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).mpr
  change (HomotopyCategory.subcategoryAcyclic C)
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone f))
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact h

/-- Acyclicity is invariant under isomorphism of cochain complexes. -/
lemma acyclic_of_iso
    {C : Type u} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (h : K.Acyclic) (e : K ≅ L) : L.Acyclic :=
  fun i => (h i).of_iso e

variable {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ}

/-- Every term of the mapping cone of a map between termwise-flasque complexes is flasque. -/
lemma mappingCone_term_isFlasque (f : K ⟶ L)
    (hK : ∀ i, (K.X i).IsFlasque) (hL : ∀ i, (L.X i).IsFlasque) (i : ℤ) :
    ((CochainComplex.mappingCone f).X i).IsFlasque := by
  let : (K.X (i + 1)).IsFlasque := hK (i + 1)
  let : (L.X i).IsFlasque := hL i
  let : (K.X (i + 1) ⊞ L.X i).IsFlasque := biprod _ _
  exact of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl)

/-- A quasi-isomorphism between bounded-below termwise-flasque complexes remains a
quasi-isomorphism after taking global sections. -/
theorem globalSectionsComplex_map_quasiIso (f : K ⟶ L) [QuasiIso f]
    (nK nL : ℤ) [K.IsStrictlyGE nK] [L.IsStrictlyGE nL]
    (hK : ∀ i, (K.X i).IsFlasque) (hL : ∀ i, (L.X i).IsFlasque) :
    QuasiIso
      (((globalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let M := CochainComplex.mappingCone f
  let n := min nK nL - 1
  let : M.IsStrictlyGE n := by
    dsimp [M, n]
    exact CochainComplex.isStrictlyGE_mappingCone f nK nL (min nK nL - 1)
      (by lia) (by lia)
  have hM : M.Acyclic := by
    dsimp [M]
    exact mappingCone_acyclic_of_quasiIso f
  have hMflasque : ∀ i, (M.X i).IsFlasque := by
    intro i
    dsimp [M]
    exact mappingCone_term_isFlasque f hK hL i
  have hglobal : (globalSectionsComplex M).Acyclic :=
    globalSectionsComplex_acyclic M n hM hMflasque
  let F := globalSectionsFunctor X
  have hcone :
      (CochainComplex.mappingCone
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)).Acyclic :=
    acyclic_of_iso hglobal (CochainComplex.mappingCone.mapHomologicalComplexIso f F)
  exact quasiIso_of_mappingCone_acyclic _ hcone

end BoundedBelowComplex
end TopCat.Sheaf.IsFlasque
