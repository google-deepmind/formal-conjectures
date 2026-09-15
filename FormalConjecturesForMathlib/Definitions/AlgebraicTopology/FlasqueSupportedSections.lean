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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.DerivedSheafSupportNaturality
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Supported sections preserve flasqueness

A supported section over `V` glues with zero on the excluded open `U` to a section on
`V ⊔ U`. Flasqueness extends that section to `W ⊔ U` when `V ≤ W`, and its restriction to
`W` vanishes on `W ⊓ U`, so it lies in the kernel defining supported sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)

/-- Restriction-pushforward on an ambient open is literally evaluation on its
intersection with the excluded open. -/
def supportedOutsideIntersectionIso :
    ((openRestrictionPushforward X U).obj F).obj.obj (op V) ≅ F.obj.obj (op (V ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V)))

/-- The preceding identification preserves the actual restriction morphism. -/
@[reassoc]
theorem toOpenRestrictionPushforward_intersection :
    (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) ≫
      (supportedOutsideIntersectionIso X U V F).hom =
        F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The literal supported-section inclusion restricts to zero on the intersection. -/
@[reassoc]
theorem supportedOutsideInclusion_restrict_intersection :
    ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
      F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op = 0 := by
  rw [← toOpenRestrictionPushforward_intersection X U V F, ← Category.assoc]
  have h := congrArg (fun f => f.hom.app (op V))
    (sheafSectionsSupportedOutsideInclusion_restriction X U F)
  change ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
    ((toOpenRestrictionPushforward X U).app F).hom.app (op V) = 0 at h
  rw [h, zero_comp]

/-- Pairwise sheaf gluing extends a supported section by zero across `U`, as an actual
additive morphism from the defining kernel. -/
def supportedOutsideGlueZero :
    ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op (V ⊔ U)) :=
  F.interUnionPullbackConeLift V U
    (PullbackCone.mk
      (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
      (0 : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op U))
      (by rw [supportedOutsideInclusion_restrict_intersection, zero_comp]))

/-- Gluing with zero preserves the given section on its original open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_left :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op =
        ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) :=
  F.interUnionPullbackConeLift_left V U _

/-- The same glued section is exactly zero on the excluded open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_right :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op = 0 :=
  F.interUnionPullbackConeLift_right V U _

/-- A section zero on the intersection lifts into the actual supported-section kernel.
The proof uses its canonical on-open kernel comparison, not a chosen support lift. -/
theorem exists_supportedOutsideSection_of_restrict_eq_zero
    (s : F.obj.obj (op V))
    (hs : F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s = 0) :
    ∃ t : ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V),
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) t = s := by
  let r := ((toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have hr : r s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (supportedOutsideIntersectionIso X U V F).hom).1
    rw [map_zero]
    exact (ConcreteCategory.congr_hom
      (toOpenRestrictionPushforward_intersection X U V F) s).trans hs
  let e := sheafSectionsSupportedOutsideOnOpenIso X U V F ≪≫ AddCommGrpCat.kernelIsoKer r
  let a : r.hom.ker := ⟨s, hr⟩
  refine ⟨e.inv a, ?_⟩
  have he : e.hom ≫ AddCommGrpCat.ofHom r.hom.ker.subtype =
      ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) := by
    simp only [e, Iso.trans_hom, Category.assoc,
      AddCommGrpCat.kernelIsoKer_hom_comp_subtype]
    exact sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F
  rw [← he]
  change (AddCommGrpCat.ofHom r.hom.ker.subtype) (e.hom (e.inv a)) = s
  have hai : e.hom (e.inv a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
  rw [hai]
  rfl

variable {V} {W : Opens X}

/-- Every supported section extends along an open inclusion when the original sheaf
is flasque. The extension is produced by gluing with zero before extending. -/
theorem sheafSectionsSupportedOutside_restriction_surjective [F.IsFlasque]
    (hVW : V ≤ W) :
    Function.Surjective (((sheafSectionsSupportedOutside X U).obj F).obj.map
      (homOfLE hVW).op) := by
  intro a
  let G := (sheafSectionsSupportedOutside X U).obj F
  let ι := (sheafSectionsSupportedOutsideInclusion X U).app F
  have hsup : V ⊔ U ≤ W ⊔ U := sup_le_sup_right hVW U
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE hsup).op)).mp inferInstance
      (supportedOutsideGlueZero X U V F a)
  have htU : F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t = 0 := by
    calc
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (F.obj.map (homOfLE hsup).op t) := by
        rw [← Functor.map_comp_apply]
        rfl
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (supportedOutsideGlueZero X U V F a) := by rw [ht]
      _ = 0 := ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_right X U V F) a
  let b := F.obj.map (homOfLE (le_sup_left : W ≤ W ⊔ U)).op t
  have hb : F.obj.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op b = 0 := by
    calc
      _ = F.obj.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op
          (F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t) := by
        dsimp [b]
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl
      _ = 0 := by rw [htU, map_zero]
  obtain ⟨c, hc⟩ := exists_supportedOutsideSection_of_restrict_eq_zero X U W F b hb
  have hι : Function.Injective (ι.hom.app (op V)) := by
    apply (AddCommGrpCat.mono_iff_injective _).mp
    change Mono (((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F]
    infer_instance
  refine ⟨c, hι ?_⟩
  calc
    ι.hom.app (op V) (G.obj.map (homOfLE hVW).op c) =
        F.obj.map (homOfLE hVW).op (ι.hom.app (op W) c) :=
      ConcreteCategory.congr_hom (ι.hom.naturality (homOfLE hVW).op) c
    _ = F.obj.map (homOfLE hVW).op b := by rw [hc]
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (F.obj.map (homOfLE hsup).op t) := by
      dsimp [b]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (supportedOutsideGlueZero X U V F a) := by rw [ht]
    _ = ι.hom.app (op V) a :=
      ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_left X U V F) a

/-- The actual sheaf-valued supported-sections functor preserves flasque sheaves. -/
instance sheafSectionsSupportedOutside_isFlasque [F.IsFlasque] :
    ((sheafSectionsSupportedOutside X U).obj F).IsFlasque where
  epi {V W} i := by
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (sheafSectionsSupportedOutside_restriction_surjective X U F (leOfHom i.unop))

/-- Equivalently, sections supported in any actual closed subset preserve flasqueness. -/
instance sheafSectionsWithClosedSupport_isFlasque (Z : Closeds X) [F.IsFlasque] :
    ((sheafSectionsWithClosedSupport X Z).obj F).IsFlasque :=
  sheafSectionsSupportedOutside_isFlasque X Z.compl F

end TopCat.Sheaf
