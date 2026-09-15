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

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Presheaf

import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Degree-zero facts about constant sheaves

This file records elementary facts about constant sheaves on a nonempty topological space. In
particular, sheafification does not identify two different constant global sections, and the
constant-sheaf functor on additive commutative groups is faithful.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace TopCat

variable (X : TopCat.{u})

/-- The constant additive presheaf with value `A`. -/
abbrev constantAddCommGrpPresheaf (A : AddCommGrpCat.{u}) : X.Presheaf AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj A

private lemma constantPresheaf_Γgerm_injective (x : X) (A : AddCommGrpCat.{u}) :
    Function.Injective ((constantAddCommGrpPresheaf X A).Γgerm x) := by
  intro a b h
  obtain ⟨U, hxU, i, j, hij⟩ :=
    (constantAddCommGrpPresheaf X A).germ_eq x (by simp) (by simp) a b h
  simpa using hij

/-- On a nonempty space, the sheafification map for a constant additive presheaf is injective on
global sections. -/
lemma constant_toSheafify_app_top_injective [Nonempty X] (A : AddCommGrpCat.{u}) :
    Function.Injective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (constantAddCommGrpPresheaf X A)).app (op ⊤)) := by
  let x : X := Classical.choice inferInstance
  let P := constantAddCommGrpPresheaf X A
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P
  let Q : X.Presheaf AddCommGrpCat.{u} :=
    CategoryTheory.sheafify (Opens.grothendieckTopology X) P
  let stalk := Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let : IsIso (stalk.map η) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  intro a b h
  change η.app (op ⊤) a = η.app (op ⊤) b at h
  apply constantPresheaf_Γgerm_injective X x A
  apply (ConcreteCategory.bijective_of_isIso (stalk.map η)).1
  change stalk.map η (P.Γgerm x a) = stalk.map η (P.Γgerm x b)
  have hmid : Q.Γgerm x (η.app (op ⊤) a) = Q.Γgerm x (η.app (op ⊤) b) :=
    congrArg (fun s => Q.Γgerm x s) h
  have ha : stalk.map η (P.Γgerm x a) = Q.Γgerm x (η.app (op ⊤) a) := by
    dsimp [stalk, Q, Presheaf.Γgerm]
    convert Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens X) x True.intro η a using 1
    exact Iff.rfl
  have hb : stalk.map η (P.Γgerm x b) = Q.Γgerm x (η.app (op ⊤) b) := by
    dsimp [stalk, Q, Presheaf.Γgerm]
    convert Presheaf.stalkFunctor_map_germ_apply (⊤ : Opens X) x True.intro η b using 1
    exact Iff.rfl
  exact ha.trans (hmid.trans hb.symm)

private lemma exists_constant_local_representation (A : AddCommGrpCat.{u})
    (s : (CategoryTheory.sheafify (Opens.grothendieckTopology X)
      (constantAddCommGrpPresheaf X A)).obj (op ⊤)) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ a : A,
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).map (homOfLE le_top).op s =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).app (op U) a := by
  let J := Opens.grothendieckTopology X
  let P := constantAddCommGrpPresheaf X A
  let Q : X.Presheaf AddCommGrpCat.{u} := CategoryTheory.sheafify J P
  let η := CategoryTheory.toSheafify J P
  let stalk := Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let : IsIso (stalk.map η) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  obtain ⟨t, ht⟩ :=
    (ConcreteCategory.bijective_of_isIso (stalk.map η)).2 (Q.Γgerm x s)
  obtain ⟨U, hxU, a, ha⟩ := P.exists_germ_eq t
  have hgerm : Q.germ U x hxU (η.app (op U) a) = Q.Γgerm x s := by
    rw [← Presheaf.stalkFunctor_map_germ_apply]
    change stalk.map η (P.germ U x hxU a) = Q.Γgerm x s
    rw [ha, ht]
  obtain ⟨V, hxV, iVU, iVtop, hV⟩ :=
    Q.germ_eq (U := U) (V := ⊤) x hxU True.intro (η.app (op U) a) s hgerm
  refine ⟨V, hxV, a, ?_⟩
  calc
    Q.map (homOfLE le_top).op s = Q.map iVtop.op s := by
      rw [Subsingleton.elim (homOfLE le_top) iVtop]
    _ = Q.map iVU.op (η.app (op U) a) := hV.symm
    _ = η.app (op V) (P.map iVU.op a) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, η.naturality]
    _ = η.app (op V) a := rfl

private lemma constant_local_representation_value_unique (A : AddCommGrpCat.{u})
    (s : (CategoryTheory.sheafify (Opens.grothendieckTopology X)
      (constantAddCommGrpPresheaf X A)).obj (op ⊤)) (x : X)
    (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V) (a b : A)
    (ha : (CategoryTheory.sheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).map (homOfLE le_top).op s =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).app (op U) a)
    (hb : (CategoryTheory.sheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).map (homOfLE le_top).op s =
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (constantAddCommGrpPresheaf X A)).app (op V) b) : a = b := by
  let J := Opens.grothendieckTopology X
  let P := constantAddCommGrpPresheaf X A
  let Q : X.Presheaf AddCommGrpCat.{u} := CategoryTheory.sheafify J P
  let η := CategoryTheory.toSheafify J P
  let stalk := Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let : IsIso (stalk.map η) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  have hp : P.germ U x hxU a = P.germ V x hxV b := by
    apply (ConcreteCategory.bijective_of_isIso (stalk.map η)).1
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply]
    change Q.germ U x hxU (η.app (op U) a) = Q.germ V x hxV (η.app (op V) b)
    rw [← ha, ← hb, Q.germ_res_apply, Q.germ_res_apply]
  obtain ⟨W, hxW, iWU, iWV, hW⟩ := P.germ_eq x hxU hxV a b hp
  simpa [P, constantAddCommGrpPresheaf] using hW

/-- On a connected space, every global section of a constant additive sheaf comes from a
constant global section before sheafification. -/
lemma constant_toSheafify_app_top_surjective [ConnectedSpace X] (A : AddCommGrpCat.{u}) :
    Function.Surjective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (constantAddCommGrpPresheaf X A)).app (op ⊤)) := by
  let J := Opens.grothendieckTopology X
  let P := constantAddCommGrpPresheaf X A
  let F := (presheafToSheaf J AddCommGrpCat.{u}).obj P
  let Q : X.Presheaf AddCommGrpCat.{u} := F.obj
  let η := CategoryTheory.toSheafify J P
  intro s
  choose U hxU a ha using fun x => exists_constant_local_representation X A s x
  have hloc : IsLocallyConstant a := (IsLocallyConstant.iff_exists_open a).2 fun x =>
    ⟨U x, (U x).2, hxU x, fun y hy =>
      constant_local_representation_value_unique X A s y (U y) (U x)
        (hxU y) hy (a y) (a x) (ha y) (ha x)⟩
  let x₀ : X := Classical.choice inferInstance
  refine ⟨a x₀, ?_⟩
  apply Presheaf.section_ext F ⊤
  intro y hy
  have hay : a y = a x₀ := hloc.apply_eq_of_preconnectedSpace y x₀
  have hη : Q.map (homOfLE le_top : U y ⟶ ⊤).op (η.app (op ⊤) (a x₀)) =
      η.app (op (U y)) (a x₀) := by
    calc
      Q.map (homOfLE le_top : U y ⟶ ⊤).op (η.app (op ⊤) (a x₀)) =
          η.app (op (U y)) (P.map (homOfLE le_top : U y ⟶ ⊤).op (a x₀)) := by
            rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, η.naturality]
      _ = η.app (op (U y)) (a x₀) := rfl
  have hlocal : Q.map (homOfLE le_top : U y ⟶ ⊤).op (η.app (op ⊤) (a x₀)) =
      Q.map (homOfLE le_top : U y ⟶ ⊤).op s := by
    rw [hη, ha y, hay]
  rw [← Q.germ_res_apply (homOfLE le_top : U y ⟶ ⊤) y (hxU y),
    ← Q.germ_res_apply (homOfLE le_top : U y ⟶ ⊤) y (hxU y), hlocal]

/-- On a connected topological space, the coefficient group is additively equivalent to the
global sections of its constant sheaf. -/
def constantSheafGlobalSectionsAddEquiv [ConnectedSpace X] (A : AddCommGrpCat.{u}) :
    A ≃+ ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj A).obj.obj (op ⊤) :=
  AddEquiv.ofBijective
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (constantAddCommGrpPresheaf X A)).app (op ⊤)).hom
    ⟨constant_toSheafify_app_top_injective X A,
      constant_toSheafify_app_top_surjective X A⟩

@[simp]
lemma constantSheafGlobalSectionsAddEquiv_apply [ConnectedSpace X] (A : AddCommGrpCat.{u})
    (a : A) : constantSheafGlobalSectionsAddEquiv X A a =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (constantAddCommGrpPresheaf X A)).app (op ⊤) a := rfl

/-- On a connected topological space, the constant-sheaf functor on additive commutative groups
is fully faithful. -/
def constantSheafFullyFaithfulOfConnected [ConnectedSpace X] :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).FullyFaithful := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (Limits.isTerminalTop (α := Opens X))
  haveI (A : AddCommGrpCat.{u}) : IsIso (adj.unit.app A) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (constantAddCommGrpPresheaf X A)).app (op ⊤))
    exact ⟨constant_toSheafify_app_top_injective X A,
      constant_toSheafify_app_top_surjective X A⟩
  letI : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  exact adj.fullyFaithfulLOfIsIsoUnit

/-- On a nonempty topological space, the constant-sheaf functor on additive commutative groups is
faithful. -/
instance constantSheaf_faithful_of_nonempty [Nonempty X] :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Faithful where
  map_injective {A B} f g h := by
    let J := Opens.grothendieckTopology X
    let PA := constantAddCommGrpPresheaf X A
    let PB := constantAddCommGrpPresheaf X B
    let cf : PA ⟶ PB := (Functor.const (Opens X)ᵒᵖ).map f
    let cg : PA ⟶ PB := (Functor.const (Opens X)ᵒᵖ).map g
    let ηA := CategoryTheory.toSheafify J PA
    let ηB := CategoryTheory.toSheafify J PB
    change (presheafToSheaf J AddCommGrpCat.{u}).map cf =
      (presheafToSheaf J AddCommGrpCat.{u}).map cg at h
    have hs : CategoryTheory.sheafifyMap J cf = CategoryTheory.sheafifyMap J cg :=
      congrArg (fun k => k.hom) h
    let : Mono (ηB.app (op ⊤)) := ConcreteCategory.mono_of_injective _
      (constant_toSheafify_app_top_injective X B)
    apply (cancel_mono (ηB.app (op ⊤))).1
    change f ≫ ηB.app (op ⊤) = g ≫ ηB.app (op ⊤)
    have hcf := congrArg (fun k => k.app (op ⊤))
      (CategoryTheory.toSheafify_naturality J cf)
    change f ≫ ηB.app (op ⊤) = ηA.app (op ⊤) ≫
      (CategoryTheory.sheafifyMap J cf).app (op ⊤) at hcf
    have hcg := congrArg (fun k => k.app (op ⊤))
      (CategoryTheory.toSheafify_naturality J cg)
    change g ≫ ηB.app (op ⊤) = ηA.app (op ⊤) ≫
      (CategoryTheory.sheafifyMap J cg).app (op ⊤) at hcg
    calc
      f ≫ ηB.app (op ⊤) = ηA.app (op ⊤) ≫
          (CategoryTheory.sheafifyMap J cf).app (op ⊤) := hcf
      _ = ηA.app (op ⊤) ≫ (CategoryTheory.sheafifyMap J cg).app (op ⊤) := by rw [hs]
      _ = g ≫ ηB.app (op ⊤) := hcg.symm

instance constantSheaf_full_of_connected [ConnectedSpace X] :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Full :=
  (constantSheafFullyFaithfulOfConnected X).full

end TopCat
