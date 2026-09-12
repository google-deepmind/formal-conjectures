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

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Assembling constant-sheaf maps from locally represented stalk maps

A pointwise family of additive maps from a fixed group to the stalks is not automatically
a sheaf map. This module proves the precise assembly theorem: each value must be locally
represented by a section. Unique sheaf gluing then constructs the map. The stalk formula
retains the specified maps exactly, and isomorphisms on stalks give an actual sheaf
isomorphism. Geometric applications must prove the local representability hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- A locally represented family of stalk elements has a unique global section. -/
theorem existsUnique_section_of_locally_representable
    (g : ∀ x : X, F.presheaf.stalk x)
    (hlocal : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
      ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y) :
    ∃! s : F.presheaf.obj (op ⊤), ∀ x : X, F.presheaf.Γgerm x s = g x := by
  choose U hx s hs using hlocal
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf U s := by
    intro x y
    apply TopCat.Presheaf.section_ext F
    intro z hz
    simp only [F.presheaf.germ_res_apply]
    exact (hs x z hz.1).trans (hs y z hz.2).symm
  obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
    hcover s hcompat
  refine ⟨t, ?_, ?_⟩
  · intro x
    rw [← F.presheaf.Γgerm_res_apply (i := homOfLE (show U x ≤ ⊤ from le_top)) x (hx x),
      ht x]
    exact hs x x (hx x)
  · intro t' ht'
    apply TopCat.Presheaf.section_ext F
    intro x _
    change F.presheaf.Γgerm x t' = F.presheaf.Γgerm x t
    rw [ht' x, ← F.presheaf.Γgerm_res_apply (i := homOfLE (show U x ≤ ⊤ from le_top))
      x (hx x), ht x, hs x x (hx x)]

/-- The uniquely specified global section; choice selects only the unique gluing. -/
def sectionOfLocallyRepresentable
    (g : ∀ x : X, F.presheaf.stalk x)
    (hlocal : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
      ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y) : F.presheaf.obj (op ⊤) :=
  (existsUnique_section_of_locally_representable F g hlocal).exists.choose

/-- The glued section has exactly the prescribed germs. -/
@[simp]
theorem sectionOfLocallyRepresentable_germ
    (g : ∀ x : X, F.presheaf.stalk x)
    (hlocal : ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
      ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y) (x : X) :
    F.presheaf.Γgerm x (sectionOfLocallyRepresentable F g hlocal) = g x :=
  (existsUnique_section_of_locally_representable F g hlocal).exists.choose_spec x

variable (A : AddCommGrpCat.{u}) (g : ∀ x : X, A ⟶ F.presheaf.stalk x)
  (hlocal : ∀ (a : A) (x : X), ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
    ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y a)

/-- The global section map is additive because equality can be checked on stalks. -/
def globalMapOfLocallyRepresentable : A ⟶ F.presheaf.obj (op ⊤) :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ sectionOfLocallyRepresentable F (fun x ↦ g x a) (hlocal a)
      map_zero' := by
        apply TopCat.Presheaf.section_ext F
        intro x _
        change F.presheaf.Γgerm x (sectionOfLocallyRepresentable F
          (fun x ↦ g x 0) (hlocal 0)) = F.presheaf.Γgerm x 0
        rw [sectionOfLocallyRepresentable_germ, map_zero, map_zero]
      map_add' := by
        intro a b
        apply TopCat.Presheaf.section_ext F
        intro x _
        change F.presheaf.Γgerm x _ = F.presheaf.Γgerm x (_ + _)
        simp only [map_add, sectionOfLocallyRepresentable_germ] }

/-- The actual presheaf map from constants, prior to sheafification. -/
def constantPresheafMapOfLocallyRepresentable :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.presheaf where
  app U := globalMapOfLocallyRepresentable F A g hlocal ≫
    F.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    rfl

/-- Gluing followed by sheafification constructs the constant-sheaf map. -/
def constantSheafMapOfLocallyRepresentable :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    (constantPresheafMapOfLocallyRepresentable F A g hlocal) F.property⟩

variable {F}

set_option backward.isDefEq.respectTransparency false in
/-- The canonical constant-sheaf stalk identification, directed from the coefficient
group to the stalk. Its map is the germ of an actual constant section. -/
def constantSheafStalkIso (A : AddCommGrpCat.{u}) (x : X) :
    A ≅ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj := by
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  letI : IsIso (P.Γgerm x) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      obtain ⟨U, hx, i, j, hij⟩ := P.germ_eq (U := ⊤) (V := ⊤)
        x True.intro True.intro a b hab
      exact hij
    · intro t
      obtain ⟨U, hx, a, rfl⟩ := P.exists_germ_eq t
      exact ⟨a, (P.Γgerm_res_apply (i := homOfLE (show U ≤ ⊤ from le_top)) x hx a).symm⟩
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  exact asIso (P.Γgerm x) ≪≫
    asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))

variable (F)

end TopCat.Sheaf
