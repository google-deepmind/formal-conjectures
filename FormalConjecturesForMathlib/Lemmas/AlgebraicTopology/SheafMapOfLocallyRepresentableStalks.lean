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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks

/-!
# Assembling constant-sheaf maps from locally represented stalk maps

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

variable (A : AddCommGrpCat.{u}) (g : ∀ x : X, A ⟶ F.presheaf.stalk x)
  (hlocal : ∀ (a : A) (x : X), ∃ (U : Opens X) (_ : x ∈ U) (s : F.presheaf.obj (op U)),
    ∀ (y : X) (hy : y ∈ U), F.presheaf.germ U y hy s = g y a)

/-- The global additive map has exactly the specified stalk maps. -/
@[reassoc]
theorem globalMapOfLocallyRepresentable_germ (x : X) :
    globalMapOfLocallyRepresentable F A g hlocal ≫ F.presheaf.Γgerm x = g x := by
  apply AddCommGrpCat.hom_ext
  ext a
  exact sectionOfLocallyRepresentable_germ F (fun x ↦ g x a) (hlocal a) x

/-- The sheaf map agrees with the explicitly constructed map on constant sections. -/
@[reassoc]
theorem constantSheafMapOfLocallyRepresentable_unit :
    toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A) ≫
      (constantSheafMapOfLocallyRepresentable F A g hlocal).hom =
      constantPresheafMapOfLocallyRepresentable F A g hlocal :=
  toSheafify_sheafifyLift _ _ _

variable {F}

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- Exact stalk normalization of the assembled sheaf map. -/
@[reassoc]
theorem constantSheafMapOfLocallyRepresentable_stalk (x : X) :
    (constantSheafStalkIso A x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constantSheafMapOfLocallyRepresentable F A g hlocal).hom = g x := by
  simp only [constantSheafStalkIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Functor.map_comp, constantSheafMapOfLocallyRepresentable_unit]
  dsimp only [TopCat.Presheaf.Γgerm]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  change globalMapOfLocallyRepresentable F A g hlocal ≫ F.presheaf.map (𝟙 _) ≫
    F.presheaf.Γgerm x = g x
  rw [CategoryTheory.Functor.map_id, Category.id_comp, globalMapOfLocallyRepresentable_germ]

/-- If the specified stalk maps are isomorphisms, the assembled sheaf map is an
isomorphism. This uses the actual stalk formula, not a chosen sheaf equivalence. -/
theorem constantSheafMapOfLocallyRepresentable_isIso (hg : ∀ x : X, IsIso (g x)) :
    IsIso (constantSheafMapOfLocallyRepresentable F A g hlocal) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).2
  intro x
  have hfac := constantSheafMapOfLocallyRepresentable_stalk F A g hlocal x
  have : IsIso ((constantSheafStalkIso A x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constantSheafMapOfLocallyRepresentable F A g hlocal).hom) := by
    rw [hfac]
    exact hg x
  exact IsIso.of_isIso_comp_left (constantSheafStalkIso A x).hom _

end TopCat.Sheaf
