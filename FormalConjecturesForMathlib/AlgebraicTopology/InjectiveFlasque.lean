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

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective sheaves are flasque

For an open set `U`, sections of an additive sheaf `F` over `U` are represented by morphisms
from the sheafification of the free abelian presheaf on `yoneda.obj U`.  An inclusion of open
sets induces a monomorphism between these representing sheaves.  The extension property of an
injective sheaf therefore makes every restriction map surjective.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- The sheafified free abelian Yoneda functor on the poset of open subsets. -/
abbrev freeAbelianYonedaSheaf :
    Opens X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  yoneda ⋙
    (Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Morphisms from the free abelian Yoneda sheaf represent sections over the corresponding
open subset. -/
def freeAbelianYonedaSheafHomEquiv (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((freeAbelianYonedaSheaf X).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv _ _).trans <|
    ((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans
      yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The representing equivalence sends precomposition along an inclusion to restriction of
sections. -/
lemma freeAbelianYonedaSheafHomEquiv_naturality
    {U V : Opens X} (i : V ⟶ U)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (g : (freeAbelianYonedaSheaf X).obj U ⟶ F) :
    freeAbelianYonedaSheafHomEquiv X V F
        ((freeAbelianYonedaSheaf X).map i ≫ g) =
      F.obj.map i.op (freeAbelianYonedaSheafHomEquiv X U F g) := by
  change yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _)
        (((sheafificationAdjunction (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).homEquiv _ _)
            ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
              (((Functor.whiskeringRight (Opens X)ᵒᵖ (Type u)
                AddCommGrpCat.{u}).obj AddCommGrpCat.free).map (yoneda.map i)) ≫ g))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ i).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every injective sheaf of abelian groups on a topological space is flasque. -/
instance injective_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] :
    F.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    let A := freeAbelianYonedaSheaf X
    let gV : A.obj V.unop ⟶ F :=
      (freeAbelianYonedaSheafHomEquiv X V.unop F).symm s
    let a : A.obj V.unop ⟶ A.obj U.unop := A.map i.unop
    let : Mono a := by
      let W :=
        (Functor.whiskeringRight (Opens X)ᵒᵖ (Type u) AddCommGrpCat.{u}).obj
          AddCommGrpCat.free
      let S := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      change Mono (S.map (W.map (yoneda.map i.unop)))
      let : Mono (yoneda.map i.unop) := Functor.map_mono yoneda i.unop
      let : Mono (W.map (yoneda.map i.unop)) := Functor.map_mono W (yoneda.map i.unop)
      exact Functor.map_mono S (W.map (yoneda.map i.unop))
    let gU : A.obj U.unop ⟶ F := Injective.factorThru gV a
    refine ⟨freeAbelianYonedaSheafHomEquiv X U.unop F gU, ?_⟩
    calc
      _ = freeAbelianYonedaSheafHomEquiv X V.unop F (a ≫ gU) := by
        simpa only [a, A, Quiver.Hom.op_unop] using
          (freeAbelianYonedaSheafHomEquiv_naturality X i.unop F gU).symm
      _ = freeAbelianYonedaSheafHomEquiv X V.unop F gV := by
        rw [Injective.comp_factorThru]
      _ = s := (freeAbelianYonedaSheafHomEquiv X V.unop F).apply_symm_apply s

end TopCat.Sheaf
