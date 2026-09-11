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

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import FormalConjecturesForMathlib.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Residue fields and local sections along a closed immersion

A closed immersion is surjective on stalks of structure sheaves, hence on residue fields; since a
map of fields is injective, the residue fields at corresponding points are canonically isomorphic.

Surjectivity on stalks also says that a section of the closed subscheme is, near each of its
points, the restriction of a section defined on an open set of the ambient scheme. That local
lifting is what transports the analytic topology across a closed immersion.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Topology

namespace AlgebraicGeometry.IsClosedImmersion

variable {A B : Scheme} {i : A ⟶ B}

/-- A closed immersion induces a surjection on residue fields. Since a map of fields is
injective, this identifies the residue fields at corresponding points. -/
lemma residueFieldMap_surjective [IsClosedImmersion i] (x : A) :
    Function.Surjective (i.residueFieldMap x) := by
  intro y
  obtain ⟨r, rfl⟩ := A.residue_surjective x y
  obtain ⟨s, hs⟩ := i.stalkMap_surjective x r
  refine ⟨B.residue (i x) s, ?_⟩
  change (B.residue (i x) ≫ i.residueFieldMap x) s = _
  rw [Scheme.residue_residueFieldMap]
  exact congrArg (A.residue x) hs

/-- The residue-field isomorphism induced by a closed immersion. -/
noncomputable def residueFieldIso [IsClosedImmersion i] (x : A) :
    B.residueField (i x) ≅ A.residueField x :=
  (RingEquiv.ofBijective (i.residueFieldMap x).hom
    ⟨RingHom.injective _, residueFieldMap_surjective x⟩).toCommRingCatIso

lemma residueFieldIso_hom [IsClosedImmersion i] (x : A) :
    (residueFieldIso x).hom = i.residueFieldMap x :=
  rfl

/-- The map on stalks of structure sheaves induced by a closed immersion is surjective. This
version removes the pushforward-stalk comparison from the usual statement. -/
lemma stalkMap_c_surjective [IsClosedImmersion i] (x : A) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor CommRingCat (i x)).map i.c) := by
  let p := A.presheaf.stalkPushforward CommRingCat i.base x
  let : IsIso p :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      CommRingCat i.isClosedEmbedding.isInducing A.presheaf x
  intro y
  obtain ⟨s, hs⟩ := i.stalkMap_surjective x (p y)
  exact ⟨s, (ConcreteCategory.bijective_of_isIso p).1 hs⟩

/-- A section of the closed subscheme is locally the restriction of a section on the ambient
scheme, near each point of its domain. -/
lemma exists_local_ambient_lift [IsClosedImmersion i] (U : B.Opens)
    (t : ((TopCat.Presheaf.pushforward CommRingCat i.base).obj A.presheaf).obj (op U))
    (x : A) (hx : i x ∈ U) :
    ∃ (V : B.Opens) (hVU : V ⟶ U),
      (∃ s : Γ(B, V), (i.c.app (op V)) s =
        (((TopCat.Presheaf.pushforward CommRingCat i.base).obj A.presheaf).map hVU.op) t) ∧
          i x ∈ V := by
  set t_x := ((TopCat.Presheaf.pushforward CommRingCat i.base).obj A.presheaf).germ
    U (i x) hx t with ht_x
  obtain ⟨s_x, hs_x : ((TopCat.Presheaf.stalkFunctor CommRingCat (i x)).map i.c) s_x =
      t_x⟩ := stalkMap_c_surjective x t_x
  obtain ⟨V, hxV, s, rfl⟩ := B.presheaf.exists_germ_eq s_x
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht_x] at hs_x
  have key_W := ((TopCat.Presheaf.pushforward CommRingCat i.base).obj A.presheaf).germ_eq
    (i x) hxV hx (i.c.app _ s) t hs_x
  obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
  refine ⟨W, hWU, ⟨B.presheaf.map hWV.op s, ?_⟩, hxW⟩
  convert! h_eq using 1
  simp only [← ConcreteCategory.comp_apply, i.c.naturality]


end AlgebraicGeometry.IsClosedImmersion
