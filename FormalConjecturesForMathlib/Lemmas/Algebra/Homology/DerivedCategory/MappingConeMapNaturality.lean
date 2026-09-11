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

public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality

/-! # Actual cone maps and additive comparison naturality -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.mappingCone

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {K L K' L' : CochainComplex C ℤ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The general homotopy-cofiber arrow map is the literal standard cone
map, with zero off-diagonal homotopy. -/
lemma mapArrowHom_eq_map (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g) :
    homotopyCofiber.mapArrowHom f g
      (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
      (Arrow.homMk a b h.symm) = map f g a b h := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]
  constructor
  · change homotopyCofiber.inlX f (n + 1) n _ ≫ _ = _
    simp [homotopyCofiber.mapArrowHom,
      homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n
        (ComplexShape.up_mk _ _ (by omega)), inl]
  · change homotopyCofiber.inrX f n ≫ _ = _
    simp [homotopyCofiber.mapArrowHom, inr]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Applying an additive functor to a cone map agrees with the literal
cone map after the canonical additive-functor comparison. -/
@[reassoc]
lemma mapHomologicalComplexIso_naturality (f : K ⟶ L) (g : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g)
    (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex (.up ℤ)).map (map f g a b h) ≫
      (mapHomologicalComplexIso g F).hom =
    (mapHomologicalComplexIso f F).hom ≫
      map ((F.mapHomologicalComplex (.up ℤ)).map f)
        ((F.mapHomologicalComplex (.up ℤ)).map g)
        ((F.mapHomologicalComplex (.up ℤ)).map a)
        ((F.mapHomologicalComplex (.up ℤ)).map b)
        (by rw [← Functor.map_comp, h, Functor.map_comp]) := by
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [ext_to_iff _ n (n + 1) rfl]
  simp only [mapHomologicalComplexIso, Hom.isoOfComponents_hom_f,
    mapHomologicalComplexXIso_eq _ F n (n + 1) rfl,
    mapHomologicalComplexXIso'_hom]
  constructor <;>
    simp only [map, desc_f _ _ _ _ n (n + 1) rfl, Category.assoc,
      Preadditive.add_comp, Preadditive.comp_add,
      inl_v_fst_v_assoc, inr_f_fst_v_assoc, inl_v_snd_v_assoc, inr_f_snd_v_assoc,
      inl_v_fst_v, inr_f_fst_v, inl_v_snd_v, inr_f_snd_v,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_obj_X,
      zero_comp, comp_zero, add_zero, zero_add, Category.comp_id,
      ← Functor.map_comp_assoc]

end CochainComplex.mappingCone
