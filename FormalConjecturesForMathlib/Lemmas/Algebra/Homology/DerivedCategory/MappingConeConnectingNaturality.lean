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

public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExact
/-! # Exact normalization of the cone connecting map

Mathlib's standard cone triangle uses the negative first projection. These
lemmas retain that sign under additive functors and under the rotated
short-exact-sequence comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShiftedHom

variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]

lemma map_commSq {K L K' L' : C} (s : ℤ)
    (a : K ⟶ K') (b : L ⟶ L') (g : K ⟶ L⟦s⟧) (g' : K' ⟶ L'⟦s⟧)
    (h : a ≫ g' = g ≫ b⟦s⟧') (F : C ⥤ D) [F.CommShift ℤ] :
    F.map a ≫ ShiftedHom.map g' F = ShiftedHom.map g F ≫ (F.map b)⟦s⟧' := by
  dsimp only [ShiftedHom.map]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (fun f => F.map g ≫ f) ((F.commShiftIso s).hom.naturality b)

lemma comp_commSq {A K L K' L' : C} (s n n' : ℤ) (h : s + n = n')
    (a : K ⟶ K') (b : L ⟶ L') (g : K ⟶ L⟦s⟧) (g' : K' ⟶ L'⟦s⟧)
    (hab : a ≫ g' = g ≫ b⟦s⟧') (x : ShiftedHom A K n) :
    x.comp g h ≫ b⟦n'⟧' = ShiftedHom.comp (x ≫ a⟦n⟧') g' h := by
  simp only [ShiftedHom.comp, Category.assoc]
  rw [← (shiftFunctorAdd' C s n n' h).inv.naturality b]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← hab]

end CategoryTheory.ShiftedHom

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace mappingCone

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The additive-functor/cone comparison preserves the exact (negative)
connecting projection, with the functor's canonical shift comparison. -/
@[reassoc]
lemma mapHomologicalComplexIso_connecting {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (F : C ⥤ D) [F.Additive] :
    (mapHomologicalComplexIso f F).hom ≫
      (triangle ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ =
    (F.mapHomologicalComplex (.up ℤ)).map (triangle f).mor₃ ≫
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) := by
  ext n
  simp [mapHomologicalComplexIso, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso', triangle, HomComplex.Cocycle.homOf,
    HomComplex.Cocycle.rightShift, HomComplex.Cochain.rightShift,
    shiftFunctorObjXIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The preceding exact chain-level equation on degree-shifted homology. -/
lemma mapHomologicalComplexIso_homology_connecting {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (F : C ⥤ D) [F.Additive]
    (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap (mapHomologicalComplexIso f F).hom n ≫
      (HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftMap
        (triangle ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ n n' h =
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftMap
      (ShiftedHom.map (triangle f).mor₃ (F.mapHomologicalComplex (.up ℤ))) n n' h := by
  change ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shift n).map _ ≫ _ = _
  rw [← Functor.shiftMap_comp', mapHomologicalComplexIso_connecting]
  rfl

end mappingCone

namespace mappingCocone

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard connecting projection is the negative shifted inclusion.
This sign must be retained when comparing a cone model of supported
cohomology with actual kernel-defined supported sections. -/
@[reassoc]
lemma shiftedLiftShortComplex_connecting (S : ShortComplex (CochainComplex C ℤ)) :
    shiftedLiftShortComplex S ≫ (mappingCone.triangle S.g).mor₃ = -S.f⟦(1 : ℤ)⟧' := by
  ext n
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The exact signed homology square for the rotated short-complex lift. -/
lemma homologyMap_shiftedLiftShortComplex_connecting
    (S : ShortComplex (CochainComplex C ℤ)) (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
        (mappingCone.triangle S.g).mor₃ n n' h =
    -(((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).hom.app
      S.X₁ ≫ HomologicalComplex.homologyMap S.f n') := by
  change ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shift n).map _ ≫ _ = _
  rw [← Functor.shiftMap_comp', shiftedLiftShortComplex_connecting]
  simp only [Functor.shiftMap, Functor.map_neg, Preadditive.neg_comp]
  congr 1
  exact (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso
    1 n n' h).hom.naturality S.f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inverting the actual short-exact-sequence quasi-isomorphism requires a
minus sign to identify the connecting map with support-forgetting. -/
lemma inv_homologyMap_shiftedLiftShortComplex_connecting
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (n n' : ℤ) (h : 1 + n = n') :
    letI := quasiIso_shiftedLiftShortComplex S hS;
    -(inv (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) ≫
      ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso 1 n n' h).hom.app S.X₁ ≫
      HomologicalComplex.homologyMap S.f n') =
    (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap
      (mappingCone.triangle S.g).mor₃ n n' h := by
  let := quasiIso_shiftedLiftShortComplex S hS
  have hh := congrArg
    (fun f => inv (HomologicalComplex.homologyMap (shiftedLiftShortComplex S) n) ≫ f)
    (homologyMap_shiftedLiftShortComplex_connecting S n n' h)
  simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp,
    Preadditive.comp_neg] using hh.symm

end mappingCocone

end CochainComplex
