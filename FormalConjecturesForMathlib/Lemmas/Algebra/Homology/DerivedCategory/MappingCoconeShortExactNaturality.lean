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

public import FormalConjecturesForMathlib.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-!
# MappingCoconeShortExactNaturality

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCocone

variable {C : Type*} [Category* C] [Abelian C]
  {S T : ShortComplex (CochainComplex C ℤ)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit shifted fiber lift is natural for actual short-complex
maps, before passing to any derived or homotopy category. -/
@[reassoc]
lemma shiftedLiftShortComplex_naturality (f : S ⟶ T) :
    f.τ₁⟦(1 : ℤ)⟧' ≫ shiftedLiftShortComplex T =
      shiftedLiftShortComplex S ≫
        mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm := by
  ext n
  simp [shiftedLiftShortComplex, mappingCone.rotateHomotopyEquiv,
    mappingCone.map, mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun g => g.f (n + 1) ≫ (mappingCone.inl T.g).v (n + 1) n (by omega))
      f.comm₁₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality on homology of the canonical cone comparison. -/
@[reassoc]
lemma shortExactHomologyIsoCone_naturality (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n n' : ℤ) (h : 1 + n = n') :
    HomologicalComplex.homologyMap f.τ₁ n' ≫
      (shortExactHomologyIsoCone T hT n n' h).hom =
    (shortExactHomologyIsoCone S hS n n' h).hom ≫
      HomologicalComplex.homologyMap
        (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm) n := by
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) 0
  change (H.shift n').map f.τ₁ ≫
      (((H.shiftIso 1 n n' h).inv.app T.X₁) ≫
        (H.shift n).map (shiftedLiftShortComplex T)) =
    ((H.shiftIso 1 n n' h).inv.app S.X₁ ≫
      (H.shift n).map (shiftedLiftShortComplex S)) ≫
      (H.shift n).map (mappingCone.map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm)
  rw [(H.shiftIso 1 n n' h).inv.naturality_assoc f.τ₁,
    Functor.comp_map, ← Functor.map_comp, shiftedLiftShortComplex_naturality, Functor.map_comp,
    Category.assoc]

end CochainComplex.mappingCocone
