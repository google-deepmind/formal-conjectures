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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiGlobalSectionsComparison
/-! # Naturality of the additive map/extension comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v

variable {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}

set_option backward.isDefEq.respectTransparency false in
/-- The explicit additive map/extension isomorphism is natural in chain maps. -/
@[reassoc]
lemma mapExtendIso_inv_naturality
    (F : Functor C D) [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    extendMap ((F.mapHomologicalComplex c).map f) e ≫ (mapExtendIso F L e).inv =
      (mapExtendIso F K e).inv ≫ (F.mapHomologicalComplex c').map (extendMap f e) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change extend.mapX ((F.mapHomologicalComplex c).map f) (e.r q) ≫
      (mapExtendXIsoAux F L (e.r q)).inv =
    (mapExtendXIsoAux F K (e.r q)).inv ≫ F.map (extend.mapX f (e.r q))
  generalize e.r q = x
  cases x with
  | none => simp [extend.mapX, mapExtendXIsoAux]
  | some n =>
    change F.map (f.f n) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.f n)
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Naturality in an actual transformation out of the identity functor. This
fixes the normalization of restriction after extending a complex by zero. -/
@[reassoc]
lemma mapExtendIso_hom_naturality_from_id
    (F : C ⥤ C) [F.Additive] (τ : 𝟭 C ⟶ F) (K : HomologicalComplex C c)
    (e : c.Embedding c') [e.IsRelIff] :
    (τ.mapHomologicalComplex c').app (K.extend e) ≫ (mapExtendIso F K e).hom =
      extendMap ((τ.mapHomologicalComplex c).app K) e := by
  apply HomologicalComplex.Hom.ext
  funext q
  change τ.app (extend.X K (e.r q)) ≫ (mapExtendXIsoAux F K (e.r q)).hom =
    extend.mapX ((τ.mapHomologicalComplex c).app K) (e.r q)
  generalize e.r q = x
  cases x with
  | none => exact (Limits.isZero_zero C).eq_of_src _ _
  | some n =>
    change τ.app (K.X n) ≫ 𝟙 _ = τ.app (K.X n)
    simp

end HomologicalComplex

namespace CochainComplex

universe u

variable {C D : Type u} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℕ} (f : K ⟶ L)
  [QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map f)]

/-- If applying an additive functor to a nonnegative chain map gives a
quasi-isomorphism, the same holds for its extension to integer degrees. -/
lemma quasiIso_map_extendMap_nat :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) := by
  have : QuasiIso ((HomologicalComplex.mapExtendIso F K ComplexShape.embeddingUpNat).inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)) := by
    rw [← HomologicalComplex.mapExtendIso_inv_naturality F f ComplexShape.embeddingUpNat]
    infer_instance
  exact quasiIso_of_comp_left
    (HomologicalComplex.mapExtendIso F K ComplexShape.embeddingUpNat).inv _

end CochainComplex
