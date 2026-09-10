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

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

For `0 → A → B → C → 0` this file constructs the canonical quasi-isomorphism
`A → mappingCocone (B → C)`. Its normalization is the actual inclusion `A → B`.
The proof uses the explicit mapping-cone rotation homotopy equivalence and the
canonical quasi-isomorphism from the cone of `A → B` to `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A map of mapping cones induced by quasi-isomorphisms is a quasi-isomorphism. -/
lemma quasiIso_map_of_quasiIso {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : f₁ ≫ b = a ≫ f₂) [QuasiIso a] [QuasiIso b] :
    QuasiIso (map f₁ f₂ a b h) := by
  let := HasDerivedCategory.standard C
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C _).1
  exact isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map (triangleMap f₁ f₂ a b h))
    (DerivedCategory.mappingCone_triangle_distinguished f₁)
    (DerivedCategory.mappingCone_triangle_distinguished f₂)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map a)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map b)))

end mappingCone

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- The explicit rotated-cone comparison, before shifting back to the homotopy
fiber. It is built from canonical chain maps, not from a choice of a completion
of a morphism of distinguished triangles. -/
def shiftedLiftShortComplex : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

lemma quasiIso_shiftedLiftShortComplex (hS : S.ShortExact) :
    QuasiIso (shiftedLiftShortComplex S) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have := mappingCone.quasiIso_map_of_quasiIso
    (mappingCone.inr S.f) S.g (𝟙 _) (mappingCone.descShortComplex S) (by simp)
  dsimp only [shiftedLiftShortComplex]
  infer_instance

/-- Canonical comparison from the first term of a short complex to the homotopy
fiber of its second map. -/
def liftShortComplex : S.X₁ ⟶ mappingCocone S.g :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).inv.app S.X₁ ≫
    (shiftedLiftShortComplex S)⟦(-1 : ℤ)⟧'

set_option backward.isDefEq.respectTransparency false in
lemma quasiIso_liftShortComplex (hS : S.ShortExact) :
    QuasiIso (liftShortComplex S) := by
  have := quasiIso_shiftedLiftShortComplex S hS
  dsimp only [liftShortComplex]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftShortComplex_fst : liftShortComplex S ≫ fst S.g = S.f := by
  ext n
  have aux (p q : ℤ) (h : p = q) (hpq : p + 0 = q) :
      (S.X₁.XIsoOfEq h.symm).hom ≫ (HomComplex.Cochain.ofHom S.f).v p q hpq =
        S.f.f q := by
    subst q
    simp
  simpa [liftShortComplex, shiftedLiftShortComplex, fst,
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    mappingCone.rotateHomotopyEquiv, mappingCone.map,
    mappingCone.lift_f _ _ _ _ (n + -1) n (by omega),
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso] using
      aux (n + -1 + 1) n (by omega) (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma liftShortComplex_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (liftShortComplex S).f p ≫ (snd S.g).v p q hpq = 0 := by
  subst q
  simp [liftShortComplex, shiftedLiftShortComplex, snd,
    shiftFunctorCompIsoId, shiftFunctorAdd'_hom_app_f', shiftFunctorZero_inv_app_f,
    mappingCone.rotateHomotopyEquiv, mappingCone.map,
    mappingCone.lift_f _ _ _ _ (p + -1) p (by omega),
    HomComplex.Cochain.leftShift, shiftFunctorObjXIso]

/-- The rotated-cone formula is exactly the standard fiber lift with the zero
nullhomotopy of `S.f ≫ S.g = 0`. Thus its chain-level normalization is canonical. -/
lemma liftShortComplex_eq_lift :
    liftShortComplex S = lift S.g S.f 0 (by simp) := by
  ext p
  calc
    _ = (liftShortComplex S).f p ≫ 𝟙 _ := by simp
    _ = (liftShortComplex S).f p ≫
        ((fst S.g).f p ≫ (inl S.g).v p p (add_zero p) +
          (snd S.g).v p (p + -1) rfl ≫ (inr S.g).1.v (p + -1) p (by omega)) := by
      rw [id_X]
    _ = (lift S.g S.f 0 (by simp)).f p ≫
        ((fst S.g).f p ≫ (inl S.g).v p p (add_zero p) +
          (snd S.g).v p (p + -1) rfl ≫ (inr S.g).1.v (p + -1) p (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, liftShortComplex_f_snd_v,
        zero_comp, add_zero, lift_f_fst_f, lift_f_snd_v,
        HomComplex.Cochain.zero_v]
      exact congrArg (fun f : S.X₁ ⟶ S.X₂ => f.f p ≫ (inl S.g).v p p (add_zero p))
        (liftShortComplex_fst S)
    _ = _ := by rw [id_X]; simp

end mappingCocone

end CochainComplex
