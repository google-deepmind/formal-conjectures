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

public import FormalConjecturesForMathlib.Algebra.Homology.HomComplexPostcompNaturality

/-! # Hom-complex cohomology and target shifts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A map on homology only depends on the middle component of a morphism of
short complexes. -/
lemma homologyMap_eq_of_middle_eq {S T : ShortComplex C} (f g : S ⟶ T)
    (h : f.τ₂ = g.τ₂) : homologyMap f = homologyMap g := by
  apply (cancel_epi S.homologyπ).1
  apply (cancel_mono T.homologyι).1
  simpa only [Category.assoc, π_homologyMap_ι] using
    congrArg (fun k => S.iCycles ≫ k ≫ T.pOpcycles) h

end CategoryTheory.ShortComplex

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (A K : CochainComplex C ℤ) (s n n' : ℤ) (h : n + s = n')

/-- Unshift the target on cochains, with its grading displayed. -/
def rightUnshiftCochain : Cochain A (K⟦s⟧) n →+ Cochain A K n' where
  toFun z := z.rightUnshift n' h
  map_zero' := by simp
  map_add' _ _ := Cochain.rightUnshift_add _ _ _ _

/-- Unshift the target on cocycles. -/
def rightUnshiftCocycle : Cocycle A (K⟦s⟧) n →+ Cocycle A K n' where
  toFun z := z.rightUnshift n' h
  map_zero' := by ext; simp [Cocycle.rightUnshift]
  map_add' _ _ := by ext; simp [Cocycle.rightUnshift, Cochain.rightUnshift_add]

/-- Target unshifting descends through actual coboundaries. The factor
`(-1)^s` is included in the witnessing primitive. -/
def rightUnshiftClass : CohomologyClass A (K⟦s⟧) n →+ CohomologyClass A K n' :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom A K n').comp (rightUnshiftCocycle A K s n n' h)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.rightUnshift n' h) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m + s, by omega,
        s.negOnePow • a.rightUnshift (m + s) rfl, ?_⟩
      rw [δ_units_smul, Cochain.δ_rightUnshift a (m + s) rfl n' n h, ha,
        smul_smul, Int.units_mul_self, one_smul]
      rfl)

@[simp]
lemma rightUnshiftClass_mk (z : Cocycle A (K⟦s⟧) n) :
    rightUnshiftClass A K s n n' h (CohomologyClass.mk z) =
      CohomologyClass.mk (z.rightUnshift n' h) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual three-term map for unshifting a target. The outer components
have the standard `(-1)^s` factors; its middle component has no sign. -/
def rightUnshiftShortComplex :
    (HomComplex A (K⟦s⟧)).sc n ⟶ (HomComplex A K).sc n' where
  τ₁ := s.negOnePow • AddCommGrpCat.ofHom
    (rightUnshiftCochain A K s ((ComplexShape.up ℤ).prev n)
      ((ComplexShape.up ℤ).prev n') (by simp only [CochainComplex.prev]; omega))
  τ₂ := AddCommGrpCat.ofHom (rightUnshiftCochain A K s n n' h)
  τ₃ := s.negOnePow • AddCommGrpCat.ofHom
    (rightUnshiftCochain A K s ((ComplexShape.up ℤ).next n)
      ((ComplexShape.up ℤ).next n') (by simp only [CochainComplex.next]; omega))
  comm₁₂ := by
    ext z
    change δ ((ComplexShape.up ℤ).prev n') n'
        (s.negOnePow • z.rightUnshift ((ComplexShape.up ℤ).prev n')
          (by simp only [CochainComplex.prev]; omega)) =
      (δ ((ComplexShape.up ℤ).prev n) n z).rightUnshift n' h
    rw [δ_units_smul, Cochain.δ_rightUnshift z _ _ n' n h,
      smul_smul, Int.units_mul_self, one_smul]
  comm₂₃ := by
    ext z
    exact Cochain.δ_rightUnshift z n' h ((ComplexShape.up ℤ).next n')
      ((ComplexShape.up ℤ).next n) (by simp only [CochainComplex.next]; omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Target unshifting on cohomology classes describes exactly the homology
map of the sign-normalized three-term comparison. -/
def rightUnshiftLeftHomologyMapData :
    ShortComplex.LeftHomologyMapData (rightUnshiftShortComplex A K s n n' h)
      (leftHomologyData A (K⟦s⟧) n) (leftHomologyData A K n') where
  φK := AddCommGrpCat.ofHom (rightUnshiftCocycle A K s n n' h)
  φH := AddCommGrpCat.ofHom (rightUnshiftClass A K s n n' h)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData A K n').i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (rightUnshiftCocycle A K s n n' h) ≫
        (leftHomologyData A K n').i =
      (leftHomologyData A (K⟦s⟧) n).i ≫
        (rightUnshiftShortComplex A K s n n' h).τ₂ from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact (rightUnshiftShortComplex A K s n n' h).comm₁₂.symm
  commπ := rfl

lemma homologyAddEquiv_rightUnshift (x : (HomComplex A (K⟦s⟧)).homology n) :
    homologyAddEquiv A K n'
      (ShortComplex.homologyMap (rightUnshiftShortComplex A K s n n' h) x) =
    rightUnshiftClass A K s n n' h (homologyAddEquiv A (K⟦s⟧) n x) :=
  ConcreteCategory.congr_hom
    (rightUnshiftLeftHomologyMapData A K s n n' h).homologyMap_comm x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Unshifting cocycles corresponds to the actual shift-composition
isomorphism on their representing chain maps. -/
lemma equivHomShift_symm_rightUnshift (z : Cocycle A (K⟦s⟧) n) :
    Cocycle.equivHomShift.symm (z.rightUnshift n' h) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm z)
        (show ShiftedHom (K⟦s⟧) K s from 𝟙 (K⟦s⟧)) (by omega) := by
  ext p
  simp [ShiftedHom.comp, Cocycle.equivHomShift_symm_apply,
    Cochain.rightShift, Cochain.rightUnshift,
    shiftFunctorAdd'_inv_app_f', shiftFunctorObjXIso]

lemma rightUnshift_v_zero (z : Cochain A (K⟦s⟧) n) :
    (z.rightUnshift (n + s) rfl).v 0 (n + s) (zero_add _) =
      z.v 0 n (zero_add _) := by
  dsimp only [Cochain.rightUnshift, Cochain.mk_v]
  exact z.v_comp_XIsoOfEq_hom 0 (0 + n) n rfl (zero_add n)

end CochainComplex.HomComplex
