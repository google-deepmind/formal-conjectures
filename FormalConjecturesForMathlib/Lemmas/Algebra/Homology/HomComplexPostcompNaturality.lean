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

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Postcomposition and naturality for the Hom complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ} (f : L ⟶ M)

/-- Postcomposition by an actual chain map, on the entire Hom complex. -/
def postcompMap : HomComplex K L ⟶ HomComplex K M where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' _ _ := Cochain.add_comp _ _ _ _ }
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z f m

/-- Postcomposition on cocycles as an additive map. -/
def postcompCocycle (n : ℤ) : Cocycle K L n →+ Cocycle K M n where
  toFun z := z.postcomp f
  map_zero' := by ext; simp [Cocycle.postcomp]
  map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp]

/-- Postcomposition descends to actual cohomology classes. -/
def postcompClass (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K M n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K M n).comp (postcompCocycle K f n)) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.postcomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, a.comp (Cochain.ofHom f) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, ha]
      rfl)

@[simp]
lemma postcompClass_mk (n : ℤ) (z : Cocycle K L n) :
    postcompClass K f n (CohomologyClass.mk z) = CohomologyClass.mk (z.postcomp f) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit cycles and cohomology-class maps describe the homology map
of postcomposition. -/
def postcompLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (postcompMap K f)) (leftHomologyData K L n) (leftHomologyData K M n) where
  φK := AddCommGrpCat.ofHom (postcompCocycle K f n)
  φH := AddCommGrpCat.ofHom (postcompClass K f n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K M n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom (postcompCocycle K f n) ≫ (leftHomologyData K M n).i =
        (leftHomologyData K L n).i ≫ (postcompMap K f).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
      (postcompMap K f)).comm₁₂.symm
  commπ := rfl

/-- The Hom-complex homology/cohomology-class equivalence is natural under
postcomposition by a chain map. -/
lemma homologyAddEquiv_postcompMap (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K M n (HomologicalComplex.homologyMap (postcompMap K f) n x) =
      postcompClass K f n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (postcompLeftHomologyMapData K f n).homologyMap_comm x

end CochainComplex.HomComplex
