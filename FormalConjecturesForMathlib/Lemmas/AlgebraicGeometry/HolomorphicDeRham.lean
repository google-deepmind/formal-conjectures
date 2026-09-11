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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HolomorphicDeRham

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.HolomorphicPoincare
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The holomorphic de Rham complex

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.HolomorphicDeRham`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

lemma holomorphicDeRhamModuleDifferential_comp
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    holomorphicDeRhamModuleDifferential X d p ≫
      holomorphicDeRhamModuleDifferential X d (p + 1) = 0 :=
  NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| LinearMap.ext fun x =>
    holomorphicFormDifferential_squared X d U p x

/-- The holomorphic de Rham complex is exact in every degree above the complex dimension. -/
lemma holomorphicDeRhamComplex_exactAt_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    (holomorphicDeRhamComplex X d).ExactAt p :=
  HomologicalComplex.ExactAt.of_isZero
    (holomorphicDeRhamSheaf_isZero_of_lt X d hp)

@[simp] lemma scalarHolomorphicDeRhamPresheaf_apply
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (c : ℂ)
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : HolomorphicForm X d U p) :
    (scalarHolomorphicDeRhamPresheaf X d p c).app U x = c • x := by
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_zero
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf X d p 0 = 0 := by
  ext U x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_one
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) :
    scalarHolomorphicDeRhamPresheaf X d p 1 = 𝟙 _ := by
  ext U x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_add
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf X d p (a + b) =
      scalarHolomorphicDeRhamPresheaf X d p a +
        scalarHolomorphicDeRhamPresheaf X d p b := by
  ext U x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [add_smul]
  rfl

@[simp] lemma scalarHolomorphicDeRhamPresheaf_mul
    [SmoothOfRelativeDimension d X.hom] (p : ℕ) (a b : ℂ) :
    scalarHolomorphicDeRhamPresheaf X d p (a * b) =
      scalarHolomorphicDeRhamPresheaf X d p b ≫
        scalarHolomorphicDeRhamPresheaf X d p a := by
  ext U x
  dsimp [scalarHolomorphicDeRhamPresheaf, holomorphicDeRhamPresheaf]
  simp [mul_smul]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplex_zero
    [SmoothOfRelativeDimension d X.hom] :
    scalarHolomorphicDeRhamComplex X d 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p 0) = 0
  rw [scalarHolomorphicDeRhamPresheaf_zero, Functor.map_zero]

@[simp] lemma scalarHolomorphicDeRhamComplex_one
    [SmoothOfRelativeDimension d X.hom] :
    scalarHolomorphicDeRhamComplex X d 1 = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p 1) = 𝟙 _
  rw [scalarHolomorphicDeRhamPresheaf_one]
  exact (presheafToSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat).map_id _

@[simp] lemma scalarHolomorphicDeRhamComplex_add
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex X d (a + b) =
      scalarHolomorphicDeRhamComplex X d a +
        scalarHolomorphicDeRhamComplex X d b := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p (a + b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_add, Functor.map_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplex_mul
    [SmoothOfRelativeDimension d X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplex X d (a * b) =
      scalarHolomorphicDeRhamComplex X d b ≫
        scalarHolomorphicDeRhamComplex X d a := by
  apply HomologicalComplex.hom_ext
  intro p
  change (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
      (scalarHolomorphicDeRhamPresheaf X d p (a * b)) = _
  rw [scalarHolomorphicDeRhamPresheaf_mul, Functor.map_comp]
  rfl

/-- Conjugating twice is the identity on the constant complex presheaf. -/
lemma conjConstantComplexPresheaf_comp_self :
    conjConstantComplexPresheaf X ≫ conjConstantComplexPresheaf X =
      𝟙 (constantComplexAddCommGrpPresheaf X) := by
  ext U : 2
  change (starRingEnd ℂ).toAddMonoidHom.comp (starRingEnd ℂ).toAddMonoidHom = AddMonoidHom.id ℂ
  exact AddMonoidHom.ext Complex.conj_conj

/-- Conjugating twice is the identity on the constant complex sheaf. -/
lemma conjConstantComplexSheaf_comp_self :
    conjConstantComplexSheaf X ≫ conjConstantComplexSheaf X =
      𝟙 (constantComplexSheaf X) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) ≫
    (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) = _
  rw [← Functor.map_comp, conjConstantComplexPresheaf_comp_self]
  exact (presheafToSheaf J AddCommGrpCat).map_id _

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex presheaf. This is the presheaf-level source of conjugate-linearity. -/
lemma complexScalarPresheaf_comp_conj (c : ℂ) :
    complexScalarPresheaf X c ≫ conjConstantComplexPresheaf X =
      conjConstantComplexPresheaf X ≫
        complexScalarPresheaf X (starRingEnd ℂ c) := by
  ext U : 2
  change (starRingEnd ℂ).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c) =
    (DistribSMul.toAddMonoidHom ℂ (starRingEnd ℂ c)).comp (starRingEnd ℂ).toAddMonoidHom
  exact AddMonoidHom.ext (map_mul (starRingEnd ℂ) c)

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the constant
complex sheaf. -/
lemma complexScalarSheaf_comp_conj (c : ℂ) :
    complexScalarSheaf X c ≫ conjConstantComplexSheaf X =
      conjConstantComplexSheaf X ≫
        complexScalarSheaf X (starRingEnd ℂ c) := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map (complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) =
    (presheafToSheaf J AddCommGrpCat).map (conjConstantComplexPresheaf X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (complexScalarPresheaf X (starRingEnd ℂ c))
  rw [← Functor.map_comp, ← Functor.map_comp, complexScalarPresheaf_comp_conj]

/-- The inclusion of constant zero-forms commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamZero_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamZeroSheaf X d ≫
      (let J := Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf X d 0 c)) =
    complexScalarSheaf X c ≫
      constantsToHolomorphicDeRhamZeroSheaf X d := by
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  change (presheafToSheaf J AddCommGrpCat).map
      (constantsToHolomorphicDeRhamZero X d) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (scalarHolomorphicDeRhamPresheaf X d 0 c) =
    (presheafToSheaf J AddCommGrpCat).map
      (complexScalarPresheaf X c) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (constantsToHolomorphicDeRhamZero X d)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  let f := holomorphicFormOfConstant X d U
  change (c • LinearMap.id).toAddMonoidHom.comp f.toAddMonoidHom =
    f.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom ℂ c)
  ext x
  change c • f x = f (c • x)
  exact (f.map_smul c x).symm

/-- The constant-to-de Rham comparison is a quasi-isomorphism in every degree above the complex
dimension. Both sides have zero cohomology there. -/
lemma constantsToHolomorphicDeRhamComplex_quasiIsoAt_of_lt
    [SmoothOfRelativeDimension d X.hom] {p : ℕ} (hp : d < p) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplex X d) p := by
  have hp0 : p ≠ 0 := by lia
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp0
  rw [quasiIsoAt_iff_exactAt _ _
    (CochainComplex.exactAt_succ_single_obj (constantComplexSheaf X) q)]
  exact holomorphicDeRhamComplex_exactAt_of_lt X d hp

/-- The constant-to-de Rham comparison commutes with complex scalar multiplication. -/
lemma constantsToHolomorphicDeRhamComplex_scalar
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamComplex X d ≫
      scalarHolomorphicDeRhamComplex X d c =
    complexScalarComplex X c ≫
      constantsToHolomorphicDeRhamComplex X d := by
  apply HomologicalComplex.hom_ext
  intro p
  rcases p with _ | p
  · exact constantsToHolomorphicDeRhamZero_scalar X d c
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℕ) 0 (constantComplexSheaf X) (p + 1)
      (Nat.succ_ne_zero p)).eq_of_src

/-- Conjugating twice is the identity in degree zero. -/
lemma conjConstantComplexComplex_comp_self :
    conjConstantComplexComplex X ≫ conjConstantComplexComplex X = 𝟙 _ := by
  unfold conjConstantComplexComplex
  rw [← Functor.map_comp, conjConstantComplexSheaf_comp_self]
  exact (CochainComplex.single₀ _).map_id _

/-- Conjugation intertwines the two scalar multiplications in degree zero. -/
lemma complexScalarComplex_comp_conj (c : ℂ) :
    complexScalarComplex X c ≫ conjConstantComplexComplex X =
      conjConstantComplexComplex X ≫
        complexScalarComplex X (starRingEnd ℂ c) := by
  unfold complexScalarComplex conjConstantComplexComplex
  rw [← Functor.map_comp, ← Functor.map_comp, complexScalarSheaf_comp_conj]

/-- Conjugating twice is the identity on the integer-indexed constant complex. -/
lemma conjConstantComplexSheafComplexInt_comp_self :
    conjConstantComplexSheafComplexInt X ≫ conjConstantComplexSheafComplexInt X = 𝟙 _ := by
  unfold conjConstantComplexSheafComplexInt constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, conjConstantComplexComplex_comp_self]
  exact HomologicalComplex.extendMap_id _ _

/-- Conjugation intertwines multiplication by `c` with multiplication by `conj c` on the
integer-indexed constant complex. -/
lemma complexScalarComplexInt_comp_conj (c : ℂ) :
    complexScalarComplexInt X c ≫ conjConstantComplexSheafComplexInt X =
      conjConstantComplexSheafComplexInt X ≫
        complexScalarComplexInt X (starRingEnd ℂ c) := by
  unfold complexScalarComplexInt conjConstantComplexSheafComplexInt
    constantComplexSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    complexScalarComplex_comp_conj]

@[simp] lemma scalarHolomorphicDeRhamComplexInt_zero
    [IsIntegral X.left] [Smooth X.hom] :
    scalarHolomorphicDeRhamComplexInt X 0 = 0 := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_zero, HomologicalComplex.extendMap_zero]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_one
    [IsIntegral X.left] [Smooth X.hom] :
    scalarHolomorphicDeRhamComplexInt X 1 = 𝟙 _ := by
  unfold scalarHolomorphicDeRhamComplexInt holomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_one]
  exact HomologicalComplex.extendMap_id _ _

@[simp] lemma scalarHolomorphicDeRhamComplexInt_add
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt X (a + b) =
      scalarHolomorphicDeRhamComplexInt X a +
        scalarHolomorphicDeRhamComplexInt X b := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_add, HomologicalComplex.extendMap_add]
  rfl

@[simp] lemma scalarHolomorphicDeRhamComplexInt_mul
    [IsIntegral X.left] [Smooth X.hom] (a b : ℂ) :
    scalarHolomorphicDeRhamComplexInt X (a * b) =
      scalarHolomorphicDeRhamComplexInt X b ≫
        scalarHolomorphicDeRhamComplexInt X a := by
  unfold scalarHolomorphicDeRhamComplexInt
  rw [scalarHolomorphicDeRhamComplex_mul, HomologicalComplex.extendMap_comp]
  rfl

/-- The integer-indexed constant-to-de Rham comparison is a quasi-isomorphism at every
degree. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt X) n :=
  inferInstance

/-- In a nonnegative degree, extending the constant-to-de Rham comparison from natural to
integer indices does not change whether it is a quasi-isomorphism. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_iff
    [IsIntegral X.left] [Smooth X.hom] (p : ℕ) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt X) (p : ℤ) ↔
      QuasiIsoAt (constantsToHolomorphicDeRhamComplex X (dim X.left)) p :=
  HomologicalComplex.quasiIsoAt_extendMap_iff
    (constantsToHolomorphicDeRhamComplex X (dim X.left))
    ComplexShape.embeddingUpNat rfl

/-- The integer-indexed constant-to-de Rham comparison is automatically a quasi-isomorphism in
negative degrees, since both extended complexes vanish there. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_of_neg
    [IsIntegral X.left] [Smooth X.hom] {n : ℤ} (hn : n < 0) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt X) n := by
  have hnone : ∀ p : ℕ, (p : ℤ) ≠ n := fun p hp => by lia
  rw [quasiIsoAt_iff_exactAt]
  · exact HomologicalComplex.extend_exactAt
      (holomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat n hnone
  · exact HomologicalComplex.extend_exactAt
      ((CochainComplex.single₀
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
          (constantComplexSheaf X))
      ComplexShape.embeddingUpNat n hnone

/-- The integer-indexed comparison is a quasi-isomorphism in every nonnegative degree above the
complex dimension. -/
lemma constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℕ} (hp : dim X.left < p) :
    QuasiIsoAt (constantsToHolomorphicDeRhamComplexInt X) (p : ℤ) := by
  rw [constantsToHolomorphicDeRhamComplexInt_quasiIsoAt_iff]
  exact constantsToHolomorphicDeRhamComplex_quasiIsoAt_of_lt X (dim X.left) hp

/-- The integer-indexed constant-to-de Rham comparison commutes with complex scalar
multiplication. -/
lemma constantsToHolomorphicDeRhamComplexInt_scalar
    [IsIntegral X.left] [Smooth X.hom] (c : ℂ) :
    constantsToHolomorphicDeRhamComplexInt X ≫
      scalarHolomorphicDeRhamComplexInt X c =
    complexScalarComplexInt X c ≫
      constantsToHolomorphicDeRhamComplexInt X := by
  unfold constantsToHolomorphicDeRhamComplexInt
    scalarHolomorphicDeRhamComplexInt complexScalarComplexInt
  change HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (scalarHolomorphicDeRhamComplex X (dim X.left) c) ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (complexScalarComplex X c) ComplexShape.embeddingUpNat ≫
    HomologicalComplex.extendMap
      (constantsToHolomorphicDeRhamComplex X (dim X.left)) ComplexShape.embeddingUpNat
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_scalar]

end AlgebraicGeometry.ComplexPoint
