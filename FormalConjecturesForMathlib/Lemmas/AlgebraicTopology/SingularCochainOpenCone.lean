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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainOpenCone

/-!
# SingularCochainOpenCone

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainOpenCone`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

attribute [local instance] singularCochainOpenConeDerivedCategory

/-- Local supported cohomology in negative degrees vanishes already
termwise in this nonnegative sheaf-cochain model. The cone index is `n - 1`. -/
lemma openSingularSheafRestrictionCone_homology_isZero_negative
    {V W : Opens X} (i : W ⟶ V) (n : ℤ) (hn : n < 0) :
    IsZero ((openSingularSheafRestrictionCone R X i).homology (n - 1)) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero ((CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
      ComplexShape.embeddingUpNat)).X (n - 1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact (openSingularCochainSheafComplex R X V).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1 + 1; omega)
  · exact (openSingularCochainSheafComplex R X W).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1; omega)

/-- The local cone comparison preserves Mathlib's connecting morphism,
including its negative-first-projection convention. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionCone_connecting {V W : Opens X} (i : W ⟶ V) :
    openRawToSingularSheafRestrictionCone R X i ≫
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ =
    (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ ≫
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
        ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧' :=
  (CochainComplex.mappingCone.triangleMap _ _ _ _
    (openSingularSheafRestrictionInt_naturality R X i)).comm₃.symm

end AlgebraicTopology.Singular
