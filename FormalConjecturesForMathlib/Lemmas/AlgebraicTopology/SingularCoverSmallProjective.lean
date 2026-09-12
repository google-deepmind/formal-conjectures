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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCoverSmall
public import Mathlib.Algebra.Homology.QuasiIso

import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Projective reduction for the small-chain theorem

Integral simplicial chain groups are free abelian and hence projective.  Consequently, for the
nonnegatively graded singular chain complexes used by the excision development, it is enough to
prove that the cover-small inclusion is a quasi-isomorphism: projectivity upgrades it to a
chain-homotopy equivalence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped Simplicial

namespace AlgebraicTopology.Singular

set_option linter.style.haveILetI false in
/-- If the cover-small inclusion is a quasi-isomorphism, then it is a chain-homotopy
equivalence, because all the chain groups involved are projective. -/
public theorem coverSmallChainApproximation_of_quasiIso
    {i : Type} (X : TopCat) (U : i → Set X)
    (h : QuasiIso (coverSmallIntegralSingularChainInclusion X U)) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (coverSmallIntegralSingularChainInclusion X U) := by
  letI : QuasiIso (coverSmallIntegralSingularChainInclusion X U) := h
  letI projectiveInteger : Projective (AddCommGrpCat.of ℤ) :=
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_projective_iff
      (ModuleCat.of ℤ ℤ)).mpr inferInstance
  letI projectiveSmall (n : ℕ) :
      Projective ((CoverSmallIntegralSingularChainComplex X U).X n) := by
    change Projective
      (∐ fun _ : (coverSmallSingularSubcomplex X U : SSet).obj
          (Opposite.op (SimplexCategory.mk n)) ↦
        AddCommGrpCat.of ℤ)
    infer_instance
  letI projectiveFull (n : ℕ) :
      Projective ((IntegralSingularChainComplexObj X).X n) := by
    change Projective
      (∐ fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    infer_instance
  exact (ChainComplex.quasiIso_iff_of_projective
    (coverSmallIntegralSingularChainInclusion X U)).mp (by infer_instance)

end AlgebraicTopology.Singular
