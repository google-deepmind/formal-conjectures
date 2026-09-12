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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.RelativeCochainCone

/-!
# Relative singular cohomology as a cochain mapping cone

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.RelativeCochainCone`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
/-- The cone comparison commutes with the connecting morphism which, in supported
cohomology, forgets support. -/
lemma relativeDualShiftIsoCochainCone_hom_comp_mor₃ (X : TopPair.{u}) :
    (relativeDualShiftIsoCochainCone R X).hom ≫
        (CochainComplex.mappingCone.triangleh
          (relativeCochainRestrictionInt R X)).mor₃ =
      (CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X)).rotate.mor₃ := by
  change (relativeCochainConeTriangleIso R X).hom.hom₃ ≫
      (CochainComplex.mappingCone.triangleh
        (relativeCochainRestrictionInt R X)).mor₃ = _
  rw [← (relativeCochainConeTriangleIso R X).hom.comm₃]
  unfold relativeCochainConeTriangleIso
  rw [Pretriangulated.isoTriangleOfIso₁₂_hom_hom₁]
  simp

end AlgebraicTopology.Singular
