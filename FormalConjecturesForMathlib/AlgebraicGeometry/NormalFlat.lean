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

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import FormalConjecturesForMathlib.RingTheory.Ideal.NormalFlat

/-!
# Normal flatness along a closed subscheme

Normal flatness is expressed on affine opens by flatness of the modules
`I ^ n / I ^ (n + 1)` over `R ⧸ I`. These are the graded pieces of the normal cone.

*References:*
* [Stacks, the normal cone of an immersion](https://stacks.math.columbia.edu/tag/062Z).
* [Cossart--Piltant, Resolution of singularities of arithmetical
  threefolds](https://arxiv.org/abs/1412.0868), Remark 1.4.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- `X` is normally flat along the closed subscheme defined by `I` if on every
affine open the associated graded pieces are flat over the quotient ring. -/
def IsNormallyFlat {X : Scheme} (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, (I.ideal U).IsNormallyFlat

end AlgebraicGeometry.Scheme.IdealSheafData
