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

public import FormalConjecturesUtil

/-!
# The Bing-Borsuk Conjecture

The Bing-Borsuk conjecture states that every $n$-dimensional homogeneous Euclidean neighborhood
retract is a topological $n$-manifold [HR2008, Section 1]. We use its formulation for locally
compact separable metric absolute neighborhood retracts.

The conjecture has been verified in dimensions $1$ and $2$ but remains open in higher dimensions.
A notable consequence is that if the $3$-dimensional case is true, it implies the Poincaré
conjecture.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Bing%E2%80%93Borsuk_conjecture)
 - [HR2008] Halverson, Denise M., and Dušan Repovš. "The Bing-Borsuk and the Busemann
   conjectures." Mathematical Communications 13.2 (2008): 163-184.
   https://arxiv.org/abs/0811.0886
-/

@[expose] public section

namespace BingBorsuk

open scoped Manifold
open TopologicalSpace

/--
Every $n$-dimensional locally compact separable metric homogeneous absolute neighborhood retract
is a topological $n$-manifold [HR2008, Sections 1 and 2]. Local compactness and separability are
the domain assumptions of the Euclidean neighborhood retract formulation. Metrizability supplies
the Hausdorff property, so the conclusion only needs a charted-space structure.
-/
@[category research open, AMS 54 57]
theorem bing_borsuk_conjecture (n : ℕ) (X : Type) [TopologicalSpace X] [MetrizableSpace X]
    [LocallyCompactSpace X] [SeparableSpace X] [HomogeneousSpace X]
    [IsAbsoluteNeighborhoodRetract X] :
    HasLebesgueCoveringDimensionEq X n → Nonempty (ChartedSpace (Fin n → ℝ) X) := by
  sorry

end BingBorsuk
