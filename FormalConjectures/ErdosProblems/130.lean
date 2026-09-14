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

import FormalConjecturesUtil

/-!
# Erdős Problem 130

*Reference:* [erdosproblems.com/130](https://www.erdosproblems.com/130)
-/

namespace Erdos130

open EuclideanGeometry SimpleGraph

/--
Let $A\subset\mathbb{R}^2$ be an infinite set which contains no three points on a
line and no four points on a circle. Consider the graph with vertices the points
in $A$, where two vertices are joined by an edge if and only if they are an
integer distance apart. How large can the chromatic number and clique number of
this graph be? In particular, can the chromatic number be infinite?

The chromatic number can be infinite: there is an infinite general-position set
whose integer-distance graph admits no finite proper colouring. How large the
*clique* number can be is not addressed here.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/williamjblair/lean-proofs/blob/4f915a323443bfb1709a6805a013812016dca88a/starfleet/erdos-130/Research/Basic.lean"]
theorem erdos_130 :
    answer(True) ↔
      ∃ A : Set ℝ², A.Infinite ∧ InGeneralPosition A ∧
        (IntegerDistancePlaneGraph A).chromaticNumber = ⊤ := by
  sorry

end Erdos130
