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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 93

*References:*
- [erdosproblems.com/93](https://www.erdosproblems.com/93)
- [Al63] Altman, E., *On a problem of P. Erdős*. Amer. Math. Monthly (1963), 148-157.
-/

open EuclideanGeometry

namespace Erdos93

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then they determine at least
$\lfloor \frac{n}{2}\rfloor$ distinct distances.

Solved by Altman [Al63].

We formalise the hypothesis as: $A$ is a finite set of at least three points in $\mathbb{R}^2$
in convex position (`ConvexIndep`), i.e. $A$ is the vertex set of a convex polygon.
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos93.lean"]
theorem erdos_93 (A : Finset ℝ²) (hA_card : 3 ≤ A.card)
    (hA : ConvexIndep (A : Set ℝ²)) :
    A.card / 2 ≤ distinctDistances A := by
  sorry

end Erdos93
