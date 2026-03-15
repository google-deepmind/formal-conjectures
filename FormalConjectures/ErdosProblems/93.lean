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

*Reference:* [erdosproblems.com/93](https://www.erdosproblems.com/93)

If $n$ points in $\mathbb{R}^2$ are in convex position (vertices of a convex polygon), then they
determine at least $\lfloor n/2 \rfloor$ distinct distances. Proved by Altman.

[Al63] Altman, E., _On a problem of P. Erdős_. Amer. Math. Monthly 70 (1963), 148-157.
-/

open scoped Classical
open EuclideanGeometry

namespace Erdos93

/--
Erdős Problem 93: If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon, then they
determine at least $\lfloor n/2 \rfloor$ distinct distances. Proved by Altman [Al63].
-/
@[category research solved, AMS 52]
theorem erdos_93
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconv : ConvexIndep (↑A : Set (EuclideanSpace ℝ (Fin 2))))
    (hn : 2 ≤ A.card) :
    A.card / 2 ≤ distinctDistances A := by
  sorry

end Erdos93
