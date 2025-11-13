/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 982

*Reference:* [erdosproblems.com/982](https://www.erdosproblems.com/982)
-/

open EuclideanGeometry

namespace Erdos982

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then some vertex has at least
$\lfloor \frac{n}{2}\rfloor$ different distances to other vertices.
-/
@[category research open, AMS 52]
theorem erdos_982 (n : ℕ) (hn : 3 ≤ n) :
    ∀ (p : Fin n → ℝ²), Function.Injective p →
      EuclideanGeometry.IsConvexPolygon p →
      ∃ (i : Fin n),
        { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  sorry

end Erdos982
