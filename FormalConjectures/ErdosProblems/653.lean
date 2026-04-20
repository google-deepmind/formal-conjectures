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
# Erdős Problem 653

*Reference:* [erdosproblems.com/653](https://www.erdosproblems.com/653)
-/

open Finset EuclideanGeometry Filter

namespace Erdos653

/-- Let $x_1,\ldots,x_n\in \mathbb{R}^2$ and let $R(x_i)=\#\{ \lvert x_j-x_i\rvert : j\neq i\}$,
where the points are ordered such that
\[R(x_1)\leq \cdots \leq R(x_n).\]
Let $g(n)$ be the maximum number of distinct values the $R(x_i)$ can take. Is it true that
$g(n) \geq (1-o(1))n$? -/
@[category research open, AMS 5 52]
theorem erdos_653 : answer(sorry) ↔ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (1 - o n) * n ≤ maximalDistinctDistancesFrom n := by
  sorry

end Erdos653
