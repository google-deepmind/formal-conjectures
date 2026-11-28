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
# The Lih–Wang permanent conjecture

K.-W. Lih and E. T. H. Wang proposed this inequality in *A convexity inequality on the permanent
of doubly stochastic matrices*, Congressus Numerantium 36 (1982), 189–198.

*References:*
* [Udayan and Somasundaram, equation (3)](https://doi.org/10.1515/spma-2024-0006)
* [Open Problems in Numerical Linear Algebra, MI-17](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/matrix-inequalities-and-norms/MI-17)
-/

@[expose] public section

namespace LihWang

/-- Let $A$ be a doubly stochastic matrix of order $n \ge 3$, and let $J$ have every entry
$1/n$. For $1/2 \le t \le 1$, the permanent of $tJ + (1-t)A$ is at most
$t \operatorname{per}(J) + (1-t) \operatorname{per}(A)$. -/
@[category research open, AMS 15]
theorem permanent_convexity (n : ℕ) (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2) 1) :
    let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ ↦ (n : ℝ)⁻¹
    (t • J + (1 - t) • A).permanent ≤ t * J.permanent + (1 - t) * A.permanent := by
  sorry

end LihWang
