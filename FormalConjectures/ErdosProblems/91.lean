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
# Erdős Problem 91

*Reference:* [erdosproblems.com/91](https://www.erdosproblems.com/91)

For large $n$, is it true that every $n$-point set in $\mathbb{R}^2$ minimizing the number of
distinct distances admits another minimizer of the same size that is not similar to it?

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry
(Siófok, 1985) (1987), 167-177.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467-478.

[Er97e] Erdős, P., _Some problems and results on combinatorial number theory_ (1997).

[Ko24c] Kovács, Z., _A note on Erdős's mysterious remark_. arXiv:2412.05190 (2024).
-/

open Finset Classical EuclideanGeometry

namespace Erdos91

/--
Two finite point sets in $\mathbb{R}^2$ are similar if there exists a map
$f : \mathbb{R}^2 \to \mathbb{R}^2$ that scales all distances by the same positive constant $r$
and maps one set onto the other.
-/
def AreSimilar (A B : Finset ℝ²) : Prop :=
  ∃ (f : ℝ² → ℝ²) (r : ℝ),
    r > 0 ∧
    (∀ x y : ℝ², dist (f x) (f y) = r * dist x y) ∧
    (∀ a, a ∈ A → f a ∈ B) ∧
    (∀ b, b ∈ B → ∃ a ∈ A, f a = b)

/--
Erdős Problem 91 [Er87b, Er90, Er97e]: For sufficiently large $n$, if
$A \subset \mathbb{R}^2$ has $|A| = n$ and minimises the number of distinct distances, then there
exists another minimiser $A'$ of the same cardinality that is not similar to $A$. In other words,
there are at least two non-similar sets that minimise the number of distinct distances.
-/
@[category research open, AMS 52]
theorem erdos_91 : answer(sorry) ↔
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℝ²,
      A.card = n →
      (∀ B : Finset ℝ², B.card = n →
        distinctDistances A ≤ distinctDistances B) →
      ∃ A' : Finset ℝ²,
        A'.card = n ∧
        (∀ B : Finset ℝ², B.card = n →
          distinctDistances A' ≤ distinctDistances B) ∧
        ¬ AreSimilar A A' := by
  sorry

end Erdos91
