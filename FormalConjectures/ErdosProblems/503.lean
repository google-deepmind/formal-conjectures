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
# Erdős Problem 503

*Reference:* [erdosproblems.com/503](https://www.erdosproblems.com/503)
-/

namespace Erdos503

open scoped EuclideanGeometry

/--
What is the size of the largest $A \subseteq \mathbb{R}^n$ such that every three points from $A$
determine an isosceles triangle? That is, for any three points $x$, $y$, $z$ from $A$, at least two
of the distances $|x - y|$, $|y - z|$, $|x - z|$ are equal.
-/
@[category research open, AMS 51]
theorem erdos_503 (n : ℕ) :
    IsGreatest {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)} answer(sorry) := by
  sorry

/--
When $n = 2$, the answer is 6 (due to Kelly [ErKe47] - an alternative proof is given by Kovács [Ko24c]).

[ErKe47] Erdős, Paul and Kelly, L. M., Elementary Problems and Solutions: Solutions: E735. Amer. Math. Monthly (1947), 227-229.
[Ko24c] Z. Kovács, A note on Erdős's mysterious remark. arXiv:2412.05190 (2024).
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.R2 :
    IsGreatest {(A.ncard) | (A : Set ℝ²) (hA : A.IsIsosceles)} 6 := by
  sorry

/--
When $n = 3$, the answer is 8 (due to Croft [Cr62]).

[Cr62] Croft, H. T., $9$-point and $7$-point configurations in $3$-space. Proc. London Math. Soc. (3) (1962), 400-424.
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.R3 :
    IsGreatest {(A.ncard) | (A : Set ℝ³) (hA : A.IsIsosceles)} 8 := by
  sorry

/--
The best upper bound known in general is due to Blokhius [Bl84] who showed that
$$
|A| \leq \binom{n + 2}{2}
$$

[Bl84] Blokhuis, A., Few-distance sets. (1984), iv+70.
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.upper_bound (n : ℕ) :
    ∀ m ∈ {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)}, m ≤ (n + 2).choose 2 := by
  sorry

/--
Alweiss has observed a lower bound of $\binom{n + 1}{2}$ follows from considering the subset of
$\mathbb{R}^{n + 1}$ formed of all vectors $e_i + e_j$ where $e_i$, $e_j$ are distinct coordinate
vectors. This set can be viewed as a subset of some $\mathbb{R}^n$, and is easily checked to have
the required property.
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.lower_bound (n : ℕ) :
    ∀ m ∈ {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)}, (n + 1).choose 2 ≤ m := by
  sorry

end Erdos503
