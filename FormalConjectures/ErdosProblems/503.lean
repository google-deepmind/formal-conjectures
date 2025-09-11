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
theorem erdos_503 {n : ℕ} :
    IsGreatest {m | ∃ A : Set (ℝ^n), isoscelesSet A ∧ A.ncard = m} answer(sorry) := by
  sorry

/--
When $n = 2$, the answer is 6 (due to Kelly
[ErKe47](https://mathscinet.ams.org/mathscinet/relay-station?mr=1526679) - an alternative proof is
given by Kovács [Ko24c](https://arxiv.org/abs/2412.05190)).
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.R2 :
    IsGreatest {m | ∃ A : Set ℝ², isoscelesSet A ∧ A.ncard = m} 6 := by
  sorry

/--
When $n = 3$, the answer is 8 (due to Croft
[Cr62](https://mathscinet.ams.org/mathscinet/relay-station?mr=155230)).
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.R3 :
    IsGreatest {m | ∃ A : Set ℝ³, isoscelesSet A ∧ A.ncard = m} 8 := by
  sorry

/--
The best upper bound known in general is due to Blokhius
[Bl84](https://mathscinet.ams.org/mathscinet/relay-station?mr=751955) who showed that
$$
|A| \leq \binom{n + 2}{2}
$$
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.upper_bound {n : ℕ} :
    ∃ a, IsGreatest {m | ∃ A : Set (ℝ^n), isoscelesSet A ∧ A.ncard = m} a ∧ a ≤ (n + 2).choose 2 := by
  sorry

/--
Alweiss has observed a lower bound of $\binom{n + 1}{2}$ follows from considering the subset of
$\mathbb{R}^{n + 1}$ formed of all vectors $e_i + e_j$ where $e_i$, $e_j$ are distinct coordinate
vectors. This set can be viewed as a subset of some $\mathbb{R}^n$, and is easily checked to have
the required property.
-/
@[category research solved, AMS 51]
theorem erdos_503.variants.lower_bound {n : ℕ} :
    ∃ a, IsGreatest {m | ∃ A : Set (ℝ^n), isoscelesSet A ∧ A.ncard = m} a ∧ (n + 1).choose 2 ≤ a := by
  sorry

end Erdos503
