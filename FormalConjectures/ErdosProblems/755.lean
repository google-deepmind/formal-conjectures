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
# Erdős Problem 755

*Reference:* [erdosproblems.com/755](https://www.erdosproblems.com/755)

The number of equilateral triangles of size $1$ formed by any set of $n$ points
in $\mathbb{R}^6$ is at most $(1/27 + o(1))n^3$.

A problem of Erdős and Purdy [ErPu75]. Erdős believed the bound should hold
even for equilateral triangles of any size. This was proved in a strong form
by Clemen, Dumitrescu, and Liu [CDL25b].

[ErPu75] Erdős, P. and Purdy, G., _Some extremal problems in geometry_.
Journal of Combinatorial Theory, Series A 10 (1975), 246-252.

[Er94b] Erdős, P., _Some old and new problems in various branches of
combinatorics_. Discrete Mathematics 165/166 (1997), 227-231.

[CDL25b] Clemen, F., Dumitrescu, A., and Liu, Y., _On the number of
equilateral triangles determined by point sets in Euclidean space_.
-/

open Classical

namespace Erdos755

/-- The number of unit equilateral triangles determined by a finite point set
in $d$-dimensional Euclidean space: the number of $3$-element subsets where
all pairwise distances are $1$. -/
noncomputable def unitEquilateralTriangleCount {d : ℕ}
    (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {T : Finset (EuclideanSpace ℝ (Fin d)) |
    T ⊆ A ∧ T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → dist x y = 1}

/--
Erdős Problem 755 [ErPu75][Er94b]:

The number of unit equilateral triangles determined by $n$ points in $\mathbb{R}^6$ is
at most $(1/27 + o(1))n^3$.

Formulated as: for every $\varepsilon > 0$, there exists $N_0$ such that for all $n \geq N_0$
and every set of $n$ points in $\mathbb{R}^6$, the number of unit equilateral triangles
is at most $(1/27 + \varepsilon) \cdot n^3$.
-/
@[category research solved, AMS 52]
theorem erdos_755 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∀ A : Finset (EuclideanSpace ℝ (Fin 6)),
          A.card = n →
          (unitEquilateralTriangleCount A : ℝ) ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 := by
  sorry

end Erdos755
