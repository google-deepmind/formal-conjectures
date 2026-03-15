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
# Erdős Problem 661

Erdős and Pach asked whether there exist, for all large $n$, point sets
$x_1, \ldots, x_n, y_1, \ldots, y_n \in \mathbb{R}^2$ such that the number of distinct
bipartite distances $d(x_i, y_j)$ is $o(n / \sqrt{\log n})$.

*Reference:* [erdosproblems.com/661](https://www.erdosproblems.com/661)

[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_,
Combinatorica (1990).

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44–48.

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proc. Int. Conf. on Discrete Math. (1997), 527–533.

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)
-/

open Real

namespace Erdos661

/-- The number of distinct bipartite distances between two finite point sets
in $\mathbb{R}^2$, i.e., the number of distinct values $\operatorname{dist}(x, y)$
for $x \in X$, $y \in Y$. -/
noncomputable def bipartiteDistinctDistances
    (X Y : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((X ×ˢ Y).image (fun p => dist p.1 p.2)).card

/--
**Erdős Problem 661** [ErPa90, Er92e, Er97e, Er97f]:

Are there, for all large $n$, some points $x_1, \ldots, x_n, y_1, \ldots, y_n \in \mathbb{R}^2$
such that the number of distinct distances $d(x_i, y_j)$ is $o(n / \sqrt{\log n})$?

Formulated as: for every $\varepsilon > 0$, there exists $N$ such that for all $n \geq N$,
there exist $X, Y \subset \mathbb{R}^2$ with $|X| = n$, $|Y| = n$, and the number of distinct
bipartite distances is at most $\varepsilon \cdot n / \sqrt{\log n}$.
-/
@[category research open, AMS 5 52]
theorem erdos_661 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ X Y : Finset (EuclideanSpace ℝ (Fin 2)),
          X.card = n ∧ Y.card = n ∧
          (bipartiteDistinctDistances X Y : ℝ) ≤
            ε * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
  sorry

end Erdos661
