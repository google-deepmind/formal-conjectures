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
# Erdős Problem 95

*Reference:* [erdosproblems.com/95](https://www.erdosproblems.com/95)

For $n$ points in $\mathbb{R}^2$ with distance multiplicities $f(u_i)$, the sum
$\sum_i f(u_i)^2 \ll_\varepsilon n^{3+\varepsilon}$ for every $\varepsilon > 0$.
Proved by Guth and Katz (2015) with the stronger bound $O(n^3 \log n)$.
This problem carried a $500 prize. See also Problem 94.

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
Eureka (1992), 44–48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
**164** (1997), 81–85.

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)

[Al63] Altman, E., _On a problem of P. Erdős_. Amer. Math. Monthly 70 (1963), 148–157.

[GuKa15] Guth, L. and Katz, N.H., _On the Erdős distinct distances problem in the plane_.
Ann. of Math. (2) **181** (2015), 155–190.
-/

open scoped Classical

namespace Erdos95

/--
The set of distinct distances determined by a finite point set $P$ in $\mathbb{R}^2$.
-/
noncomputable def distinctDistances (P : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)

/--
The number of ordered pairs $(p, q)$ from $P$ with $p \neq q$ and $\operatorname{dist}(p, q) = d$.
-/
noncomputable def distMultiplicity (P : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = d)).card

/--
Let $x_1, \ldots, x_n \in \mathbb{R}^2$ determine the set of distances $\{u_1, \ldots, u_t\}$.
Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then for all
$\varepsilon > 0$,
$$\sum_i f(u_i)^2 \ll_\varepsilon n^{3+\varepsilon}.$$

This was proved by Guth and Katz (2015) who showed the stronger bound
$\sum_i f(u_i)^2 \ll n^3 \log n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_95 :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧
        ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
          ((distinctDistances P).sum
            (fun d => (distMultiplicity P d) ^ 2) : ℝ) ≤
            C * (P.card : ℝ) ^ ((3 : ℝ) + ε) := by
  sorry

end Erdos95
