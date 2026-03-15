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

For $n$ points in $\mathbb{R}^2$, let $R(x_i)$ count the number of distinct distances from
$x_i$ to all other points. Let $g(n)$ be the maximum number of distinct values the $R(x_i)$
can take. Is it true that $g(n) \geq (1 - o(1))n$?

*Reference:* [erdosproblems.com/653](https://www.erdosproblems.com/653)

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proc. Int. Conf. on Discrete Math. (1997), 527–533.
-/

open Finset Classical

namespace Erdos653

/--
For a configuration of $n$ points in the Euclidean plane, $R(x_i)$ counts the number
of distinct distances from $x_i$ to all other points.
-/
noncomputable def distinctDistances (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 2))
    (i : Fin n) : ℕ :=
  ((Finset.univ.filter (· ≠ i)).image (fun j => dist (x i) (x j))).card

/--
For a configuration of $n$ points in the Euclidean plane, the number of distinct
values that $R(x_i)$ takes over all $i$.
-/
noncomputable def numDistinctR (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 2)) : ℕ :=
  (Finset.univ.image (fun i => distinctDistances n x i)).card

/--
Let $x_1, \ldots, x_n \in \mathbb{R}^2$ and
$R(x_i) = \#\{|x_j - x_i| : j \neq i\}$. Order the points so that
$R(x_1) \leq \cdots \leq R(x_n)$. Let $g(n)$ be the maximum number of distinct
values the $R(x_i)$ can take. Is it true that $g(n) \geq (1 - o(1))n$? [Er97e]
-/
@[category research open, AMS 52]
theorem erdos_653 :
    answer(sorry) ↔
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∃ x : Fin n → EuclideanSpace ℝ (Fin 2),
            (numDistinctR n x : ℝ) ≥ (1 - ε) * n := by
  sorry

end Erdos653
