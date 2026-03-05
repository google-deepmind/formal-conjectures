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
# Erdős Problem 652

*Reference:* [erdosproblems.com/652](https://www.erdosproblems.com/652)

Let $x_1, \ldots, x_n \in \mathbb{R}^2$ and let
$R(x_i) = \#\{ |x_j - x_i| : j \neq i \}$, where the points are ordered such that
$R(x_1) \leq \cdots \leq R(x_n)$.

Let $\alpha_k$ be minimal such that, for all large enough $n$, there exists a set of
$n$ points with $R(x_k) < \alpha_k n^{1/2}$.

Is it true that $\alpha_k \to \infty$ as $k \to \infty$?

This was proved in the affirmative. Mathialagan [Ma21] showed that given sets $P$
($k$ points) and $Q$ ($n$ points) with $2 \leq k \leq n^{1/3}$, some point of $P$
determines $\gg (kn)^{1/2}$ distances to $Q$, implying
$R(x_k) \gg (kn)^{1/2}$ for $2 \leq k \leq n^{1/3}$.

[Ma21] Mathialagan, S., *Distinct distances for points along a curve in the plane*. 2021.
-/

namespace Erdos652

/--
The number of distinct distances from a point $p$ to other points in a finite set
$S \subset \mathbb{R}^2$. That is, $R(p) = \#\{\operatorname{dist}(p, q) : q \in S, q \neq p\}$.
-/
noncomputable def numDistinctDistances (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((S.filter (· ≠ p)).image (dist p)).card

/--
Erdős Problem 652: The conjecture that $\alpha_k \to \infty$ is equivalent to: for every
constant $C > 0$, for all sufficiently large $k$, there are infinitely many $n$ such that
every set of $n$ points in $\mathbb{R}^2$ has fewer than $k$ points with fewer than
$C\sqrt{n}$ distinct distances to the rest of the set.

This was proved in the affirmative by Mathialagan [Ma21].
-/
@[category research solved, AMS 5 52]
theorem erdos_652 :
    answer(True) ↔
      ∀ C : ℝ, C > 0 →
        ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
          ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
            ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n →
              (S.filter (fun p =>
                (numDistinctDistances p S : ℝ) < C * Real.sqrt (↑n))).card < k := by
  sorry

end Erdos652
