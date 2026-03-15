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
# Erdős Problem 957

*Reference:* [erdosproblems.com/957](https://www.erdosproblems.com/957)

Let $A \subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1 < \ldots < d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the number of
(unordered) pairs of points at distance $d$. Is it true that
$$f(d_1) f(d_k) \leq \left(\frac{9}{8} + o(1)\right) n^2?$$

A question of Erdős and Pach [ErPa90]. An unpublished construction of Makai
shows that this would be the best possible. Solved by Dumitrescu [Du19], who
proved $f(d_1) f(d_k) \leq \frac{9}{8} n^2 + O(n)$.

See also problems #132 and #756.

[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_,
Combinatorica (1990).

[Du19] Dumitrescu, A., _A product inequality for extreme distances_,
Computational Geometry (2019).
-/

open Classical

namespace Erdos957

/-- The number of unordered pairs of distinct points in $A$ at Euclidean
    distance $d$. Computed as the number of ordered pairs divided by 2. -/
noncomputable def distFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/--
Erdős Problem 957 [ErPa90] (proved by Dumitrescu [Du19]):
For every $\varepsilon > 0$, for all sufficiently large finite point sets
$A \subset \mathbb{R}^2$, the product of the frequency of the minimum distance
and the frequency of the maximum distance satisfies
$f(d_{\min}) \cdot f(d_{\max}) \leq (9/8 + \varepsilon) \cdot |A|^2$.
-/
@[category research solved, AMS 5 52]
theorem erdos_957 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))), N₀ ≤ A.card →
    ∀ d₁ dk : ℝ,
    (∃ p q : EuclideanSpace ℝ (Fin 2), p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ dist p q = d₁) →
    (∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → p ≠ q → d₁ ≤ dist p q) →
    (∃ p q : EuclideanSpace ℝ (Fin 2), p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ dist p q = dk) →
    (∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → dist p q ≤ dk) →
    (distFrequency A d₁ : ℝ) * (distFrequency A dk : ℝ) ≤
      (9 / 8 + ε) * (A.card : ℝ) ^ 2 := by
  sorry

end Erdos957
