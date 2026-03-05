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
# Erdős Problem 1070

*Reference:* [erdosproblems.com/1070](https://www.erdosproblems.com/1070)

Let $f(n)$ be maximal such that, given any $n$ points in $\mathbb{R}^2$, there exist $f(n)$
points such that no two are distance $1$ apart. Estimate $f(n)$. In particular,
is it true that $f(n) \geq n/4$?

In other words, estimate the minimal independence number of a unit distance
graph with $n$ vertices.

The Moser spindle shows $f(n) \leq (2/7)n \approx 0.285n$. Croft [Cr67] gave the
best-known lower bound of $f(n) \geq 0.22936n$. Matolcsi, Ruzsa, Varga, and
Zsámboki [MRVZ23] improved the upper bound to $f(n) \leq (1/4 + o(1))n$.

[Er87b] Erdős, P., _Some problems on number theory, combinatorics and geometry_, 1987.

[Cr67] Croft, H. T., _Incidence incidents_, 1967.

[MRVZ23] Matolcsi, M., Ruzsa, I. Z., Varga, D. A., and Zsámboki, P., 2023.
-/

namespace Erdos1070

/--
**Erdős Problem #1070**, main conjecture [Er87b]:

Is it true that for every $n \geq 1$ and every placement of $n$ points in $\mathbb{R}^2$,
there exists a subset of at least $n/4$ points with no two at distance exactly $1$
(an independent set in the unit distance graph)?
-/
@[category research open, AMS 5 52]
theorem erdos_1070 : answer(sorry) ↔
    ∀ (n : ℕ), n ≥ 1 → ∀ (f : Fin n → EuclideanSpace ℝ (Fin 2)),
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ (n : ℝ) / 4 ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem #1070**, lower bound [Cr67]:

For every $n \geq 1$ and every placement of $n$ points in $\mathbb{R}^2$, there exists a subset
of at least $0.22936n$ points with no two at distance exactly $1$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.lower_bound (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2)) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 22936 / 100000 * (n : ℝ) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem #1070**, upper bound (Moser spindle):

For all sufficiently large $n$, there exists a placement of $n$ points in $\mathbb{R}^2$
such that every independent set in the unit distance graph has size at most
$(2/7)n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.upper_bound :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ 2 / 7 * (n : ℝ) := by
  sorry

end Erdos1070
