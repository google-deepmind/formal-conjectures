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
# Erdős Problem 177

*Reference:* [erdosproblems.com/177](https://www.erdosproblems.com/177)

Find the smallest $h(d)$ such that there exists a function $f : \mathbb{N} \to \{-1, 1\}$
such that, for every $d \geq 1$,
$$
  \max_{P_d} \left| \sum_{n \in P_d} f(n) \right| \leq h(d),
$$
where $P_d$ ranges over all finite arithmetic progressions with common difference $d$.

Known bounds:
- Lower: $h(d) \gg d^{1/2}$ (Roth [Ro64])
- Upper: $h(d) \leq d^{8+\varepsilon}$ is achievable for every $\varepsilon > 0$ (Beck [Be17])
- Van der Waerden's theorem implies $h(d) \to \infty$.
- Cantor, Erdős, Schreiber, and Straus proved $h(d) \ll d!$.

[Ro64] Roth, K. F., *Remark concerning integer sequences*, Acta Arithmetica 9 (1964), 257–260.

[Be17] Beck, J., *Probabilistic Diophantine Approximation*, Springer Monographs in Mathematics (2017).
-/

open Finset BigOperators Real

namespace Erdos177

/--
Erdős Problem 177: Find the smallest function $h(d)$ such that there exists
a $\pm 1$ coloring $f$ of $\mathbb{N}$ where for every $d \geq 1$, the discrepancy over
any finite arithmetic progression with common difference $d$ is at most $h(d)$.
-/
@[category research open, AMS 5 11]
theorem erdos_177 :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ d : ℕ, 0 < d → ∀ a k : ℕ, 0 < k →
      |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| ≤ (answer(sorry) : ℕ → ℝ) d := by sorry

/--
Erdős Problem 177 — Lower bound (Roth [Ro64]):
For any $\pm 1$ coloring of $\mathbb{N}$ and any $d \geq 1$, there exists a finite arithmetic
progression of common difference $d$ with discrepancy at least $c \cdot \sqrt{d}$.
That is, $h(d) \gg d^{1/2}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_177.variants.lower :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℕ → ℤ,
    (∀ n, f n = 1 ∨ f n = -1) →
    ∀ d : ℕ, 0 < d →
    ∃ a k : ℕ, 0 < k ∧
      c * Real.sqrt (↑d) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| := by
  sorry

/--
Erdős Problem 177 — Upper bound (Beck [Be17]):
For every $\varepsilon > 0$, there exists a $\pm 1$ coloring $f$ of $\mathbb{N}$ such that for every
$d \geq 1$ and every finite arithmetic progression of common difference $d$ with $k$ terms,
$\left| \sum f \right| \leq d^{8+\varepsilon}$. That is, $h(d) \leq d^{8+\varepsilon}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_177.variants.upper :
    ∀ ε : ℝ, 0 < ε →
    ∃ f : ℕ → ℤ,
    (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ d : ℕ, 0 < d → ∀ a k : ℕ, 0 < k →
      |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| ≤ (↑d : ℝ) ^ ((8 : ℝ) + ε) := by
  sorry

end Erdos177
