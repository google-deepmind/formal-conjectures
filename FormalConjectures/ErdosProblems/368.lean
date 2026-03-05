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
# Erdős Problem 368

*Reference:* [erdosproblems.com/368](https://www.erdosproblems.com/368)

How large is the largest prime factor of $n(n+1)$?

Let $F(n)$ be the largest prime factor of $n(n+1)$.

Known results:
- Pólya [Po18] proved $F(n) \to \infty$ as $n \to \infty$
- Mahler [Ma35] showed $F(n) \gg \log \log n$
- Schinzel [Sc67b] observed $F(n) \leq n^{O(1/\log \log \log n)}$ for infinitely many $n$
- Pasten [Pa24b] proved $F(n) \gg (\log \log n)^2 / \log \log \log n$

The conjectured truth is that $F(n) \gg (\log n)^2$ for all $n$, and for every
$\varepsilon > 0$, infinitely many $n$ have $F(n) < (\log n)^{2+\varepsilon}$.
-/

open Real

namespace Erdos368

/-- The largest prime factor of a natural number $n$. Returns $0$ if $n \leq 1$. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- $F(n)$ is the largest prime factor of $n(n+1)$. -/
noncomputable def F368 (n : ℕ) : ℕ := largestPrimeFactor (n * (n + 1))

/--
Erdős Problem 368 — Lower bound conjecture [Er65b, Er76d, ErGr80]:

The largest prime factor $F(n)$ of $n(n+1)$ satisfies $F(n) \gg (\log n)^2$ for all $n$.
That is, there exists $c > 0$ such that $F(n) \geq c \cdot (\log n)^2$ for all sufficiently
large $n$.
-/
@[category research open, AMS 11]
theorem erdos_368 :
    ∃ c : ℝ, 0 < c ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (F368 n : ℝ) ≥ c * (Real.log n) ^ 2 := by
  sorry

/--
Erdős Problem 368 — Upper bound conjecture [Er76d]:

For every $\varepsilon > 0$, there are infinitely many $n$ such that
$F(n) < (\log n)^{2+\varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_368.variants.upper_bound :
    ∀ ε : ℝ, 0 < ε →
    Set.Infinite {n : ℕ | (F368 n : ℝ) < (Real.log n) ^ ((2 : ℝ) + ε)} := by
  sorry

end Erdos368
