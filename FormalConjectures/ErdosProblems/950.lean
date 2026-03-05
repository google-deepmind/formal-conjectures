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
# Erdős Problem 950

*Reference:* [erdosproblems.com/950](https://www.erdosproblems.com/950)

Let $f(n) = \sum_{p < n} \frac{1}{n - p}$, where the sum is over primes $p < n$.

Is it true that $\liminf f(n) = 1$ and $\limsup f(n) = \infty$?
Is it true that $f(n) = o(\log \log n)$?

This function was considered by de Bruijn, Erdős, and Turán, who showed that
$\sum_{n < x} f(n) \sim \sum_{n < x} f(n)^2 \sim x$.

[Er77c] Erdős, P., *Problems and results on number theory and combinatorics*.
-/

namespace Erdos950

/-- The function $f(n) = \sum_{p < n} \frac{1}{n - p}$, summing over primes $p$ less than $n$. -/
noncomputable def f (n : ℕ) : ℝ :=
  ((Finset.range n).filter Nat.Prime).sum (fun p => 1 / ((n : ℝ) - (p : ℝ)))

/--
**Erdős Problem 950** — Part 1 [Er77c]:
Is it true that $\liminf_{n \to \infty} f(n) = 1$?

Equivalently: for every $\varepsilon > 0$,
  (a) $f(n) > 1 - \varepsilon$ for all sufficiently large $n$, and
  (b) $f(n) < 1 + \varepsilon$ for infinitely many $n$.
-/
@[category research open, AMS 11]
theorem erdos_950 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → f n > 1 - ε) ∧
    (∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ f n < 1 + ε) := by
  sorry

/--
**Erdős Problem 950** — Part 2 [Er77c]:
Is it true that $\limsup_{n \to \infty} f(n) = \infty$?

Equivalently: for every $M$, there exist arbitrarily large $n$ with $f(n) > M$.
-/
@[category research open, AMS 11]
theorem erdos_950.variants.limsup : answer(sorry) ↔
    ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ f n > M := by
  sorry

/--
**Erdős Problem 950** — Part 3 [Er77c]:
Is it true that $f(n) = o(\log \log n)$, i.e., $f(n) / \log(\log n) \to 0$ as $n \to \infty$?
-/
@[category research open, AMS 11]
theorem erdos_950.variants.little_o : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      f n < ε * Real.log (Real.log (n : ℝ)) := by
  sorry

end Erdos950
