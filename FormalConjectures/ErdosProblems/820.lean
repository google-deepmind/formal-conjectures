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
# Erdős Problem 820

*Reference:* [erdosproblems.com/820](https://www.erdosproblems.com/820)

Let $H(n)$ be the smallest integer $l \geq 2$ such that there exists $k$ with
$2 \leq k < l$ and $\gcd(k^n - 1, l^n - 1) = 1$.

The sequence $H(n)$ for $1 \leq n \leq 10$ is $3, 3, 3, 6, 3, 18, 3, 6, 3, 12$.
-/

namespace Erdos820

/-- $H(n)$ is the smallest integer $l \geq 2$ such that there exists $k$ with
$2 \leq k < l$ and $\gcd(k^n - 1, l^n - 1) = 1$. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {l : ℕ | 2 ≤ l ∧ ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}

/--
**Erdős Problem 820** — Part 1:

Is it true that $\gcd(2^n - 1, 3^n - 1) = 1$ for infinitely many $n$?
Equivalently, $H(n) = 3$ for infinitely many $n$.
-/
@[category research open, AMS 11]
theorem erdos_820 : answer(sorry) ↔
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ Nat.Coprime (2 ^ n - 1) (3 ^ n - 1) := by
  sorry

/--
**Erdős Problem 820** — Part 2 (lower bound):

Is it true that there exists $c > 0$ such that for all $\varepsilon > 0$,
for infinitely many $n$,
$H(n) > \exp(n^{(c - \varepsilon)/\log\log n})$?
-/
@[category research open, AMS 11]
theorem erdos_820.variants.lower_bound : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    (H n : ℝ) >
      Real.exp ((↑n : ℝ) ^ ((c - ε) / Real.log (Real.log (↑n : ℝ)))) := by
  sorry

/--
**Erdős Problem 820** — Part 3 (upper bound):

Is it true that there exists $c > 0$ such that for all $\varepsilon > 0$,
for all sufficiently large $n$,
$H(n) < \exp(n^{(c + \varepsilon)/\log\log n})$?
-/
@[category research open, AMS 11]
theorem erdos_820.variants.upper_bound : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    (H n : ℝ) <
      Real.exp ((↑n : ℝ) ^ ((c + ε) / Real.log (Real.log (↑n : ℝ)))) := by
  sorry

end Erdos820
