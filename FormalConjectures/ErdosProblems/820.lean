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

Erdős proved $H(n) > \exp(n^{c/(\log\log n)^2})$ for infinitely many $n$.
Wouter van Doorn sketched a proof of the stronger bound
$H(n) > \exp(n^{c/\log\log n})$ for infinitely many $n$.

See also: [Problem 770](https://www.erdosproblems.com/770),
[OEIS A263647](https://oeis.org/A263647) (values of $n$ where $\gcd(2^n - 1, 3^n - 1) = 1$).

[Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974), 197-202.
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
**Erdős Problem 820** — Part 2 (asymptotic growth of $H(n)$):

Does there exist a single constant $c > 0$ such that for all $\varepsilon > 0$:
- $H(n) > \exp(n^{(c - \varepsilon)/\log\log n})$ for infinitely many $n$, and
- $H(n) < \exp(n^{(c + \varepsilon)/\log\log n})$ for all sufficiently large $n$?
-/
@[category research open, AMS 11]
theorem erdos_820.variants.asymptotic_growth : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    (∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (H n : ℝ) >
        Real.exp ((↑n : ℝ) ^ ((c - ε) / Real.log (Real.log (↑n : ℝ))))) ∧
    (∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (H n : ℝ) <
        Real.exp ((↑n : ℝ) ^ ((c + ε) / Real.log (Real.log (↑n : ℝ))))) := by
  sorry

/--
**Erdős Problem 820** — Part 3 (dual variant):

Let $K(n)$ be the smallest integer $k \geq 2$ such that $\gcd(k^n - 1, 2^n - 1) = 1$.
Do similar bounds hold for $K(n)$ as conjectured for $H(n)$?
-/
@[category research open, AMS 11]
theorem erdos_820.variants.dual : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    (∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (↑(sInf {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (2 ^ n - 1)}) : ℝ) >
        Real.exp ((↑n : ℝ) ^ ((c - ε) / Real.log (Real.log (↑n : ℝ))))) ∧
    (∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (↑(sInf {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (2 ^ n - 1)}) : ℝ) <
        Real.exp ((↑n : ℝ) ^ ((c + ε) / Real.log (Real.log (↑n : ℝ))))) := by
  sorry

end Erdos820
