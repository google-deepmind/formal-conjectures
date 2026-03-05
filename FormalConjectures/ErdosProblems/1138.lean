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
# Erdős Problem 1138

*Reference:* [erdosproblems.com/1138](https://www.erdosproblems.com/1138)

Is the expected asymptotic formula for the number of primes in short intervals of length
proportional to the maximal prime gap valid? Specifically, for $x/2 < y < x$ and $C > 1$,
is $\pi(y + Cd) - \pi(y) \sim Cd / \log y$, where $d$ is the maximal prime gap below $x$?

[Va99] Vardi, I., 1.3.
-/

namespace Erdos1138

/-- The maximal gap between consecutive primes up to $x$.
For each index $k$ with the $k$-th prime (0-indexed) less than $x$,
compute the gap to the next prime and take the maximum.
Returns $0$ when there are no primes less than $x$. -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  (Finset.range (Nat.primeCounting' x)).sup
    (fun k => Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k)

/--
Erdős Problem 1138 [Va99, 1.3]:

Let $x/2 < y < x$ and $C > 1$. If $d = \max_{p_n < x} (p_{n+1} - p_n)$ is the maximal
prime gap below $x$, where $p_n$ denotes the $n$-th prime, then is it true that
$$\pi(y + Cd) - \pi(y) \sim Cd / \log y?$$

In other words, the expected asymptotic formula for the number of primes in the
interval $[y, y + Cd]$ holds. This is a combination of two well-studied problems:
finding the minimum $h$ for which $\pi(y + h) - \pi(y) \sim h / \log y$, and understanding
the maximal prime gap $d$. The conjectured size of $d$ is $\approx (\log x)^2$, which is far
below the $h$ obtainable even assuming the Riemann hypothesis.
-/
@[category research open, AMS 11]
theorem erdos_1138 : answer(sorry) ↔
    ∀ (C : ℝ), 1 < C → ∀ (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
        ∀ y : ℕ, x < 2 * y → y < x →
          |((Nat.primeCounting (y + ⌊C * (maxPrimeGap x : ℝ)⌋₊) : ℝ) -
            (Nat.primeCounting y : ℝ)) /
            (C * (maxPrimeGap x : ℝ) / Real.log (y : ℝ)) - 1| < ε := by
  sorry

end Erdos1138
