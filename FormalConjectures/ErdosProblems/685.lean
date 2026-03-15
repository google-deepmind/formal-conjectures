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
# Erdős Problem 685

*Reference:* [erdosproblems.com/685](https://www.erdosproblems.com/685)

Let $\varepsilon > 0$ and $n$ be large depending on $\varepsilon$. Is it true that for all
$n^\varepsilon < k \leq n^{1-\varepsilon}$, the number of distinct prime divisors of
$\binom{n}{k}$ is $(1 + o(1)) \cdot k \cdot \sum_{k < p < n} \frac{1}{p}$?
Or perhaps even when $k \geq (\log n)^c$?

[Er79d] Erdős, P., _Some unconventional problems in number theory_. Mathematics Magazine
52 (1979), 67-70.
-/

open Finset Nat BigOperators
open scoped ArithmeticFunction.omega

namespace Erdos685

/-- The sum of reciprocals of primes $p$ with $k < p < n$: $\sum_{k < p < n} \frac{1}{p}$. -/
noncomputable def primeReciprocalSum (k n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter (fun p => k < p ∧ Nat.Prime p), (1 : ℝ) / p

/--
Erdős Problem 685 [Er79d]: For all $\varepsilon \in (0, 1)$ and $\delta > 0$, there exists $N_0$
such that for all $n \geq N_0$ and all $k$ with $n^\varepsilon < k \leq n^{1 - \varepsilon}$,
the number of distinct prime divisors of $\binom{n}{k}$ satisfies:
$$
  |\omega(\binom{n}{k}) - k \cdot \sum_{k < p < n} \frac{1}{p}|
    \leq \delta \cdot k \cdot \sum_{k < p < n} \frac{1}{p}
$$
-/
@[category research open, AMS 11]
theorem erdos_685 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 → ε < 1 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ k : ℕ, (n : ℝ) ^ ε < (k : ℝ) → (k : ℝ) ≤ (n : ℝ) ^ (1 - ε) →
    |(↑(ω (n.choose k)) : ℝ) - ↑k * primeReciprocalSum k n| ≤
      δ * ↑k * primeReciprocalSum k n := by
  sorry

/--
Variant of Erdős Problem 685 [Er79d]: A stronger form asking whether the same asymptotic
$\omega(\binom{n}{k}) = (1 + o(1)) \cdot k \cdot \sum_{k < p < n} \frac{1}{p}$
holds under the weaker lower bound $k \geq (\log n)^c$ for some constant $c > 0$.
This would allow much smaller values of $k$ than the main formulation.
-/
@[category research open, AMS 11]
theorem erdos_685_variant : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ k : ℕ, (Real.log (n : ℝ)) ^ c ≤ (k : ℝ) → (k : ℝ) ≤ (n : ℝ) →
    |(↑(ω (n.choose k)) : ℝ) - ↑k * primeReciprocalSum k n| ≤
      δ * ↑k * primeReciprocalSum k n := by
  sorry

end Erdos685
