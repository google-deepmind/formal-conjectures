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
# Erdős Problem 1100

*Reference:* [erdosproblems.com/1100](https://www.erdosproblems.com/1100)

If $1 = d_1 < \cdots < d_{\tau(n)} = n$ are the divisors of $n$, let $\tau^\perp(n)$ count the
number of $i$ for which $\gcd(d_i, d_{i+1}) = 1$.

Part 1: Is it true that $\tau^\perp(n)/\omega(n) \to \infty$ for almost all $n$?

Part 2: Is it true that $\tau^\perp(n) < \exp((\log n)^{o(1)})$ for all $n$?
Equivalently, for every $\varepsilon > 0$ and sufficiently large $n$,
$\tau^\perp(n) < \exp((\log n)^\varepsilon)$.

Part 3: Let $g(k) = \max$ over squarefree $n$ with $\omega(n) = k$ of $\tau^\perp(n)$.
Determine the growth of $g(k)$. Erdős and Simonovits proved
$(\sqrt{2} + o(1))^k < g(k) < (2 - c)^k$ for some constant $c > 0$.
-/

open Finset Real

namespace Erdos1100

/-- The sorted list of divisors of $n$ in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- $\tau^\perp(n)$: the number of indices $i$ such that $\gcd(d_i, d_{i+1}) = 1$,
where $d_1 < \cdots < d_{\tau(n)}$ are the divisors of $n$ in increasing order. -/
def tauPerp (n : ℕ) : ℕ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).filter (fun p => Nat.gcd p.1 p.2 == 1)).length

/--
Erdős Problem 1100, Part 1:
Is it true that $\tau^\perp(n)/\omega(n) \to \infty$ for almost all $n$? That is, for every
bound $M$, the natural density of $\{n : \tau^\perp(n) \le M \cdot \omega(n)\}$ is zero.
-/
@[category research open, AMS 11]
theorem erdos_1100 :
    answer(sorry) ↔
      ∀ M : ℕ, ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          (((Finset.range N).filter (fun n =>
            tauPerp n ≤ M * n.primeFactors.card)).card : ℝ) / (N : ℝ) < ε := by
  sorry

/--
Erdős Problem 1100, Part 2:
Is it true that for every $\varepsilon > 0$, for all sufficiently large $n$,
$\tau^\perp(n) < \exp((\log n)^\varepsilon)$?
This formalizes the conjecture that $\tau^\perp(n) < \exp((\log n)^{o(1)})$.
-/
@[category research open, AMS 11]
theorem erdos_1100.variants.part2 :
    answer(sorry) ↔
      ∀ ε : ℝ, ε > 0 →
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          (tauPerp n : ℝ) < Real.exp ((Real.log (n : ℝ)) ^ ε) := by
  sorry

/--
Erdős Problem 1100, Part 3 (upper bound, proved by Erdős–Simonovits):
There exists $c > 0$ such that for all sufficiently large $k$, every squarefree $n$
with $\omega(n) = k$ satisfies $\tau^\perp(n) < (2 - c)^k$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.part3_upper :
    ∃ c : ℝ, c > 0 ∧
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∀ n : ℕ, Squarefree n → n.primeFactors.card = k →
          (tauPerp n : ℝ) < (2 - c) ^ k := by
  sorry

/--
Erdős Problem 1100, Part 3 (lower bound, proved by Erdős–Simonovits):
For every $\varepsilon > 0$ and sufficiently large $k$, there exists a squarefree $n$ with
$\omega(n) = k$ and $\tau^\perp(n) > (\sqrt{2} - \varepsilon)^k$.
-/
@[category research solved, AMS 11]
theorem erdos_1100.variants.part3_lower :
    ∀ ε : ℝ, ε > 0 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∃ n : ℕ, Squarefree n ∧ n.primeFactors.card = k ∧
          (tauPerp n : ℝ) > ((2 : ℝ) ^ ((1 : ℝ) / 2) - ε) ^ k := by
  sorry

end Erdos1100
