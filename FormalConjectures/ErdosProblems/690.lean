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
# Erdős Problem 690

Let $d_k(p)$ be the density of those integers whose $k$-th smallest prime factor is $p$.
For each fixed $k \geq 1$, is $d_k(p)$ unimodal in $p$?

*Reference:* [erdosproblems.com/690](https://www.erdosproblems.com/690)

[Er79e] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. 52 (1979), 67-70.
-/

open Filter Finset

open scoped Topology

namespace Erdos690

/-- The sorted list of distinct prime factors of $n$ in increasing order. -/
noncomputable def sortedPrimeFactors (n : ℕ) : List ℕ :=
  (Nat.primeFactors n).sort (· ≤ ·)

/-- The $k$-th smallest prime factor of $n$ (1-indexed).
Returns $0$ if $n$ has fewer than $k$ distinct prime factors. -/
noncomputable def kthSmallestPrimeFactor (n : ℕ) (k : ℕ) : ℕ :=
  (sortedPrimeFactors n).getD (k - 1) 0

/-- Count of positive integers in $\{1, \ldots, N\}$ whose $k$-th smallest prime
factor is $p$. -/
noncomputable def countKthPrimeFactor (k p N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => kthSmallestPrimeFactor (n + 1) k = p)).card

/-- A function on primes is unimodal if there exists a prime $m$ such that
$f$ is non-decreasing on primes $\leq m$ and non-increasing on primes $\geq m$. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, Nat.Prime m ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → q ≤ m → f p ≤ f q) ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → m ≤ p → p ≤ q → f q ≤ f p)

/--
Erdős Problem 690: Let $d_k(p)$ be the density of those integers whose $k$-th smallest
prime factor is $p$. For each fixed $k \geq 1$, is $d_k(p)$ unimodal in $p$?

Erdős believed the answer is negative. Cambie confirmed $d_k(p)$ is unimodal for
$1 \leq k \leq 3$ but not for $4 \leq k \leq 20$.

[Er79e]
-/
@[category research solved, AMS 11]
theorem erdos_690 : answer(False) ↔
    ∀ k : ℕ, k ≥ 1 →
    ∃ d_k : ℕ → ℝ,
      (∀ p : ℕ, Nat.Prime p →
        Filter.Tendsto (fun N : ℕ =>
          (countKthPrimeFactor k p (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
          atTop (nhds (d_k p))) ∧
      IsUnimodalOnPrimes d_k := by
  sorry

end Erdos690
