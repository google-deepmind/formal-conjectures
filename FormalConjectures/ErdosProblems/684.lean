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
# Erdős Problem 684

*Reference:* [erdosproblems.com/684](https://www.erdosproblems.com/684)

For $0 \le k \le n$ write $\binom{n}{k} = uv$ where the only primes dividing $u$ are in $[2,k]$
and the only primes dividing $v$ are in $(k,n]$. Let $f(n)$ be the smallest $k$ such
that $u > n^2$. Give bounds for $f(n)$.

Mahler's theorem implies $f(n) \to \infty$ as $n \to \infty$, but is ineffective and gives
no explicit bounds. Tang proved $f(n) \le n^{30/43 + o(1)}$.
A heuristic suggests $f(n) \sim 2 \log n$ for most $n$.

[Er79d] Erdős, P., _Problems and results on number theoretic properties of consecutive integers
and related questions_. Proceedings of the Fifth Manitoba Conference on Numerical Mathematics
(1975), Congress. Numer. XVI (1976), 25-44.
-/

open Nat Finset BigOperators Classical

namespace Erdos684

/-- The $k$-smooth part of a natural number $m$: the product of $p^{v_p(m)}$ over
all primes $p \le k$. This is the largest divisor of $m$ whose prime factors
are all at most $k$. -/
noncomputable def smoothPart (m k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p ^ (m.factorization p)

/-- $f(n)$ for Erdős Problem 684: the smallest $k$ such that the $k$-smooth part
of $\binom{n}{k}$ exceeds $n^2$. Returns $0$ if no such $k$ exists. -/
noncomputable def erdos684F (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, smoothPart (n.choose k) k > n ^ 2
  then Nat.find h
  else 0

/--
Erdős Problem 684 [Er79d]: $f(n) \to \infty$ as $n \to \infty$.

For every bound $K$, for all sufficiently large $n$, the smallest $k$ such that the
$k$-smooth part of $\binom{n}{k}$ exceeds $n^2$ is greater than $K$.

This follows from Mahler's theorem. The problem asks for effective bounds
on the growth of $f(n)$.
-/
@[category research solved, AMS 11]
theorem erdos_684 :
    ∀ K : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → erdos684F n > K := by
  sorry

/--
Erdős Problem 684, upper bound (Tang):

$f(n) \le n^{30/43 + o(1)}$. For every $\varepsilon > 0$, for all sufficiently large $n$,
$f(n) \le n^{30/43 + \varepsilon}$.
-/
@[category research solved, AMS 11]
theorem erdos_684.variants.upper_bound :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos684F n : ℝ) ≤ (n : ℝ) ^ ((30 : ℝ) / 43 + ε) := by
  sorry

end Erdos684
