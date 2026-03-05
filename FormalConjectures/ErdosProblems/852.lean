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
# Erdős Problem 852

*Reference:* [erdosproblems.com/852](https://www.erdosproblems.com/852)

Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$-th prime. Let $h(x)$ be maximal
such that for some $n < x$ the numbers $d_n, d_{n+1}, \ldots, d_{n+h(x)-1}$ are
all distinct. Estimate $h(x)$.

Brun's sieve implies $h(x) \to \infty$ as $x \to \infty$.

[Er85c] Erdős, P., _Some problems and results on combinatorial number theory_ (1985).
-/

namespace Erdos852

/-- The $n$-th prime (0-indexed): $p_0 = 2$, $p_1 = 3$, etc. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The $n$-th prime gap: $d_n = p_{n+1} - p_n$. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- A run of $k$ consecutive prime gaps starting at position $n$ are all distinct:
$d_n, d_{n+1}, \ldots, d_{n+k-1}$ are pairwise different. -/
def IsDistinctPrimeGapRun (n k : ℕ) : Prop :=
  Function.Injective (fun i : Fin k => primeGap (n + i.val))

/-- $h(x)$: the maximal length of a run of distinct consecutive prime gaps
$d_n, d_{n+1}, \ldots, d_{n+h-1}$ for some $n < x$. -/
noncomputable def h (x : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ n, n < x ∧ IsDistinctPrimeGapRun n k}

/--
**Erdős Problem 852** — Lower bound [Er85c]:

Is it true that there exists a constant $c > 0$ such that for all sufficiently large $x$,
$h(x) > (\log x)^c$?
-/
@[category research open, AMS 11]
theorem erdos_852 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ →
      (h x : ℝ) > (Real.log (x : ℝ)) ^ c := by
  sorry

/--
**Erdős Problem 852** — Upper bound [Er85c]:

Is it true that $h(x) = o(\log x)$, i.e., for every $\varepsilon > 0$ there exists $N_0$
such that for all $x \geq N_0$, $h(x) < \varepsilon \cdot \log(x)$?
-/
@[category research open, AMS 11]
theorem erdos_852.variants.upper_bound : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ →
      (h x : ℝ) < ε * Real.log (x : ℝ) := by
  sorry

end Erdos852
