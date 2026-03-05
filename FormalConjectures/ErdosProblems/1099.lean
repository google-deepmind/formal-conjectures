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
# Erdős Problem 1099

*Reference:* [erdosproblems.com/1099](https://www.erdosproblems.com/1099)

Let $1 = d_1 < \cdots < d_{\tau(n)} = n$ be the divisors of $n$, and for $\alpha > 1$ let
$$h_\alpha(n) = \sum_i \left(\frac{d_{i+1}}{d_i} - 1\right)^\alpha.$$

Is it true that $\liminf_{n \to \infty} h_\alpha(n) \ll_\alpha 1$?

Erdős [Er81h] remarks that $n!$ or $\mathrm{lcm}\{1, \ldots, n\}$ would be good candidates.
The $\liminf$ is trivially $\geq 1$ (considering the term $i = 1$).

Proved by Vose [Vo84] who constructed a specific sequence achieving bounded $h_\alpha(n)$.
It remains open whether $n!$ or $\mathrm{lcm}\{1, \ldots, n\}$ satisfy this property.

This resembles the function $G(n) = \sum_i d_i / d_{i+1}$ considered in problem \#673.

[Er81h] Erdős, P., _Some problems and results in number theory_.

[Vo84] Vose, M. D., _Integers with consecutive divisors in small ratio_, J. Number Theory (1984).
-/

open Classical Finset Real

namespace Erdos1099

/-- The sorted list of divisors of $n$ in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- $h_\alpha(n) = \sum_i (d_{i+1}/d_i - 1)^\alpha$ where $d_1 < \cdots < d_{\tau(n)}$ are the
divisors of $n$ in increasing order. -/
noncomputable def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

/--
Erdős Problem 1099 (Proved by Vose [Vo84]):

For every $\alpha > 1$, there exists a constant $C$ (depending on $\alpha$) such that
$h_\alpha(n) \leq C$ for infinitely many $n$, i.e., $\liminf_{n \to \infty} h_\alpha(n)$
is finite.

Formally: for every $\alpha > 1$, there exists $C$ such that for every $N$, there
exists $n \geq N$ with $h_\alpha(n) \leq C$.
-/
@[category research solved, AMS 11]
theorem erdos_1099 : answer(True) ↔
    ∀ α : ℝ, α > 1 → ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ hAlpha α n ≤ C := by
  sorry

end Erdos1099
