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
# Erdős Problem 824

*Reference:* [erdosproblems.com/824](https://www.erdosproblems.com/824)

Let $h(x)$ count the number of integers $1 \le a < b < x$ such that $(a,b) = 1$ and
$\sigma(a) = \sigma(b)$, where $\sigma$ is the sum of divisors function.

Is it true that $h(x) > x^{2-o(1)}$?

Erdős [Er74b] proved that $\limsup h(x)/x = \infty$, and claimed a similar proof for
this problem. A complete proof that $h(x)/x \to \infty$ was provided by Pollack and
Pomerance [PoPo16].

[Er59c] Erdős, P., _Remarks on number theory II. Some problems on the σ function_.
Acta Arith. 5 (1959), 171-177.

[Er74b] Erdős, P., _On abundant-like numbers_. Canad. Math. Bull. 17 (1974), 599-602.

[PoPo16] Pollack, P. and Pomerance, C., _Some problems of Erdős on the sum-of-divisors
function_. Trans. Amer. Math. Soc. Ser. B 3 (2016), 1-26.
-/

open Finset BigOperators Nat

namespace Erdos824

/-- The sum of divisors function $\sigma(n) = \sum_{d \mid n} d$. -/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- $h(x)$ counts the number of pairs of coprime integers $1 \le a < b < x$
with equal sum-of-divisors values. -/
def erdos824_h (x : ℕ) : ℕ :=
  ((Finset.range x ×ˢ Finset.range x).filter
    (fun p => 0 < p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
      sumDivisors p.1 = sumDivisors p.2)).card

/--
Erdős Problem 824 [Er59c, Er74b]:

Is it true that $h(x) > x^{2-o(1)}$? Equivalently, for every $\varepsilon > 0$,
for all sufficiently large $x$, $h(x) > x^{2-\varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_824 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (erdos824_h x : ℝ) > (x : ℝ) ^ ((2 : ℝ) - ε) := by
  sorry

end Erdos824
