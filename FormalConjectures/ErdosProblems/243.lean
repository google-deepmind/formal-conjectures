/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Erdős Problem 243

*References:*
- [erdosproblems.com/243](https://www.erdosproblems.com/243)
- [Koi25] Koizumi, J., Irrationality of the reciprocal sum of doubly exponential
  sequences. arXiv:2504.05933 (2025).
-/

open Filter

open scoped Topology

namespace Erdos243

/--
Let $a_1 < a_2 < \dots$ be a sequence of integers such that
$\lim_{n\to\infty} \frac{a_n}{a_{n-1}^2} = 1$ and $\sum \frac{1}{a_n} \in \mathbb{Q}$.

Then, for all sufficiently large $n \ge 1$, $a_n = a_{n-1}^2 - a_{n-1} + 1$.
-/
@[category research open, AMS 40]
theorem erdos_243 (a : ℕ → ℕ) (ha₀ : StrictMono a)
    (ha₁ : Tendsto (fun n ↦ (a n : ℝ) / a (n - 1) ^ 2) atTop (𝓝 1))
    (ha₂ : Summable ((1 : ℚ) / a ·)) :
      ∀ᶠ n in atTop, a n = a (n - 1) ^ 2 - a (n - 1) + 1 := by
  sorry

/--
Sylvester's sequence satisfies the recurrence appearing in the conclusion of
`erdos_243`, so `erdos_243` asks whether every sequence meeting its hypotheses is
eventually a shifted Sylvester sequence.
-/
@[category test, AMS 11]
theorem erdos_243.sylvester_satisfies_recurrence (n : ℕ) :
    Nat.sylvester (n + 1) = Nat.sylvester n ^ 2 - Nat.sylvester n + 1 :=
  Nat.sylvester_succ n

/--
Koizumi [Koi25, Corollary 2] proved that the two-sided bound
$2/3 \leq a_n^2/a_{n+1} \leq 4/3$ together with $\sum 1/a_n = 1$ determines the
sequence completely: it must be Sylvester's sequence $2, 3, 7, 43, 1807, \dots$.

Compare `erdos_243`, which assumes the ratio *tends to* $1$ and only that the sum is
rational, and asks for the Sylvester recurrence eventually. Here the ratio hypothesis
is a bound rather than a limit, the sum is pinned to $1$, and the conclusion is exact
equality at every index.
-/
@[category research solved, AMS 11]
theorem erdos_243.variants.sylvester_of_tsum_eq_one (a : ℕ → ℕ)
    (ha : ∀ n, 0 < a n)
    (hlb : ∀ n, 2 / 3 ≤ (a n : ℝ) ^ 2 / a (n + 1))
    (hub : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 4 / 3)
    (hsum : ∑' n, (1 : ℝ) / a n = 1) :
    ∀ n, a n = Nat.sylvester n := by
  sorry

/--
Koizumi [Koi25, Corollary 3] proved the companion characterisation for the Millin
series: the one-sided bound $a_n^2/a_{n+1} \leq 2/3$ together with
$\sum 1/a_n = (5 - \sqrt{5})/2$ forces $a_n = F_{2^n}$, where $F$ is the Fibonacci
sequence, so that
$$\frac{5 - \sqrt 5}{2} = \frac11 + \frac13 + \frac1{21} + \frac1{987} + \cdots.$$
-/
@[category research solved, AMS 11]
theorem erdos_243.variants.fib_of_tsum_eq_millin (a : ℕ → ℕ)
    (ha : ∀ n, 0 < a n)
    (hub : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hsum : ∑' n, (1 : ℝ) / a n = (5 - Real.sqrt 5) / 2) :
    ∀ n, a n = Nat.fib (2 ^ (n + 1)) := by
  sorry

end Erdos243
