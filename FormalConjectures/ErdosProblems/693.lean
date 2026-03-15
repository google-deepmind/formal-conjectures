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
# Erdős Problem 693

Let $k \geq 2$ and $n$ be sufficiently large. Consider the set of integers in $[n, n^k]$ which
have a divisor in the open interval $(n, 2n)$. Is the maximum gap between consecutive elements of
this set at most $(\log n)^{O(1)}$?

See also Problem 446 for a related problem about integers with divisors in $(n, 2n)$.

OEIS: [A391118](https://oeis.org/A391118) (possibly related sequence).

*Reference:* [erdosproblems.com/693](https://www.erdosproblems.com/693)

[Er79e] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. **52** (1979),
67-70.
-/

open Real

namespace Erdos693

/-- An integer $m$ has a divisor in the open interval $(n, 2n)$. -/
def HasDivisorIn (m n : ℕ) : Prop :=
  ∃ d, d ∣ m ∧ n < d ∧ d < 2 * n

/--
Erdős Problem 693 [Er79e]:

Let $k \geq 2$ and $n$ be sufficiently large depending on $k$. Let
$A = \{a_1 < a_2 < \cdots\}$ be the set of integers in $[n, n^k]$ which have a divisor
in $(n, 2n)$. Is the maximum gap $\max_i (a_{i+1} - a_i) \leq (\log n)^{O(1)}$?
-/
@[category research open, AMS 11]
theorem erdos_693 :
    answer(sorry) ↔
    ∀ k : ℕ, k ≥ 2 →
    ∃ C : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ a b : ℕ, n ≤ a → a < b → b ≤ n ^ k →
    HasDivisorIn a n → HasDivisorIn b n →
    (∀ m : ℕ, a < m → m < b → ¬HasDivisorIn m n) →
    (b : ℝ) - (a : ℝ) ≤ (Real.log (n : ℝ)) ^ C := by
  sorry

end Erdos693
