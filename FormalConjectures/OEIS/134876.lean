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
module

public import FormalConjecturesUtil

/-!
# Number of Proth primes with a fixed exponent

For a positive integer $n$, count the odd integers $k < 2^n$ for which $k2^n+1$ is prime.
These counts form OEIS A134876.

*References:*
- [A134876](https://oeis.org/A134876)
-/

@[expose] public section

namespace OeisA134876

/-- The number of odd $k < 2^n$ such that $k2^n+1$ is prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n)).filter fun k => k % 2 = 1 ∧ (k * 2 ^ n + 1).Prime).card

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide +kernel

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by decide +kernel

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

/-- The two candidates at exponent two are $5$ and $13$. -/
@[category test, AMS 11]
theorem candidates_at_two :
    ((Finset.range (2 ^ 2)).filter fun k => k % 2 = 1 ∧ (k * 2 ^ 2 + 1).Prime) =
      {1, 3} := by decide

/-- The unique candidate at exponent three is $41$. -/
@[category test, AMS 11]
theorem candidates_at_three :
    ((Finset.range (2 ^ 3)).filter fun k => k % 2 = 1 ∧ (k * 2 ^ 3 + 1).Prime) =
      {5} := by decide

@[category test, AMS 11]
theorem a_le_two_pow (n : ℕ) : a n ≤ 2 ^ n := by
  simpa only [a, Finset.card_range] using
    Finset.card_filter_le (Finset.range (2 ^ n))
      (fun k => k % 2 = 1 ∧ (k * 2 ^ n + 1).Prime)

/--
"Conjecture: $a(n) \sim C \cdot 2^n / n$, where $C = 1/(2 \log 2) = 0.7213475\ldots$"
-/
@[category research open, AMS 11]
theorem proth_prime_count_asymptotic :
    Filter.Tendsto (fun n : ℕ =>
      (a n : ℝ) / ((2 : ℝ) ^ n / (2 * Real.log 2 * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  sorry

end OeisA134876
