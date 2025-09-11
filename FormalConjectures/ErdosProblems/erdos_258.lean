/-
Copyright 2025 Google LLC

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

-- Erdos Problems URL: https://www.erdosproblems.com/258
import FormalConjectures.Util.ProblemImports

/--
Let `a_n → ∞` be a sequence of non-zero natural numbers. Is `∑_n, d(n)/(a_1 ... a_n)` irrational, where `d(n)`
is the number of divisors of `n`?
-/
@[problem_status open]
theorem erdos_258
    (a : ℕ → ℕ) (ha : ∀ n, a n ≠ 0)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Irrational (∑' (n : ℕ), ((n+1).divisors.card / ∏ i in Finset.Icc 1 n, a i)) := by
  sorry


/--
Let `a_n → ∞` be a monotone sequence of non-zero natural numbers. Is `∑_n, d(n)/(a_1 ... a_n)` irrational, where `d(n)`
is the number of divisors of `n`?

Solution: True (proved by Erdős and Straus, see Erdos Problems website).
-/
@[problem_status solved]
theorem erdos_258.variants.Monotone
    (a : ℕ → ℤ) (ha : ∀ n, a n ≠ 0) (ha : Monotone a)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop) :
    Irrational (∑' (n : ℕ), ((n+1).divisors.card / ∏ i in Finset.Icc 1 n, a i)) := by
  sorry


/--
Is `∑_n, d(n)/(t^n)` irrational, where `t ≥ 2` is an integer.

Solution: True (proved by Erdős, see Erdos Problems website)
-/
@[problem_status solved]
theorem erdos_258.variants.Constant (t : ℕ) (ht : 2 ≤ t):
    Irrational (∑' (n : ℕ), ((n+1).divisors.card / t^n)) := by
  sorry
