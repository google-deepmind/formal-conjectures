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
# Ways to write $n = k + m$ with $p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ all prime

Let $p_j$ denote the $j$-th prime number. The sequence $a(n)$ counts the number of ways to write
$n = k + m$ with $k > 0$ and $m > 0$ such that $p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ are all
prime.

*References:*
- [A237413](https://oeis.org/A237413)
-/

@[expose] public section

namespace OeisA237413

/-- $a(n)$ is the number of ways to write $n = k + m$ with $k > 0$ and $m > 0$ such that
$p_k^2 - 2$, $p_m^2 - 2$, and $p_{p_m}^2 - 2$ are all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    if (Nat.nth Nat.Prime (k - 1) ^ 2 - 2).Prime ∧
       (Nat.nth Nat.Prime (n - k - 1) ^ 2 - 2).Prime ∧
       (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n - k - 1) - 1) ^ 2 - 2).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  simp [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h : Finset.Ico 1 2 = {1} := by decide
  simp only [a, h, Finset.sum_singleton, Nat.reduceSub, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  have h : Finset.Ico 1 3 = {1, 2} := by decide
  simp only [a, h, Finset.sum_insert, Finset.mem_singleton, OfNat.one_ne_ofNat,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceSub, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  have h : Finset.Ico 1 4 = {1, 2, 3} := by decide
  simp only [a, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
    Nat.reduceSub, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_four_eq_eleven]
  decide

set_option maxRecDepth 2000 in
@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  have h : Finset.Ico 1 5 = {1, 2, 3, 4} := by decide
  simp only [a, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
    Nat.reduceSub, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven,
    Nat.nth_prime_six_eq_seventeen]
  decide

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : 0 < a n := by
  sorry

end OeisA237413
