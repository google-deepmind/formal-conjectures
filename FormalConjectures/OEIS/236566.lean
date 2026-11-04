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
# Ordered ways to write $2n = p + q$ with $p, q$ and $p_{p+2} + 2$ all prime

Let $p_k$ denote the $k$-th prime number. The sequence $a(n)$ counts the number of ordered ways to
write $2n = p + q$ with $p, q$, and $p_{p+2} + 2$ all prime.

*References:*
- [A236566](https://oeis.org/A236566)
-/

@[expose] public section

namespace OeisA236566

/-- $a(n)$ is the number of ordered ways to write $2n = p + q$ with $p, q$ and
$\operatorname{prime}(p + 2) + 2$ all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.range (2 * n),
    if p.Prime ∧ (2 * n - p).Prime ∧ (Nat.nth Nat.Prime (p + 1) + 2).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  have h : Finset.range 2 = {0, 1} := by decide
  simp only [a, Nat.reduceMul, h, Finset.sum_insert, Finset.mem_singleton,
    zero_ne_one, not_false_eq_true, Finset.sum_singleton]
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  have h : Finset.range 4 = {0, 1, 2, 3} := by decide
  simp only [a, Nat.reduceMul, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    zero_ne_one, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceAdd, Nat.nth_prime_three_eq_seven]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h : Finset.range 6 = {0, 1, 2, 3, 4, 5} := by decide
  simp only [a, Nat.reduceMul, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    zero_ne_one, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceAdd, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_four_eq_eleven]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  have h : Finset.range 8 = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
  simp only [a, Nat.reduceMul, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    zero_ne_one, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceAdd, Nat.nth_prime_four_eq_eleven,
    Nat.nth_prime_six_eq_seventeen]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by
  have h : Finset.range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  simp only [a, Nat.reduceMul, h, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    zero_ne_one, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceAdd, Nat.nth_prime_four_eq_eleven,
    Nat.nth_prime_six_eq_seventeen, Nat.nth_prime_eight_eq_twentyThree]
  decide

/--
Conjecture: (i) $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 2 < n) : 0 < a n := by
  sorry

/--
Conjecture: (ii) If $n > 30$, then $2n + 1$ can be written as $2p + q$ with $p$, $q$ and
$\operatorname{prime}(p + 2) + 2$ all prime.
-/
@[category research open, AMS 11]
theorem conjecture_2 (n : ℕ) (hn : 30 < n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (Nat.nth Nat.Prime (p + 1) + 2).Prime ∧
      2 * n + 1 = 2 * p + q := by
  sorry

end OeisA236566
