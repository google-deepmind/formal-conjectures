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

import FormalConjecturesUtil

/-!
# Integers $0 < k < n$ with $p = k + \mathrm{prime}(n - k)$ and $\mathrm{prime}(p) - p + 1$ prime

*References:*
- [A234694](https://oeis.org/A234694)
-/

namespace OeisA234694

/--
The primary defining sequence `a`.
$a(n)$ is the number of integers $0 < k < n$ such that $p = k + \mathrm{prime}(n - k)$
and $\mathrm{prime}(p) - p + 1$ are both prime, where $\mathrm{prime}(m)$ denotes the $m$-th prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 n,
    let p := k + Nat.nth Nat.Prime (n - k - 1)
    if p.Prime ∧ Nat.Prime (Nat.nth Nat.Prime (p - 1) - p + 1) then 1 else 0

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 :=
  Nat.nth_count (by decide : (13).Prime)

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 :=
  Nat.nth_count (by decide : (17).Prime)

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 :=
  Nat.nth_count (by decide : (19).Prime)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  simp [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have hIco : Finset.Ico 1 2 = {1} := by decide
  simp only [a, hIco, Finset.sum_singleton, Nat.reduceSub, Nat.reduceAdd,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  simp only [a, hIco, Finset.sum_insert, Finset.mem_singleton, OfNat.one_ne_ofNat,
    not_false_eq_true, Finset.sum_singleton, Nat.reduceSub, Nat.reduceAdd,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_three_eq_seven]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  have hIco : Finset.Ico 1 4 = {1, 2, 3} := by decide
  simp only [a, hIco, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
    Nat.reduceSub, Nat.reduceAdd, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_four_eq_eleven, nth_prime_five]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  have hIco : Finset.Ico 1 5 = {1, 2, 3, 4} := by decide
  simp only [a, hIco, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
    Nat.reduceSub, Nat.reduceAdd, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, nth_prime_five,
    nth_prime_six, nth_prime_seven]
  decide

/--
Conjecture (i): $a(n) > 0$ for all $n > 9$. Also, for any integer $n > 51$ there is a positive
integer $k < n$ such that $p = k + \mathrm{prime}(n - k)$ and $\mathrm{prime}(p) + p + 1$ are
both prime.
-/
@[category research open, AMS 11]
theorem conjecture1 :
    (∀ n : ℕ, 9 < n → 0 < a n) ∧
    (∀ n : ℕ, 51 < n → ∃ k, 0 < k ∧ k < n ∧
      let p := k + Nat.nth Nat.Prime (n - k - 1)
      p.Prime ∧ Nat.Prime (Nat.nth Nat.Prime (p - 1) + p + 1)) := by
  sorry

/--
Conjecture (ii): If $n > 9$ (or $n > 21$), then there is a positive integer $k < n$ such that
$m - 1$ and $\mathrm{prime}(m) + m$ (or $\mathrm{prime}(m) - m$, respectively) are both prime,
where $m = k + \mathrm{prime}(n - k)$.
-/
@[category research open, AMS 11]
theorem conjecture2 :
    (∀ n : ℕ, 9 < n → ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (m - 1) ∧ Nat.Prime (Nat.nth Nat.Prime (m - 1) + m)) ∧
    (∀ n : ℕ, 21 < n → ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (m - 1) ∧ Nat.Prime (Nat.nth Nat.Prime (m - 1) - m)) := by
  sorry

/--
Conjecture (iii): If $n > 483$, then for some $0 < k < n$ both $\mathrm{prime}(m) + m$
and $\mathrm{prime}(m) - m$ are prime, where $m = k + \mathrm{prime}(n - k)$.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : 483 < n) :
    ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (Nat.nth Nat.Prime (m - 1) + m) ∧
      Nat.Prime (Nat.nth Nat.Prime (m - 1) - m) := by
  sorry

/--
Conjecture (iv): If $n > 3$, then there is a positive integer $k < n$ such that
$\mathrm{prime}(k + \mathrm{prime}(n - k)) + 2$ is prime.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : 3 < n) :
    ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (Nat.nth Nat.Prime (m - 1) + 2) := by
  sorry

end OeisA234694
