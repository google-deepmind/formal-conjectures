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
# Number of $0 < k < n-2$ with $p = \phi(k) + \phi(n-k)/2 + 1$ and $p_p - p \pm 1$ prime

Let $\phi$ denote Euler's totient function and $p_m$ denote the $m$-th prime number.
The sequence $a(n)$ counts the number of integers $0 < k < n - 2$ such that
$p = \phi(k) + \phi(n-k)/2 + 1$, $p_p - p - 1$, and $p_p - p + 1$ are all prime.

*References:*
- [A236097](https://oeis.org/A236097)
-/

@[expose] public section

namespace OeisA236097

/-- $a(n)$ is the number of integers $0 < k < n-2$ such that $p = \phi(k) + \phi(n-k)/2 + 1$,
$\operatorname{prime}(p) - p - 1$, and $\operatorname{prime}(p) - p + 1$ are all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico 1 (n - 2),
    let p := k.totient + (n - k).totient / 2 + 1
    let pPrime := Nat.nth Nat.Prime (p - 1)
    if p.Prime ∧ (pPrime - p - 1).Prime ∧ (pPrime - p + 1).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  have hIco : Finset.Ico 1 2 = {1} := by decide
  simp only [a, Nat.reduceSub, hIco, Finset.sum_singleton]
  have ht1 : Nat.totient 1 + Nat.totient 3 / 2 + 1 = 3 := by decide
  rw [ht1]
  simp only [Nat.reduceSub, Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  simp only [a, Nat.reduceSub, hIco, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  have ht1 : Nat.totient 1 + Nat.totient 4 / 2 + 1 = 3 := by decide
  have ht2 : Nat.totient 2 + Nat.totient 3 / 2 + 1 = 3 := by decide
  rw [ht1, ht2]
  simp only [Nat.reduceSub, Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_11 : a 11 = 3 := by
  have hIco : Finset.Ico 1 9 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  simp only [a, Nat.reduceSub, hIco, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton]
  have ht1 : Nat.totient 1 + Nat.totient 10 / 2 + 1 = 4 := by decide
  have ht2 : Nat.totient 2 + Nat.totient 9 / 2 + 1 = 5 := by decide
  have ht3 : Nat.totient 3 + Nat.totient 8 / 2 + 1 = 5 := by decide
  have ht4 : Nat.totient 4 + Nat.totient 7 / 2 + 1 = 6 := by decide
  have ht5 : Nat.totient 5 + Nat.totient 6 / 2 + 1 = 6 := by decide
  have ht6 : Nat.totient 6 + Nat.totient 5 / 2 + 1 = 5 := by decide
  have ht7 : Nat.totient 7 + Nat.totient 4 / 2 + 1 = 8 := by decide
  have ht8 : Nat.totient 8 + Nat.totient 3 / 2 + 1 = 6 := by decide
  rw [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]
  simp only [Nat.reduceSub, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven,
    Nat.nth_prime_five_eq_thirteen, Nat.nth_prime_seven_eq_nineteen]
  decide

/--
Conjecture: $a(n) > 0$ for all $n > 31$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 31 < n) : 0 < a n := by
  sorry

end OeisA236097
