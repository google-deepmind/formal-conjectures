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
# Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n) - 1)^2$ prime

The sequence $a(n)$ counts the number of primes $p < n$ such that
$\text{prime}(p)^2 + (\text{prime}(n) - 1)^2$ is prime, where $\text{prime}(i)$ denotes the
$i$-th prime number (1-indexed).

*References:*
- [A238585](https://oeis.org/A238585)
- [Problems on combinatorial properties of primes](https://arxiv.org/abs/1402.6641)
  by *Zhi-Wei Sun* (2014)
-/

@[expose] public section

namespace OeisA238585

open Finset

/-- Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n) - 1)^2$ prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ p ∈ Ico 1 n,
    if p.Prime ∧ Nat.Prime (Nat.nth Nat.Prime (p - 1) ^ 2 + (Nat.nth Nat.Prime (n - 1) - 1) ^ 2)
    then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  simp [a]

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  simp only [a, show Ico 1 2 = {1} by decide, Finset.sum_singleton]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  simp only [a, show Ico 1 3 = {1, 2} by decide,
    Finset.sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)),
    Finset.sum_singleton, Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  simp only [a, show Ico 1 4 = {1, 2, 3} by decide,
    Finset.sum_insert (by decide : 1 ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_insert (by decide : 2 ∉ ({3} : Finset ℕ)),
    Finset.sum_singleton, Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_three_eq_seven]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  simp only [a, show Ico 1 5 = {1, 2, 3, 4} by decide,
    Finset.sum_insert (by decide : 1 ∉ ({2, 3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : 2 ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : 3 ∉ ({4} : Finset ℕ)),
    Finset.sum_singleton, Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_four_eq_eleven]
  decide

set_option maxRecDepth 4000 in
@[category test, AMS 11]
theorem a_8 : a 8 = 2 := by
  have hIco : Ico 1 8 = {1, 2, 3, 4, 5, 6, 7} := by decide
  simp only [a, hIco, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
    Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
    Nat.nth_prime_four_eq_eleven, Nat.nth_prime_six_eq_seventeen,
    Nat.nth_prime_seven_eq_nineteen]
  decide

/--
Conjecture (i): $a(n) > 0$ unless $n$ divides $6$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    0 < a n ↔ ¬(n ∣ 6) := by
  sorry

/--
Conjecture (i): $a(n) = 1$ only for
$n \in \{4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44\}$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (n : ℕ) (hn : 0 < n) :
    a n = 1 ↔ n ∈ ({4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44} : Set ℕ) := by
  sorry

/--
Conjecture (ii): If $n > 2$ is not equal to $9$, then
$\text{prime}(n)^2 + (\text{prime}(p) - 1)^2$ is prime for some prime $p < n$.
-/
@[category research open, AMS 11]
theorem conjecture_3 (n : ℕ) (hn : 2 < n) (hn9 : n ≠ 9) :
    ∃ p : ℕ, p < n ∧ p.Prime ∧
      Nat.Prime (Nat.nth Nat.Prime (n - 1) ^ 2 + (Nat.nth Nat.Prime (p - 1) - 1) ^ 2) := by
  sorry

/--
Conjecture (iii), part 1: For $n > 3$, there is a prime $p < n$ with
$\text{prime}(p) + \text{prime}(n) + 1$ prime.
-/
@[category research open, AMS 11]
theorem conjecture_4 (n : ℕ) (hn : 3 < n) :
    ∃ p : ℕ, p < n ∧ p.Prime ∧
      Nat.Prime (Nat.nth Nat.Prime (p - 1) + Nat.nth Nat.Prime (n - 1) + 1) := by
  sorry

/--
Conjecture (iii), part 2: If $n > 9$ is not equal to $18$, then
$\text{prime}(p)^2 + \text{prime}(n)^2 - 1$ is prime for some prime $p < n$.
-/
@[category research open, AMS 11]
theorem conjecture_5 (n : ℕ) (hn : 9 < n) (hn18 : n ≠ 18) :
    ∃ p : ℕ, p < n ∧ p.Prime ∧
      Nat.Prime (Nat.nth Nat.Prime (p - 1) ^ 2 + Nat.nth Nat.Prime (n - 1) ^ 2 - 1) := by
  sorry

end OeisA238585
