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
import Mathlib.Data.Nat.Prime.Nth

/-!
# Conjectures associated with A110854

$a(n) = \mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$,
where $\mathrm{prime}(k)$ is the $k$-th prime number.

*References:*
- [A110854](https://oeis.org/A110854)
-/

namespace OeisA110854

open Nat

/--
The primary defining sequence `a`.
$a(n)$ is $\mathrm{prime}(2n+2) - \mathrm{prime}(2n+1) - \mathrm{prime}(2n) + \mathrm{prime}(2n-1)$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let p (k : ℕ) : ℤ := (Nat.nth Nat.Prime (k - 1)).cast
  if n = 0 then 0
  else p (2 * n + 2) - p (2 * n + 1) - p (2 * n) + p (2 * n - 1)

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  dsimp [a]
  rw [nth_prime_five, Nat.nth_prime_four_eq_eleven, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_two_eq_five]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  dsimp [a]
  rw [nth_prime_seven, nth_prime_six, nth_prime_five, Nat.nth_prime_four_eq_eleven]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  dsimp [a]
  rw [nth_prime_nine, nth_prime_eight, nth_prime_seven, nth_prime_six]
  norm_num

/-- Every prime other than the first one is odd. -/
@[category API, AMS 11]
theorem odd_nth_prime {k : ℕ} (hk : k ≠ 0) : Odd (Nat.nth Nat.Prime k) := by
  have hprime : Nat.Prime (Nat.nth Nat.Prime k) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  refine hprime.odd_of_ne_two ?_
  intro h
  have h2 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime k :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (Nat.pos_of_ne_zero hk)
  rw [Nat.nth_prime_zero_eq_two, h] at h2
  exact lt_irrefl 2 h2

/-- The defining formula for `a`, with the index arithmetic carried out, for `n ≥ 2`. -/
@[category API, AMS 11]
theorem a_add_two (m : ℕ) :
    a (m + 2) = (Nat.nth Nat.Prime (2 * m + 5) : ℤ) - (Nat.nth Nat.Prime (2 * m + 4) : ℤ)
      - (Nat.nth Nat.Prime (2 * m + 3) : ℤ) + (Nat.nth Nat.Prime (2 * m + 2) : ℤ) := by
  have h : ¬ (m + 2 = 0) := by omega
  have e1 : 2 * (m + 2) + 2 - 1 = 2 * m + 5 := by omega
  have e2 : 2 * (m + 2) + 1 - 1 = 2 * m + 4 := by omega
  have e3 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
  have e4 : 2 * m + 3 - 1 = 2 * m + 2 := by omega
  simp only [a, if_neg h, e1, e2, e3, e4]

/--
For `n ≥ 2` all four primes occurring in `a n` are odd, so `a n` is even.
Together with `a 1 = 1` this gives `(a n).natAbs ∈ {1} ∪ 2ℕ` for every `n > 0`.
-/
@[category API, AMS 11]
theorem even_a (m : ℕ) : Even (a (m + 2)) := by
  obtain ⟨j1, hj1⟩ := odd_nth_prime (k := 2 * m + 5) (by omega)
  obtain ⟨j2, hj2⟩ := odd_nth_prime (k := 2 * m + 4) (by omega)
  obtain ⟨j3, hj3⟩ := odd_nth_prime (k := 2 * m + 3) (by omega)
  obtain ⟨j4, hj4⟩ := odd_nth_prime (k := 2 * m + 2) (by omega)
  refine ⟨(j1 : ℤ) - j2 - j3 + j4, ?_⟩
  rw [a_add_two, hj1, hj2, hj3, hj4]
  push_cast
  ring

/--
Do the absolute values cover A004275?

The statement below is *not* that question. [A004275](https://oeis.org/A004275)
is $1$ together with the nonnegative even numbers, whereas the hypothesis here
asks for every $d$ that is an absolute difference of two primes. That hypothesis
is strictly weaker, so the statement below is strictly stronger than the OEIS
comment, and it is false.

Counterexample $d = 3 = |5 - 2|$. Indeed $a(1) = 7 - 5 - 3 + 2 = 1$, and for
$n \ge 2$ the four primes occurring in $a(n)$ are all odd, so $a(n)$ is even.
Hence $|a(n)| \in \{1\} \cup 2\mathbb{N}$ for every $n > 0$, and $3$ is attained
by no term. The same argument refutes every $d = p - 2$ with $p$ an odd prime
greater than $3$, i.e. $d = 5, 9, 11, 15, 17, 21, \ldots$

The OEIS question itself is untouched by this and is stated in
`conjecture.variants.oeis_question`.
-/
@[category research solved, AMS 11]
theorem conjecture : answer(False) ↔
    ∀ d > 0, (∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ d = (p1 - p2 : ℤ).natAbs) →
    ∃ n > 0, d = (a n).natAbs := by
  constructor
  · exact fun h => h.elim
  · intro h
    obtain ⟨n, hn, hd⟩ :=
      h 3 (by norm_num) ⟨5, 2, by norm_num, by norm_num, by norm_num⟩
    by_cases h1 : n = 1
    · subst h1
      rw [a_1] at hd
      simp at hd
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hEven : Even ((a (m + 2)).natAbs) := Int.natAbs_even.mpr (even_a m)
      rw [← hd, Nat.even_iff] at hEven
      omega

/--
Do the absolute values cover A004275?

This is the question asked by the OEIS comment. [A004275](https://oeis.org/A004275)
is $1$ together with the nonnegative even numbers, which is the set
$\{d : d = 1 \lor d \text{ even}\}$. It remains open.
-/
@[category research open, AMS 11]
theorem conjecture.variants.oeis_question : answer(sorry) ↔
    ∀ d : ℕ, (d = 1 ∨ Even d) → ∃ n > 0, d = (a n).natAbs := by
  sorry

end OeisA110854
