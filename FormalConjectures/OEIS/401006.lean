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
# Decimal concatenation of a cofactor and the largest prime factor

For a composite positive integer $n$, let $p$ be its largest prime factor. The sequence value
$a(n)$ concatenates the decimal representations of $n/p$ and $p$, in that order. It fixes primes
and one, and is extended here by $a(0)=0$.

*References:*
- [OEIS A401006](https://oeis.org/A401006)
-/

@[expose] public section

namespace OeisA401006

/-- The number of decimal digits of a natural number, counting zero as one digit. -/
def decimalDigitCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else (Nat.digits 10 n).length

/-- Append the decimal digits of `b` to those of `a`. -/
def decimalAppend (a b : ℕ) : ℕ :=
  a * 10 ^ decimalDigitCount b + b

/-- Zero, one, and primes are fixed; a composite number is replaced by its
cofactor after removing one largest prime factor, followed by that prime factor in decimal. -/
def a (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else if n.Prime then n
  else decimalAppend (n / n.maxPrimeFac) n.maxPrimeFac

/-- Zero is the artificial fixed point outside the official OEIS indexing. -/
@[category API, AMS 11]
theorem a_zero : a 0 = 0 := by
  simp [a]

/-- One is a fixed point. -/
@[category API, AMS 11]
theorem a_one : a 1 = 1 := by
  simp [a]

/-- Every prime is a fixed point. -/
@[category API, AMS 11]
theorem a_prime {p : ℕ} (hp : p.Prime) : a p = p := by
  simp [a, hp, not_le_of_gt hp.one_lt]

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  exact a_zero

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  exact a_one

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_4 : a 4 = 22 := by
  norm_num [a, decimalAppend, decimalDigitCount, Nat.maxPrimeFac,
    Nat.primeFactorsList, List.getLastI]

@[category test, AMS 11]
theorem a_5 : a 5 = 5 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_6 : a 6 = 23 := by
  norm_num [a, decimalAppend, decimalDigitCount, Nat.maxPrimeFac,
    Nat.primeFactorsList, List.getLastI]

@[category test, AMS 11]
theorem a_7 : a 7 = 7 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_8 : a 8 = 42 := by
  norm_num [a, decimalAppend, decimalDigitCount, Nat.maxPrimeFac,
    Nat.primeFactorsList, List.getLastI]

@[category test, AMS 11]
theorem a_44 : a 44 = 411 := by
  norm_num [a, decimalAppend, decimalDigitCount, Nat.maxPrimeFac,
    Nat.primeFactorsList, List.getLastI]

/-- Decimal append is larger than the corresponding product when both inputs are positive. -/
@[category API, AMS 11]
theorem mul_lt_decimal_append {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    x * y < decimalAppend x y := by
  have hypow : y < 10 ^ decimalDigitCount y := by
    simpa [decimalDigitCount, hy.ne'] using
      (Nat.lt_base_pow_length_digits (b := 10) (m := y) (by norm_num))
  exact (Nat.mul_lt_mul_of_pos_left hypow hx).trans (Nat.lt_add_of_pos_right hy)

/-- Applying $a$ to a composite integer above one strictly increases its value. -/
@[category API, AMS 11]
theorem lt_a_of_not_prime {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) : n < a n := by
  have hp : n.maxPrimeFac.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq : 0 < n / n.maxPrimeFac := Nat.div_pos Nat.maxPrimeFac_le hp.pos
  have hlt := mul_lt_decimal_append hq hp.pos
  rw [Nat.div_mul_cancel Nat.maxPrimeFac_dvd] at hlt
  simpa [a, not_le.mpr hn, hprime] using hlt

/-- A starting value reaches a prime after finitely many iterations of $a$. -/
def ReachesPrime (n : ℕ) : Prop :=
  ∃ k : ℕ, ((a^[k]) n).Prime

/-- Zero never reaches a prime under iteration. -/
@[category test, AMS 11]
theorem not_reaches_prime_zero : ¬ ReachesPrime 0 := by
  rintro ⟨k, hk⟩
  rw [Function.iterate_fixed a_zero k] at hk
  exact Nat.not_prime_zero hk

/-- One never reaches a prime under iteration. -/
@[category test, AMS 11]
theorem not_reaches_prime_one : ¬ ReachesPrime 1 := by
  rintro ⟨k, hk⟩
  rw [Function.iterate_fixed a_one k] at hk
  exact Nat.not_prime_one hk

set_option maxRecDepth 10000 in
/-- The orbit starting from $49$ reaches the prime $131321$ after seven steps. -/
@[category test, AMS 11]
theorem reaches_prime_49 : ReachesPrime 49 := by
  refine ⟨7, ?_⟩
  norm_num [Function.iterate_succ_apply, a, decimalAppend, decimalDigitCount,
    Nat.maxPrimeFac, Nat.primeFactorsList, List.getLastI]

/--
"Conjecture: if we start at n >= 2, and repeatedly apply the map k -> a(k), we will eventually
reach a prime, which is then a fixed point."

— [OEIS A401006](https://oeis.org/A401006)
-/
@[category research open, AMS 11]
theorem eventually_prime : ∀ n : ℕ, 2 ≤ n → ReachesPrime n := by
  sorry

end OeisA401006
