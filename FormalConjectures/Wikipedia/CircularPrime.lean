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
# Base-10 Circular Primes

A prime $p$ is *circular* in base $10$ ([OEIS A068652](https://oeis.org/A068652)) when every cyclic
rotation of its fixed-width decimal digit list represents a prime. Every decimal repunit prime
$R_n = (10^n - 1)/9$ (`repunit10`) is automatically circular. Up to $10^{25}$, the
largest known circular prime outside the repunit family is $999331$ (from the cycle of $199933$ in
[OEIS A016114](https://oeis.org/A016114)). Finiteness of circular primes outside the repunits is
conjectured ([OEIS A293663](https://oeis.org/A293663)), while infinitude of circular primes overall
would follow from infinitude of decimal repunit primes.

*References:*
- [Wikipedia: Circular prime](https://en.wikipedia.org/wiki/Circular_prime)
- [OEIS A016114](https://oeis.org/A016114)
- [OEIS A068652](https://oeis.org/A068652)
- [OEIS A293663](https://oeis.org/A293663)
- C. K. Caldwell, *Circular prime*,
  [The Prime Glossary](https://primes.utm.edu/glossary/xpage/CircularPrime.html).
-/

@[expose] public section

namespace CircularPrime

/-- A natural number $p$ is a base-$10$ circular prime if $p$ is prime and every cyclic shift of
its base-$10$ digit list `Nat.digits 10 p` evaluates via `Nat.ofDigits 10` to a prime. -/
def IsCircularPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ k < (Nat.digits 10 p).length, (Nat.ofDigits 10 ((Nat.digits 10 p).rotate k)).Prime

instance instDecidableIsCircularPrime (p : ℕ) : Decidable (IsCircularPrime p) := by
  unfold IsCircularPrime
  infer_instance

/-- Every decimal repunit prime is a base-$10$ circular prime. -/
@[category API, AMS 11]
theorem isCircularPrime_of_repunit10_prime {n : ℕ} (hp : (repunit10 n).Prime) :
    IsCircularPrime (repunit10 n) :=
  ⟨hp, fun k _ => by
    rw [digits_repunit10, List.rotate_replicate, ← digits_repunit10, Nat.ofDigits_digits]
    exact hp⟩

@[category test, AMS 11]
theorem isCircularPrime_two : IsCircularPrime 2 := by
  decide

@[category test, AMS 11]
theorem isCircularPrime_13 : IsCircularPrime 13 := by
  decide

@[category test, AMS 11]
theorem isCircularPrime_37 : IsCircularPrime 37 := by
  decide

@[category test, AMS 11]
theorem isCircularPrime_79 : IsCircularPrime 79 := by
  decide

@[category test, AMS 11]
theorem isCircularPrime_repunit10_two : IsCircularPrime (repunit10 2) := by
  decide

/-- The circular prime $13$ is not equal to any decimal repunit. -/
@[category test, AMS 11]
theorem thirteen_ne_repunit10 : ¬ ∃ n : ℕ, 13 = repunit10 n := by
  rintro ⟨n, hn⟩
  have hlen := congrArg List.length (congrArg (Nat.digits 10) hn)
  rw [digits_repunit10, List.length_replicate] at hlen
  have hn2 : n = 2 := hlen.symm.trans (by decide)
  subst hn2
  revert hn
  decide

/-- Negative witness: $23$ rotates to $32$. -/
@[category test, AMS 11]
theorem not_isCircularPrime_23 : ¬ IsCircularPrime 23 := by
  decide

/-- Negative witness: $101$ rotates to $110$. -/
@[category test, AMS 11]
theorem not_isCircularPrime_101 : ¬ IsCircularPrime 101 := by
  decide

/-- Negative witness: $1013$ rotates via $0131$ to $1310$ (whereas iteratively dropping leading
zeros would enter $\{131, 311, 113\}$). -/
@[category test, AMS 11]
theorem not_isCircularPrime_1013 : ¬ IsCircularPrime 1013 := by
  intro h
  have hd : Nat.digits 10 1013 = [3, 1, 0, 1] := by norm_num
  have hrot := h.2 2 (by rw [hd]; decide)
  rw [hd] at hrot
  norm_num [List.rotate, Nat.ofDigits] at hrot

/-- Negative witness: $R_3 = 111$ is composite. -/
@[category test, AMS 11]
theorem not_isCircularPrime_repunit10_three : ¬ IsCircularPrime (repunit10 3) := by
  decide

/--
Only finitely many base-$10$ circular primes are not decimal repunits $R_n = (10^n - 1) / 9$.
-/
@[category research open, AMS 11]
theorem non_repunit_circular_primes_finite :
    {p : ℕ | IsCircularPrime p ∧ ¬ ∃ n : ℕ, p = repunit10 n}.Finite := by
  sorry

/--
Infinitely many base-$10$ circular primes exist.
-/
@[category research open, AMS 11]
theorem circular_primes_infinite :
    {p : ℕ | IsCircularPrime p}.Infinite := by
  sorry

end CircularPrime
