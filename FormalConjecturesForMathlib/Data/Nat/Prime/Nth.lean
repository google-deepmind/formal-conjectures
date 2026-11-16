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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Nth

/-!
# Small values of `Nat.nth Nat.Prime` and primorials of the first $k$ primes

This file extends `Mathlib.Data.Nat.Prime.Nth` with evaluation lemmas for `Nat.nth Nat.Prime`
at small indices and defines `Nat.kthPrimorial k`, the product of the first $k$ prime numbers.
-/

@[expose] public section

namespace Nat

@[simp]
theorem nth_prime_five_eq_thirteen : nth Nat.Prime 5 = 13 :=
  nth_count (show Nat.Prime 13 by decide)

@[simp]
theorem nth_prime_six_eq_seventeen : nth Nat.Prime 6 = 17 :=
  nth_count (show Nat.Prime 17 by decide)

@[simp]
theorem nth_prime_seven_eq_nineteen : nth Nat.Prime 7 = 19 :=
  nth_count (show Nat.Prime 19 by decide)

@[simp]
theorem nth_prime_eight_eq_twentyThree : nth Nat.Prime 8 = 23 :=
  nth_count (show Nat.Prime 23 by decide)

@[simp]
theorem nth_prime_nine_eq_twentyNine : nth Nat.Prime 9 = 29 :=
  nth_count (show Nat.Prime 29 by decide)

@[simp]
theorem nth_prime_ten_eq_thirtyOne : nth Nat.Prime 10 = 31 :=
  nth_count (show Nat.Prime 31 by decide)

@[simp]
theorem nth_prime_eleven_eq_thirtySeven : nth Nat.Prime 11 = 37 :=
  nth_count (show Nat.Prime 37 by decide)

@[simp]
theorem nth_prime_twelve_eq_fortyOne : nth Nat.Prime 12 = 41 :=
  nth_count (show Nat.Prime 41 by decide)

@[simp]
theorem nth_prime_thirteen_eq_fortyThree : nth Nat.Prime 13 = 43 :=
  nth_count (show Nat.Prime 43 by decide)

@[simp]
theorem nth_prime_fourteen_eq_fortySeven : nth Nat.Prime 14 = 47 :=
  nth_count (show Nat.Prime 47 by decide)

/-- The $k$-th primorial $p_k\# = \prod_{i < k} p_{i+1}$, defined as the product of the first $k$
prime numbers. Unlike `_root_.primorial n` (which takes the product of primes $\le n$),
`Nat.kthPrimorial k` is indexed by the number of prime factors $k$. -/
noncomputable def kthPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

@[simp]
theorem kthPrimorial_zero : kthPrimorial 0 = 1 := rfl

theorem kthPrimorial_succ (k : ℕ) :
    kthPrimorial (k + 1) = kthPrimorial k * Nat.nth Nat.Prime k :=
  Finset.prod_range_succ _ k

@[simp]
theorem kthPrimorial_one : kthPrimorial 1 = 2 := by
  simp [kthPrimorial]

@[simp]
theorem kthPrimorial_two : kthPrimorial 2 = 6 := by
  simp [kthPrimorial_succ]

@[simp]
theorem kthPrimorial_three : kthPrimorial 3 = 30 := by
  simp [kthPrimorial_succ]

@[simp]
theorem kthPrimorial_four : kthPrimorial 4 = 210 := by
  simp [kthPrimorial_succ]

@[simp]
theorem kthPrimorial_five : kthPrimorial 5 = 2310 := by
  simp [kthPrimorial_succ]

end Nat
