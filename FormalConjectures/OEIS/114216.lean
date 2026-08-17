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
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Largest odd divisor of $a(n-1) + \textrm{prime}(n)$

$a(0)=0$; thereafter $a(n)$ = largest odd divisor of $a(n-1) + \textrm{prime}(n)$.

*References:*
- [A114216](https://oeis.org/A114216)
-/

namespace OeisA114216

/--
The primary defining sequence `a`.
$a(n)$ is the largest odd divisor of $a(n-1) + \textrm{prime}(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 =>
    let pN : ℕ := Nat.nth Nat.Prime n'
    let prevA : ℕ := a n'
    let sumVal : ℕ := prevA + pN
    let nu2 : ℕ := padicValNat 2 sumVal
    sumVal / (2 ^ nu2)

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  change (0 + Nat.nth Nat.Prime 0) / 2 ^ padicValNat 2 (0 + Nat.nth Nat.Prime 0) = 1
  rw [Nat.nth_prime_zero_eq_two, padicValNat.padicValNat_eq_maxPowDiv]
  native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  change (a 1 + Nat.nth Nat.Prime 1) / 2 ^ padicValNat 2 (a 1 + Nat.nth Nat.Prime 1) = 1
  rw [a_1, Nat.nth_prime_one_eq_three, padicValNat.padicValNat_eq_maxPowDiv]
  native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  change (a 2 + Nat.nth Nat.Prime 2) / 2 ^ padicValNat 2 (a 2 + Nat.nth Nat.Prime 2) = 3
  rw [a_2, Nat.nth_prime_two_eq_five, padicValNat.padicValNat_eq_maxPowDiv]
  native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  change (a 3 + Nat.nth Nat.Prime 3) / 2 ^ padicValNat 2 (a 3 + Nat.nth Nat.Prime 3) = 5
  rw [a_3, Nat.nth_prime_three_eq_seven, padicValNat.padicValNat_eq_maxPowDiv]
  native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  change (a 4 + Nat.nth Nat.Prime 4) / 2 ^ padicValNat 2 (a 4 + Nat.nth Nat.Prime 4) = 1
  rw [a_4, Nat.nth_prime_four_eq_eleven, padicValNat.padicValNat_eq_maxPowDiv]
  native_decide

/--
Is $a(33900)$ the last term equal to $1$?
-/
@[category research open, AMS 11]
theorem conjecture :
  answer(sorry) ↔ ∀ n > 33900, a n ≠ 1 := by
  sorry

end OeisA114216
