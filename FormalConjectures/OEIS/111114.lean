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
# A111114

Integer part of $\mathrm{prime}(n)/\pi(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, and $\pi(n)$ is the prime-counting function.

*References:*
- [A111114](https://oeis.org/A111114)
-/

namespace OeisA111114

open Nat

/--
`a n` is the integer part of $\mathrm{prime}(n)/\pi(n)$.
Here $\mathrm{prime}(n)$ is the $n$-th prime number, and $\pi(n)$ is the prime-counting function.
The sequence is defined for $n \ge 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Nat.nth Nat.Prime (n - 1)) / (Nat.primeCounting n)

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  have : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by
  have : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  have : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  unfold a
  rw [this]
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by
  have : Nat.nth Nat.Prime 4 = 11 := Nat.nth_prime_four_eq_eleven
  unfold a
  rw [this]
  decide

/--
Conjecture: As n -> infinity, there are infinitely many n's such that a(n) is greater than a(n+1).
-/
@[category research open, AMS 11]
theorem conjecture : ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 2 ∧ a n > a (n + 1) := by
  sorry

end OeisA111114
