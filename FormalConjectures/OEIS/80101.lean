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
# Number of prime powers strictly between $n$-th prime and $(n+1)$-th prime

The sequence $a(n)$ is the number of prime powers $k$ strictly between the $n$-th prime $p_n$
and the $(n+1)$-th prime $p_{n+1}$: $p_n < k < p_{n+1}$.

*References:*
- [A080101](https://oeis.org/A080101)-/

namespace OeisA80101

open Finset

/-- Number of prime powers strictly between the $n$-th prime and the $(n+1)$-th prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let pn := Nat.nth Nat.Prime (n - 1)
    let pn1 := Nat.nth Nat.Prime n
    ((Ioo pn pn1).filter IsPrimePow).card

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  change ((Ioo (Nat.nth Nat.Prime 0) (Nat.nth Nat.Prime 1)).filter IsPrimePow).card = 0
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  change ((Ioo (Nat.nth Nat.Prime 1) (Nat.nth Nat.Prime 2)).filter IsPrimePow).card = 1
  rw [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  change ((Ioo (Nat.nth Nat.Prime 2) (Nat.nth Nat.Prime 3)).filter IsPrimePow).card = 0
  rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  change ((Ioo (Nat.nth Nat.Prime 3) (Nat.nth Nat.Prime 4)).filter IsPrimePow).card = 2
  rw [Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  decide +native

/--
It is conjectured that $a(n) \le 2$ for all $n$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : a n ≤ 2 := by
  sorry

end OeisA80101
