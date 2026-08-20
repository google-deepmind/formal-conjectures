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
# Conjectures associated with A109227

Binary strings that have 1's where primes occur, 0's elsewhere and every term ends
with the $n$-th prime index.

Conjecture: $a(2)$ and $a(121)$ are primes. Are there any more?

*References:*
- [A109227](https://oeis.org/A109227)
-/

namespace OeisA109227

open Nat List

/--
The primary defining sequence `a`.
$a(n)$ is the natural number whose decimal digits are given by the binary string of length $p_n$
where the $k$-th digit is $1$ if $k$ is prime and $0$ otherwise, with leading zeros dropped.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let pN : ℕ := Nat.nth Nat.Prime (n - 1)
  let primeBitsFull : List ℕ := (range (pN + 1)).map (fun i =>
    if i.Prime then 1 else 0
  )
  let primeBitsTrimmed := primeBitsFull.dropWhile (· = 0)
  ofDigits 10 primeBitsTrimmed.reverse

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  rw [Nat.nth_prime_zero_eq_two]
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 11 := by
  dsimp [a]
  rw [Nat.nth_prime_one_eq_three]
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1101 := by
  dsimp [a]
  rw [Nat.nth_prime_two_eq_five]
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 110101 := by
  dsimp [a]
  rw [Nat.nth_prime_three_eq_seven]
  decide

/--
Conjecture: $a(2)$ and $a(121)$ are primes. Are there any more?
-/
@[category research open, AMS 11]
theorem conjecture :
    answer(sorry) ↔ ∃ n > 0, n ≠ 2 ∧ n ≠ 121 ∧ (a n).Prime := by
  sorry

end OeisA109227
