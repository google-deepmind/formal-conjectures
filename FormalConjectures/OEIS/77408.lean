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
# Trajectory of 103 under the Reverse and Add! operation in base 3

The sequence $a(n)$ is the trajectory of $103$ under the Reverse and Add! operation carried out
in base $3$, written in base $10$.
$a(0) = 103$, and $a(n+1) = a(n) + \text{rev}_3(a(n))$.

*References:*
- [A077408](https://oeis.org/A077408)-/

namespace OeisA77408

/-- The number whose base-$b$ digits are the reversal of $n$'s base-$b$ digits. -/
def revBase (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

/-- A natural number $n$ is a base-$b$ palindrome if its base-$b$ digits read the same forwards
and backwards. -/
def IsBasePalindrome (b n : ℕ) : Prop :=
  n = revBase b n

/-- Trajectory of 103 under the Reverse and Add! operation in base 3. -/
def a : ℕ → ℕ
  | 0 => 103
  | n + 1 => a n + revBase 3 (a n)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 103 := by
  rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 230 := by
  decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 436 := by
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 776 := by
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 2424 := by
  decide +native

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 3856 := by
  decide +native

/--
$103$ is conjectured to be the smallest number such that the Reverse and Add! algorithm in base $3$
does not lead to a palindrome. Its trajectory is conjectured to never reach a palindrome.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : ¬ IsBasePalindrome 3 (a n) := by
  sorry

end OeisA77408
