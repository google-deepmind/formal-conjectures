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

import FormalConjectures.Util.ProblemImports

/-!
# Non-Power-of-2 Almost Perfect Numbers Conjecture

*Reference:* https://mathworld.wolfram.com/AlmostPerfectNumber.html
*Reference:* https://en.wikipedia.org/wiki/Almost_perfect_number
-/

namespace AlmostPerfectNumbers

open Nat

open scoped ArithmeticFunction

/-- 
A number is almost perfect if the sum of its divisors is equal to $2n - 1$. 
-/
def AlmostPerfect (n : ℕ) : Prop :=
  1 + σ 1 n = 2 * n

/--
**Non-Power-of-2 Almost Perfect Numbers Conjecture.**
Does there exist an almost perfect number that is not a power of 2?
-/
@[category research open, AMS 11]
theorem exists_almost_perfect_not_power_of_two :
    answer(sorry) ↔ ∃ n : ℕ, AlmostPerfect n ∧ ¬ ∃ k : ℕ, n = 2^k := by
  sorry

end AlmostPerfectNumbers
