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

/-
# Existence of Odd Weird Numbers

*References:*
- [Wikipedia] (https://en.wikipedia.org/wiki/Weird_number)
- [A006037] (https://oeis.org/A006037)
-/

namespace OddWeirdNumber

/-
Given n ∈ ℕ, n is abundant if the sum of the proper divisors of n
is greater than n.
-/
def is_abundant (n : ℕ) : Prop :=
  n.properDivisors.sum id > n

/-
Given n ∈ ℕ, n is pseudoperfect if there exists a subset S of
proper divisors of n such that S sums to n.
-/
def pseudoperfect (n : ℕ) : Prop :=
  ∃ S ⊆ n.properDivisors, S.sum id = n

/-
A weird number is a natural number that is abundant
but not pseudoperfect.
-/
def is_weird (n : ℕ) : Prop :=
  is_abundant n ∧ ¬pseudoperfect n

/-
The Existence of Odd Weird Number Conjecture asks if there exists
an odd number that is weird.
-/
@[category research open, AMS 11]
theorem existence_odd_weird :
    ∃ n : ℕ, is_weird n ∧ Odd n := by
  sorry

end OddWeirdNumber
