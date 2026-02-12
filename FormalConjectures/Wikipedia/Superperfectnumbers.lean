/-
Copyright 2025 The Formal Conjectures Authors.

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
# (m,k)-perfect numbers

An integer `n : ℤ` is `(m,k)-perfect` if `σᵐ(n) = kn` where `σᵐ` is the mᵗʰ iterate of the
sum of divisors function.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Superperfect_number#Generalizations)
 - [Wikipedia](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics#General)
-/

namespace Superperfect

/--
The sum of divisors function σ(n) = `∑ d ∈ divisors n, d`
-/
def σ (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/--
An integer `n : ℕ` is `(m,k)-perfect` if `σᵐ(n) = kn` where `σᵐ` is the mᵗʰ iterate of `σ`.
-/
def Perfect (n m k : ℕ) : Prop := Nat.iterate σ m n = k * n

/-- An integer `n : ℤ` can be written as a sum of three cubes (of integers) if and only if
`n` is not `4` or `5` mod `9`. -/
@[category research open, AMS 11]
theorem twoFivePerfect : ¬∃ (n : ℕ), Perfect n 2 5 := by
  sorry

end Superperfect
