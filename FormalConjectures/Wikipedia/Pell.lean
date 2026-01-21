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
# Infinitude of Pell number primes

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Pell_number#Primes_and_squares)
 - [OEIS A086383](https://oeis.org/A086383)

The Pell numbers $P_n$ are defined by $P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$. [OEIS A000129](https://oeis.org/A000129)

The conjecture says that there are infinitely many prime Pell numbers.
-/

namespace PellNumbers

/-- The *Pell numbers* $P_n$ are defined by $P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2*P_{n+1} + P_n$ -/
def pellNumber : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 + 1 => 2 * pellNumber  (n + 1) + pellNumber n

@[category test, AMS 11]
theorem pellNumber_zero : pellNumber 0 = 0 := rfl

@[category test, AMS 11]
theorem pellNumber_one : pellNumber 1 = 1 := rfl

@[category test, AMS 11]
theorem pellNumber_two : pellNumber 2 = 2 := rfl

@[category test, AMS 11]
theorem pellNumber_five : pellNumber 5 = 29 := rfl

/-- Similar to Fibonacci numbers, there exist numerous identites around Pell numbers, i.e.
P_{2n+1} = P_n ^ 2 + P_{n+1} ^ 2 -/
@[category high_school, AMS 11]
theorem pellNumber_sq_add_pellNumber_succ_sq (n : ℕ) :
    pellNumber (2 * n + 1) = pellNumber n ^ 2 + pellNumber (n + 1) ^ 2 := by
  sorry

/-- An explicit formula for Pell numbers, similar to Binet's formula -/
@[category high_school, AMS 11]
theorem coe_pellNumber_eq : ∀ n, (pellNumber n : ℝ) = ((1 + √2) ^ n - (1 - √2) ^ n) / (2 * √2) := by
  sorry

/-- There are infinitely many prime Pell numbers -/
@[category research open, AMS 11]
theorem infinite_pellNumber_primes : Infinite {n : ℕ | Prime (pellNumber n)} := by
  sorry

-- TODO : Formalise connection between Pell numbers and Pell equation x^2 - 2*y^2 = -1

end PellNumbers
