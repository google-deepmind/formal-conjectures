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
# Sum of binomial coefficients modulo powers of 2

The sequence is defined by
$$a(n) = \sum_{k=1}^n \left(\binom{n}{k} \bmod 2^k\right)$$

*References:*
- [A386660](https://oeis.org/A386660)
-/
open Nat Finset

namespace OeisA386660

/--
The sequence $a(n) = \sum_{k=1}^n \left(\binom{n}{k} \bmod 2^k\right)$.
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 n, (n.choose k) % (2 ^ k)

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 11 := by rfl
/--
The limit of $a(n)^{1/n}$ exists.
The numerical evidence suggests a limit of approximately $1.7086...$
-/
@[category research open, AMS 11]
theorem limit_exists :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  sorry

end OeisA386660
