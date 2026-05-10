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
# Quasiperfect Numbers

*Reference:* 
- [Wikipedia](https://en.wikipedia.org/wiki/Quasiperfect_number)
-/

namespace QuasiperfectNumbers

open Nat

open scoped ArithmeticFunction.sigma

/-- 
A number is quasiperfect if the sum of its divisors is equal to $2n + 1$. 
-/
def Quasiperfect (n : ℕ) : Prop :=
  σ 1 n = 2 * n + 1

/--
**Quasiperfect Numbers Conjecture.**
Do quasiperfect numbers exist?
-/
@[category research open, AMS 11]
theorem exists_quasiperfect :
    answer(sorry) ↔ ∃ n, Quasiperfect n := by
  sorry

end QuasiperfectNumbers
