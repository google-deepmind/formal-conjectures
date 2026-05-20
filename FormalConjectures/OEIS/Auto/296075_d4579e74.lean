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

open Nat

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  sorry
