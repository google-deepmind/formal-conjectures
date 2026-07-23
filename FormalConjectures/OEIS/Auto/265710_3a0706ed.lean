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

open Nat Finset

/--
A265710: $a(n) = \mathrm{denominator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

/--
A265710 a(n) = 2 for n = 14, 244, 494, 45994. Are there any others? - Robert Israel, Apr 02 2017
-/
theorem oeis_A265710_conjecture :
  ∀ n : ℕ, n > 1 → (a n = 2 ↔ n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) := by
  sorry
