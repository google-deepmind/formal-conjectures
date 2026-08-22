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
# Erdős Problem 2

*Reference:* [erdosproblems.com/2](https://www.erdosproblems.com/2)

Erdős asked whether the smallest modulus in a distinct covering system can be arbitrarily large.
Hough proved that the answer is no, and Balister, Bollobás, Morris, Sahasrabudhe, and Tiba later
gave a simpler proof with an improved explicit upper bound.
-/

namespace Erdos2

/--
Can the smallest modulus of a covering system be arbitrarily large?

This problem has a negative answer: there is a universal bound on the least modulus of any
distinct covering system.
-/
@[category research solved, AMS 11]
theorem erdos_2 :
    answer(False) ↔
      ∀ B : ℕ, ∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ m : ℕ,
        c.moduli i = Ideal.span {(m : ℤ)} ∧ B < m := by
  sorry

end Erdos2
