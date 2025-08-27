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
# Erdős Problem 303

*Reference:* [erdosproblems.com/303](https://www.erdosproblems.com/303)
-/

namespace Erdos303

/-- Is it true that in any finite colouring of the integers there exists a monochromatic solution
to $\frac 1 a = \frac 1 b + \frac 1 c$ with distinct $a, b, c$?

This is true, as proved by Brown and Rödl [BrRo91].

[BrRo91] Brown, Tom C. and Rödl, Voijtech,
_Monochromatic solutions to equations with unit fractions_.
Bull. Austral. Math. Soc. (1991), 387-392.
-/
@[category research solved, AMS 5 11]
theorem erdos_303 :
    --For any finite colouring of the integers
    (∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
      --There exists integers `a, b, c`
      ∃ (a b c : ℤ),
      --that are non-zero and distinct.
      [a, b, c, 0].Nodup ∧
      --`a, b, c` satisfy the equation
      (1/a : ℝ) = 1/b + 1/c ∧
      --`a, b, c` have the same color
      (𝓒 '' {a, b, c}).Subsingleton) ↔ answer(True) := by
  sorry

end Erdos303
