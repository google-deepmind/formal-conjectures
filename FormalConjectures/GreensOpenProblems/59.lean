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
# Ben Green's Open Problem 59

Is every natural number `n ≤ N` expressible as the sum of two integers whose prime factors are all at
most `N^ε` (for some absolute exponent `ε > 0`)?

*Reference:* [Ben Green's Open Problem 59](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 59)
-/

namespace Green59

/-- For fixed `ε` and parameter `N`, this is the smoothness bound `⌈N^ε⌉` used in the conjecture. -/
noncomputable def smoothBound (ε : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ ε)

/-- The conjecture asserts that, for some absolute `ε > 0`, every `n ≤ N` splits as a sum of two
`N^ε`-smooth integers. -/
@[category research open, AMS 11]
theorem green_59 :
    answer(sorry) ↔ ∃ ε > (0 : ℝ),
      ∀ (N : ℕ), 1 ≤ N →
        ∀ (n : ℕ), 1 ≤ n → n ≤ N →
          ∃ a b : ℕ,
            a ∈ Nat.smoothNumbers (smoothBound ε N) ∧
            b ∈ Nat.smoothNumbers (smoothBound ε N) ∧
            a + b = n := by
  sorry

end Green59
