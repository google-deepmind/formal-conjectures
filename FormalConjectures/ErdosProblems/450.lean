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
# Erdős Problem 450

*Reference:* [erdosproblems.com/450](https://www.erdosproblems.com/450)

How large must `y = y(ε,n)` be such that the number of integers in `(x, x+y)`
with a divisor in `(n, 2n)` is at most `ε y`?

The page notes that the intended quantifier on `x` is unclear.  We formalize
the uniform-in-`x` interpretation.
-/

noncomputable section

namespace Erdos450

open Classical

/-- `m` has a divisor strictly between `n` and `2n`. -/
def HasDivisorInMiddleInterval (n m : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

/-- The number of integers in the open interval `(x, x+y)` with such a divisor. -/
def middleDivisorCount (n x y : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc (x + 1) (x + y - 1)).filter fun m =>
    HasDivisorInMiddleInterval n m).card

/-- `y` works uniformly in `x` for the parameters `ε` and `n`. -/
def UniformMiddleDivisorBound (ε : ℝ) (n y : ℕ) : Prop :=
  ∀ x : ℕ, (middleDivisorCount n x y : ℝ) ≤ ε * (y : ℝ)

/-- `Y ε n` is the least interval length satisfying the uniform interpretation. -/
def IsUniformYFunction (Y : ℝ → ℕ → ℕ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∀ n : ℕ,
        IsLeast {y : ℕ | 0 < y ∧ UniformMiddleDivisorBound ε n y} (Y ε n)

/-- Determine the required length `y(ε,n)` under the uniform interpretation. -/
@[category research open, AMS 11]
theorem erdos_450 : {Y : ℝ → ℕ → ℕ | IsUniformYFunction Y} = answer(sorry) := by
  sorry

end Erdos450

end
