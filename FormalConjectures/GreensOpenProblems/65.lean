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
# Ben Green's Open Problem 65

*Reference:* [Ben Green's Open Problem 65](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.65)
-/

open Filter

namespace Green65

/-- An integer is a nonzero square if it is the square of a nonzero natural number. -/
def IsNonzeroSquare (d : ℤ) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ d = (n : ℤ) ^ 2

/-- An integer is one less than a prime. -/
def IsPrimeMinusOne (d : ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ d = (p : ℤ) - 1

/-- The interval `[N] = {1, ..., N}`, viewed as a finite set of integers. -/
def interval (N : ℕ) : Finset ℤ :=
  Finset.Icc (1 : ℤ) (N : ℤ)

/-- The signed difference set `A - A`. -/
def differenceSet (A : Finset ℤ) : Set ℤ :=
  {d | ∃ a ∈ A, ∃ b ∈ A, d = a - b}

/--
There is a fixed density exponent `c > 0` such that every sufficiently large subset
`A ⊆ [N]` with `|A| ≥ N^(1-c)` has a difference satisfying `P`.

We model `[N]` as the integer interval `{1, ..., N}` and use sufficiently large `N`, since the
literal small-`N` version is false for the nonzero-square question.
-/
def LargeDifferencePattern (P : ℤ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℤ,
    A ⊆ interval N →
      (N : ℝ) ^ (1 - c) ≤ (A.card : ℝ) →
        ∃ d ∈ differenceSet A, P d

/--
Is there `c > 0` such that every sufficiently large subset `A ⊆ [N]` of size at least
`N^(1-c)` has a difference that is a nonzero square?
-/
@[category research open, AMS 5 11]
theorem green_65 :
    answer(sorry) ↔ LargeDifferencePattern IsNonzeroSquare := by
  sorry

/--
Green asks the analogous question with "nonzero square" replaced by "prime minus one".
-/
@[category research open, AMS 5 11]
theorem green_65.variants.prime_minus_one :
    answer(sorry) ↔ LargeDifferencePattern IsPrimeMinusOne := by
  sorry

end Green65
