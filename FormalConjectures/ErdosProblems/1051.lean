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
# Erdős Problem 1051

*Reference:* [erdosproblems.com/1051](https://www.erdosproblems.com/1051)

Is it true that if a₁ < a₂ < ⋯ is a sequence of integers with liminf aₙ^(1/2ⁿ) > 1,
then the sum ∑_{n=1}^∞ 1/(aₙ × aₙ₊₁) is irrational?

Note: Erdős mentions this is true if aₙ → ∞ "rapidly".

## References
- [Er88c] Erdős, P., On the irrationality of certain series: problems and results.
  New advances in transcendence theory (Durham, 1986) (1988), 102-109.
-/

namespace Erdos1051

/-- A sequence of integers `a` satisfies the growth condition if
    liminf aₙ^(1/2ⁿ) > 1 -/
def GrowthCondition (a : ℕ → ℤ) : Prop :=
  ∃ c > 1, ∃ N, ∀ n ≥ N, (a n : ℝ) ^ (1 / 2 ^ n : ℝ) ≥ c

/-- The series ∑_{n=1}^∞ 1/(aₙ × aₙ₊₁) -/
noncomputable def ErdosSeries (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, 1 / ((a n : ℝ) * (a (n + 1) : ℝ))

/-- Is it true that if a₁ < a₂ < ⋯ is a strictly increasing sequence of integers
    with liminf aₙ^(1/2ⁿ) > 1, then ∑_{n=1}^∞ 1/(aₙ × aₙ₊₁) is irrational? -/
@[category research open, AMS 11]
theorem erdos_1051 :
    (∀ (a : ℕ → ℤ), StrictMono a → GrowthCondition a →
      Irrational (ErdosSeries a)) ↔ answer(sorry) := by
  sorry

/-- If the sequence grows rapidly to infinity, then the series is irrational.
    This is a solved variant mentioned by Erdős. -/
@[category research solved, AMS 11]
theorem irrational_of_rapid_growth (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_rapid : ∃ C > 0, ∀ n, (a (n + 1) : ℝ) ≥ C * (a n : ℝ) ^ 2) :
    Irrational (ErdosSeries a) := by
  sorry

end Erdos1051
