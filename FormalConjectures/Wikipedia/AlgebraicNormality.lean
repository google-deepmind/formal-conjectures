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
# Normality of Irrational Algebraic Numbers

It is unknown whether every irrational algebraic real number is normal in any integer base.
The stronger conjecture that every irrational algebraic real number is absolutely normal is stated
separately: normality in one base and normality in every base are not equivalent definitions.

*References:*
- [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [BC01] Bailey, David H., and Richard E. Crandall. "On the random character of fundamental constant
  expansions." Experimental Mathematics 10.2 (2001): 175-190.
  https://projecteuclid.org/journals/experimental-mathematics/volume-10/issue-2/On-the-random-character-of-fundamental-constant-expansions/em/999188630.full
-/

open NormalNumber

namespace AlgebraicNormality

/-- A real number is irrational algebraic if it is algebraic over `ℚ` but not rational. -/
def IsIrrationalAlgebraic (x : ℝ) : Prop :=
  IsAlgebraic ℚ x ∧ Irrational x

/-- The strong normality conjecture: every irrational algebraic real is absolutely normal. -/
@[category research open, AMS 11 12 41]
theorem irrational_algebraic_absolutely_normal :
    answer(sorry) ↔ ∀ x : ℝ, IsIrrationalAlgebraic x → IsAbsolutelyNormal x := by
  sorry

/-- The weaker normality conjecture: every irrational algebraic real is normal in at least one
integer base `b ≥ 2`. -/
@[category research open, AMS 11 12 41]
theorem irrational_algebraic_normal_in_some_base :
    answer(sorry) ↔
      ∀ x : ℝ, IsIrrationalAlgebraic x → ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b x := by
  sorry

/-- Absolute normality implies normality in at least one base. -/
@[category API, AMS 11]
theorem normal_in_some_base_of_absolutely_normal {x : ℝ} (hx : IsAbsolutelyNormal x) :
    ∃ b : ℕ, 2 ≤ b ∧ IsNormalInBase b x :=
  ⟨2, le_rfl, hx 2 le_rfl⟩

end AlgebraicNormality
