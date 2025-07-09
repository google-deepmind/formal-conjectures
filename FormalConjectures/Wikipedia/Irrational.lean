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
# Open questions on irrationality of numbers

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Irrational_number#Open_questions)
-/

open Real
open Finset

local notation "e" => exp 1

-- See also corresponding transcendence conjectures
-- in `FormalConjectures.Wikipedia.SchanuelsConjecture`

/-- $e + \pi$ is irrational -/
@[category research open, AMS 33]
theorem irrational_e_plus_pi : Irrational (e + π) := by
  sorry

/-- $e \pi$ is irrational -/
@[category research open, AMS 33]
theorem irrational_e_times_pi : Irrational (e * π) := by
  sorry

/-- $e ^ e$ is irrational -/
@[category research open, AMS 33]
theorem irrational_e_to_e : Irrational (e ^ e) := by
  sorry

/-- $\pi ^ e$ is irrational -/
@[category research open, AMS 33]
theorem irrational_pi_to_e : Irrational (π ^ e) := by
  sorry

/-- $\pi ^ \pi$ is irrational -/
@[category research open, AMS 33]
theorem irrational_pi_to_pi : Irrational (π ^ π) := by
  sorry

/-- $\ln(\pi)$ is irrational -/
@[category research open, AMS 33]
theorem irrational_ln_pi : Irrational (log π) := by
  sorry

/-- The the difference between harmonic series and natural logarithm, also known
as Euler-Mascheroni constant $\gamma$ is irrational -/
@[category research open, AMS 33]
theorem irrational_euler_mascheroni :
    Irrational eulerMascheroniConstant := by
  sorry

/-- The Catalan constant is irrational -/
@[category research open, AMS 11 33]
theorem irrational_catalan_constant :
    Irrational (∑' n : ℕ, (-1)^n / (2*n + 1)^2) := by
  sorry
