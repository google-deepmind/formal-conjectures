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

local notation "e" => exp 1

-- See also corresponding transcendence conjectures
-- in `FormalConjectures.Wikipedia.SchanuelsConjecture`

namespace Irrational

/-- Are $e$ and $\pi$ algebraically independent? -/
@[category research open, AMS 33]
theorem algebraicIndependent_e_pi :
    AlgebraicIndependent ℚ ![e, π] ↔ answer(sorry) := by
  sorry

/--
Is $e + \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_plus_pi :
    Irrational (e + π) ↔ answer(sorry) := by
  sorry

/--
Is $e \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_times_pi :
    Irrational (e * π) ↔ answer(sorry) := by
  sorry

/--
Is $e ^ e$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_to_e :
    Irrational (e ^ e) ↔ answer(sorry) := by
  sorry

/--
Is $\pi ^ e$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_pi_to_e :
    Irrational (π ^ e) ↔ answer(sorry) := by
  sorry

/--
Is $\pi ^ \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_pi_to_pi :
    Irrational (π ^ π) ↔ answer(sorry) := by
  sorry

/--
Is $\ln(\pi)$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_ln_pi :
    Irrational (log π) ↔ answer(sorry) := by
  sorry

/--
Is the Euler-Mascheroni constant $\gamma$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_eulerMascheroniConstant :
    Irrational eulerMascheroniConstant ↔ answer(sorry) := by
  sorry

/--
Is the Catalan constant $$G = \sum_{n=0}^∞ (-1)^n / (2n + 1)^2 \approx 0.91596$$ irrational?
-/
@[category research open, AMS 11 33]
theorem irrational_catalanConstant :
    Irrational catalanConstant ↔ answer(sorry) := by
  sorry

end Irrational
