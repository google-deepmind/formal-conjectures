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
module

public import FormalConjecturesUtil

/-!
# Open questions on irrationality of numbers

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Irrational_number#Open_questions)
- [OAI26a] OpenAI, *Catalan's constant is irrational*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf
-/

@[expose] public section

open Real

local notation "e" => exp 1

-- See also corresponding transcendence conjectures
-- in `FormalConjectures.Wikipedia.SchanuelsConjecture`

namespace Irrational

/-- Are $e$ and $\pi$ algebraically independent? -/
@[category research open, AMS 33]
theorem algebraicIndependent_e_pi :
    answer(sorry) ↔ AlgebraicIndependent ℚ ![e, π] := by
  sorry

/--
Is $e + \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_plus_pi :
    answer(sorry) ↔ Irrational (e + π) := by
  sorry

/--
Is $e \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_times_pi :
    answer(sorry) ↔ Irrational (e * π) := by
  sorry

/--
Is $e ^ e$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_e_to_e :
    answer(sorry) ↔ Irrational (e ^ e) := by
  sorry

/--
Is $\pi ^ e$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_pi_to_e :
    answer(sorry) ↔ Irrational (π ^ e) := by
  sorry

/--
Is $\pi ^ \pi$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_pi_to_pi :
    answer(sorry) ↔ Irrational (π ^ π) := by
  sorry

/--
Is $\ln(\pi)$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_ln_pi :
    answer(sorry) ↔ Irrational (log π) := by
  sorry

/--
Is the Euler-Mascheroni constant $\gamma$ irrational?
-/
@[category research open, AMS 33]
theorem irrational_eulerMascheroniConstant :
    answer(sorry) ↔ Irrational eulerMascheroniConstant := by
  sorry

/--
Is the Catalan constant $$G = \sum_{n=0}^∞ (-1)^n / (2n + 1)^2 \approx 0.91596$$ irrational?

This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean proof.
-/
@[category research solved, AMS 11 33, formal_proof using lean4 at
  "https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/Catalan/Results/Conclusions.lean#L11"]
theorem irrational_catalanConstant :
    answer(True) ↔ Irrational catalanConstant := by
  sorry

end Irrational
