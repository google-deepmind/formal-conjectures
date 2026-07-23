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
# Erdős Problem 676

*Reference:* [erdosproblems.com/676](https://www.erdosproblems.com/676)

Is every sufficiently large integer of the form `a p^2 + b` for some prime
`p`, integer `a ≥ 1`, and `0 ≤ b < p`?
-/

noncomputable section

namespace Erdos676

open Classical Filter

/-- A representation `n = a p^2 + b` with `p` prime, `a ≥ 1`, and `0 ≤ b < p`. -/
def PrimeSquareRemainderRepresentation (n : ℕ) : Prop :=
  ∃ a p b : ℕ,
    Nat.Prime p ∧
      1 ≤ a ∧
        b < p ∧
          n = a * p ^ 2 + b

/-- The main conjecture from Erdős problem 676. -/
def Erdos676Conjecture : Prop :=
  ∀ᶠ n in atTop, PrimeSquareRemainderRepresentation n

/-- Is every sufficiently large integer of the form `a p^2 + b`, `0 ≤ b < p`? -/
@[category research open, AMS 11]
theorem erdos_676 : answer(sorry) ↔ Erdos676Conjecture := by
  sorry

end Erdos676

end
