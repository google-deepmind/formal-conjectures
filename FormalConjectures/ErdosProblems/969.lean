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
# Erdős Problem 969

*Reference:* [erdosproblems.com/969](https://www.erdosproblems.com/969)

Let `Q(x)` count the squarefree integers in `[1, x]`.  Determine the order of
magnitude of the error term in
`Q(x) = (6 / π^2) x + E(x)`.
-/

noncomputable section

namespace Erdos969

open Classical Asymptotics

/-- A natural number is squarefree if no square of a prime divides it. -/
def SquarefreeNat (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

/-- The squarefree counting function `Q(x)`. -/
def squarefreeCountingFunction (x : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 x).filter SquarefreeNat).card

/-- The error term in `Q(x) = (6 / π^2) x + E(x)`. -/
def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCountingFunction x : ℝ) -
    (6 / Real.pi ^ 2) * (x : ℝ)

/-- A candidate order of magnitude for the squarefree-counting error term. -/
def SquarefreeErrorOrderCandidate (g : ℕ → ℝ) : Prop :=
  squarefreeCountingError =O[Filter.atTop] g ∧
    g =O[Filter.atTop] squarefreeCountingError

/--
Determine the order of magnitude of the squarefree-counting error term.
-/
@[category research open, AMS 11]
theorem erdos_969 :
    {g : ℕ → ℝ | SquarefreeErrorOrderCandidate g} = answer(sorry) := by
  sorry

end Erdos969

end
