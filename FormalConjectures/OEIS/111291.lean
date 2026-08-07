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
# Number of refactorable numbers (A033950) $\le 10^n$

A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.

*References:*
- [A111291](https://oeis.org/A111291)
-/

namespace OeisA111291

open Nat Finset Real

/-- Helper function: number of refactorable numbers $\le m$. -/
def countRefactorableNat (m : ℕ) : ℕ :=
  (Icc 1 m).filter (fun k => k.divisors.card ∣ k) |>.card

/--
`a n` is the number of refactorable numbers $\le 10^n$.
A number $k$ is refactorable if its number of divisors, $\tau(k)$, divides $k$.
-/
def a (n : ℕ) : ℕ :=
  countRefactorableNat (10 ^ n)

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 16 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 92 := by native_decide

/--
`countRefactorable x` is the number of refactorable numbers $\le x$.
-/
noncomputable def countRefactorable (x : ℝ) : ℕ :=
  if _hx : x ≥ 1 then
    countRefactorableNat (Int.toNat (floor x))
  else
    0

/--
Simon Colton conjectures that the number of refactorables less than x is at least x/(2 log(x)).
-/
@[category research open, AMS 11]
theorem conjecture : ∀ (x : ℝ), x > 1 →
    (countRefactorable x : ℝ) ≥ x / (2 * Real.log x) := by
  sorry

end OeisA111291
