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
# Zaremba's conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Zaremba%27s_conjecture)
-/

namespace ZarembaConjecture

/-- The finite list of partial quotients in the simple continued fraction expansion of a
positive rational `a / d`. -/
def partialQuotients : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, d + 1 => a / (d + 1) :: partialQuotients (d + 1) (a % (d + 1))
termination_by _ d => d
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- For `333/106 = [3; 7, 15]`. -/
@[category test, AMS 11]
example : partialQuotients 333 106 = [3, 7, 15] := by native_decide

/-- The maximum partial quotient of `a / d`, taking the value `0` when `d = 0`. -/
def maxPartialQuotient (a d : ℕ) : ℕ := (partialQuotients a d).foldl max 0

/-- The maximum partial quotient of `4217/10037` is `2`. -/
@[category test, AMS 11]
example : maxPartialQuotient 4217 10037 = 2 := by native_decide

/-- The residues `a < d` that are coprime to `d`. -/
def coprimeResidues (d : ℕ) : Finset ℕ := {a ∈ Finset.range d | d.Coprime a}

/-- The positive numerators less than `12` and coprime to `12` are `1`, `5`, `7`, and `11`. -/
@[category test, AMS 11]
example : coprimeResidues 12 = {1, 5, 7, 11} := by native_decide

/--
The least possible value, over positive coprime numerators `a < d`, of the maximum partial
quotient in the continued fraction of `a / d`. -/
def minmaxPartialQuotient (d : ℕ) :=
  ((coprimeResidues d).image fun a => maxPartialQuotient a d).min

/-- The best possible maximum partial quotient among coprime numerators for
denominator `121` is `2`. -/
@[category test, AMS 11]
example : minmaxPartialQuotient 121 = 2 := by native_decide

/--
Zaremba's conjecture: there is an absolute constant `A` such that for every
denominator `d`, there is a numerator `a` coprime to `d`, for which every partial
quotient in the continued fraction of `a / d` is at most `A`.
-/
@[category research open, AMS 11]
theorem zaremba_conjecture : ∃ A, ∀ d, minmaxPartialQuotient d ≤ (A : WithTop ℕ) := by
  sorry

end ZarembaConjecture
