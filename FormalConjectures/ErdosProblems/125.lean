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
# Erdős Problem 125

*Reference:* [erdosproblems.com/125](https://www.erdosproblems.com/125)

There are four possibilities for the density of $A+B$:
1. $A+B$ has zero upper and lower density (and hence also zero density).
2. $A+B$ has zero lower density, but positive upper density (and hence no density).
3. $A+B$ has positive upper and lower density that are equal (and hence positive density).
4. $A+B$ has positive upper and lower density that are unequal (and hence no density).
-/

open Nat Pointwise

namespace Erdos125

set_option quotPrecheck false

/--
Let $A$ be the set of integers which have only the digits $0, 1$ when written base 3,
-/
local notation "A" => { x : ℕ | (digits 3 x).toFinset ⊆ {0, 1} }
/--
and $B$ be the set of integers which have only the digits $0, 1$ when written base 4.
-/
local notation "B" => { x : ℕ | (digits 4 x).toFinset ⊆ {0, 1} }


/-
There are four possibilities for the density of $A+B$:
1. $A+B$ has zero upper and lower density (and hence also zero density).
2. $A+B$ has zero lower density, but positive upper density (and hence no density).
3. $A+B$ has positive upper and lower density that are equal (and hence positive density).
4. $A+B$ has positive upper and lower density that are unequal (and hence no density).
-/

/--
Case 3:
Does $A + B$ have positive upper and lower density that are equal?
This is the literal interpretation of "positive density" which was falsified.
-/

@[category research solved, AMS 11,
formal_proof using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/300bf771bdbef43d7b9aa2521e633a50fd54dd28/FormalConjectures/ErdosProblems/125.lean"]
theorem erdos_125 :
    answer(False) ↔ (A + B).HasPosDensity := by
  sorry

/--
Literature question:
Does $A + B$ have positive lower density?

This has been falsified.
-/
@[category research solved, AMS 11,
formal_proof using formal_conjectures at "https://github.com/mo271/formal-conjectures/blob/c27415379b5dbe34105d1fdd707994540c4c6fc7/FormalConjectures/ErdosProblems/125.lean#L468"]
theorem erdos_125.variants.positive_lower_density :
    answer(False) ↔ 0 < (A + B).lowerDensity := by
  sorry


/--
Literature question:
Does $A + B$ have positive upper density?
-/
@[category research open, AMS 11]
theorem erdos_125.variants.positive_upper_density :
    answer(sorry) ↔ 0 < (A + B).upperDensity := by
  sorry

/--
Case 1:
Does $A + B$ have zero upper and lower density?
-/
@[category research open, AMS 11]
theorem erdos_125.variants.zero_density :
    answer(sorry) ↔ (A + B).upperDensity = 0 ∧ (A + B).lowerDensity = 0 := by
  sorry

/--
Case 2:
Does $A + B$ have zero lower density, but positive upper density?
-/
@[category research open, AMS 11]
theorem erdos_125.variants.zero_lower_positive_upper_density :
    answer(sorry) ↔ (A + B).lowerDensity = 0 ∧ 0 < (A + B).upperDensity := by
  sorry

/--
Case 4:
Does $A + B$ have positive upper and lower density that are unequal?
-/
@[category research open, AMS 11]
theorem erdos_125.variants.positive_unequal_density :
    answer(sorry) ↔ 0 < (A + B).lowerDensity ∧ (A + B).lowerDensity < (A + B).upperDensity := by
  sorry

end Erdos125
