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
open Set

/--
A383466: $a(0) = 1$; thereafter $a(n) = 10n^2 - 5n + 2$, which is
$a(n) = 5n(2n-1) + 2$ for $n \ge 1$.
-/
def a : ℕ → ℕ
  | 0 => 1
  | k + 1 => 5 * (k + 1) * (2 * (k + 1) - 1) + 2

theorem a_zero : a 0 = 1 := by rfl
theorem a_one : a 1 = 7 := by rfl
theorem a_two : a 2 = 32 := by rfl
theorem a_three : a 3 = 77 := by rfl

-- We define abstract geometric concepts using axioms.
-- This is the preferred way to introduce non-fully formalized concepts for conjecture statements.
noncomputable section

/--
An abstract type representing the collection of $n$ regular pentagrams in the plane
with any radii and any centers.
-/
axiom pentagram_configuration (n : ℕ) : Type

/--
The number of connected open regions formed in the plane by the segments of a given configuration
of $n$ regular pentagrams.
-/
axiom number_of_regions {n : ℕ} (C : pentagram_configuration n) : ℕ

/--
Conjecture 2: a(n) is the maximum number of regions that can be formed in the plane by drawing n regular pentagrams with any radii and any centers.
The "maximum" is formalized as the supremum of the set of all possible region counts.
-/
theorem oeis_a383466_conjecture_2 (n : ℕ) :
  a n = sSup (Set.range (@number_of_regions n)) := by
  sorry

end
